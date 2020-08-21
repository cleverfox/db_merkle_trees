%% Licensed under the Apache License, Version 2.0 (the “License”);
%% you may not use this file except in compliance with the License.
%% You may obtain a copy of the License at
%%
%%     http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing, software
%% distributed under the License is distributed on an “AS IS” BASIS,
%% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%% See the License for the specific language governing permissions and
%% limitations under the License.
%%
%% @doc General balanced binary Merkle trees. Similar to {@link //stdlib/gb_trees}, but with Merkle proofs.
%%
%% Keys and values need to be binaries. Values are stored only in leaf nodes to shorten Merkle proofs.
%%
%% Hashes of leaf nodes are based on concatenation of hashes of key and value. Hashes of inner nodes are based on concatenation of hashes of left and right node.
%%
%% Similarly as in {@link //stdlib/gb_trees}, deletions do not cause trees to rebalance.
%%
%% SHA-256 is used as the default hashing algorithm. You can define the `GB_MERKLE_TREES_HASH_ALGORITHM' macro to use another algorithm. See documentation of {@link //crypto/crypto:hash/2} for available choices.
%%
%% @author Krzysztof Jurewicz <krzysztof.jurewicz@gmail.com> [http://jurewicz.org.pl]
%%
%% @reference See <a href="http://cglab.ca/~morin/teaching/5408/refs/a99.pdf">Arne Andersson’s “General Balanced Trees” article</a> for insights about the balancing algorithm. The original balance condition has been changed to 2^h(T) ≤ |T|^2.
%% @reference See <a href="https://github.com/tendermint/go-merkle">go-merkle</a> for a similar in purpose library written in Go which uses AVL trees instead of general balanced trees.
%% @see //stdlib/gb_trees
%% @see //crypto/crypto:hash/2

-module(db_merkle_trees).
-export([
         balance/1,
         delete/2,
         empty/0,
         enter/3,
         foldr/3,
         from_list/2,
         keys/1,
         lookup/2,
         merkle_proof/2,
         root_hash/1,
         size/1,
         to_orddict/1,
         verify_merkle_proof/4
         ]).

-ifdef(TEST).
-include_lib("triq/include/triq.hrl").
-include_lib("eunit/include/eunit.hrl").
-endif.

-ifndef(GB_MERKLE_TREES_HASH_ALGORITHM).
-define(GB_MERKLE_TREES_HASH_ALGORITHM, sha256).
-endif.
-define(HASH(X), crypto:hash(?GB_MERKLE_TREES_HASH_ALGORITHM, X)).

%% Trees are balanced using the condition 2^h(T) ≤ |T|^C
-define(C, 2).

-type key() :: binary().
-type value() :: binary().
-type hash() :: binary().

%% We distinguish inner nodes and tree nodes by tuple length instead of using records to save some space.
-type leaf_node() :: {key(), value(), hash()}.
-type inner_node() :: {key(), hash() | to_be_computed,
                       Left :: inner_node() | leaf_node(),
                       Right :: inner_node() | leaf_node()}.
-type tree_node() :: leaf_node() | inner_node() | empty.
-type merkle_proof() :: {hash() | merkle_proof(), hash() | merkle_proof()}.
-type dbh() :: fun((atom(),any(),any()) -> any()).
-type db() :: {dbh(), any()}.

-export_type([key/0,
              value/0,
              hash/0,
              merkle_proof/0]).

-spec delete(key(), db()) -> any().
delete(Key, {DBH, Acc}) ->
  {{Size,RootID}, Acc1}=DBH(get,<<"R">>,Acc),
  {{S1,NewRootID},Acc2}=delete(Key, {Size, RootID}, {DBH, Acc1}),
  DBH(put,{<<"R">>,{S1,NewRootID}},Acc2).

-spec delete(key(), {integer(), binary()}, db()) -> any().
delete(Key, {Size, RootID}, {DBH, Acc}) ->
  {Node,_}=DBH(get,RootID,Acc),
  {NewRootID,Acc1}=delete_1(Key, Node, {DBH, Acc}),
  {{Size - 1, NewRootID}, Acc1}.

-spec delete_1(key(), tree_node(), db()) -> any().
delete_1(Key, {Key, _, _}, {DBH, Acc}) ->
  Acc1=DBH(del,<<"L",Key/binary>>,Acc),
  {empty, Acc1};
delete_1(Key, {InnerKey, _, LeftNodeID, RightNodeID}, {DBH, Acc0}) ->
  Acc=DBH(del,<<"N",InnerKey/binary>>,Acc0),
  case Key < InnerKey of
    true ->
      {LeftNode,_}=DBH(get,LeftNodeID,Acc),
      case delete_1(Key, LeftNode, {DBH, Acc}) of
        {empty,Acc1} ->
          {RightNodeID,Acc1};
        {NewLeftNodeID,Acc1} ->
          NewNID= <<"N",InnerKey/binary>>,
          LeftH=nodeid_hash(NewLeftNodeID, {DBH, Acc1}),
          RightH=nodeid_hash(RightNodeID, {DBH, Acc1}),
          IH=inner_hash(LeftH,
                        RightH,
                        {DBH, Acc1}
                       ),
          NewInnerNode= {InnerKey, IH ,
                         NewLeftNodeID, RightNodeID},
          Acc2=DBH(put, {NewNID, NewInnerNode}, DBH(del, Key, Acc1)),
          {NewNID,Acc2}
      end;
    _ ->
      {RightNode,_}=DBH(get,RightNodeID,Acc),
      case delete_1(Key, RightNode, {DBH, Acc}) of
        {empty,Acc1} ->
          {LeftNodeID,Acc1};
        {NewRightNodeID, Acc1} ->
          NewNID= <<"N",InnerKey/binary>>,
          IH=inner_hash(nodeid_hash(LeftNodeID, {DBH, Acc1}), 
                        nodeid_hash(NewRightNodeID, {DBH, Acc1}),
                        {DBH, Acc1}
                       ),
          NewInnerNode= {InnerKey, 
                         IH, 
                         LeftNodeID, NewRightNodeID},
          Acc2=DBH(put, {NewNID, NewInnerNode}, Acc1),
          {NewNID,Acc2}
      end
  end.

-spec empty() -> any().
%% @doc Return an empty tree.
empty() ->
    {0, empty}.

-spec size(db()) -> non_neg_integer().
%% @doc Return number of elements stored in the tree.
size({Size, _}) ->
    Size.

-spec leaf_hash(key(), value()) -> hash().
leaf_hash(Key, Value) ->
    KeyHash = ?HASH(Key),
    ValueHash = ?HASH(Value),
    ?HASH(<<KeyHash/binary, ValueHash/binary>>).

-spec inner_hash(hash(), hash(), any()) -> hash().
inner_hash(LeftHash, RightHash, _) ->
  ?HASH(<<LeftHash/binary, RightHash/binary>>).

-spec root_hash(any()) -> hash() | undefined.
%% @doc Return the hash of root node.
root_hash({DBH, DBAcc}) ->
  {{_Size,RootID},_Acc1}=DBH(get,<<"R">>,DBAcc),
  nodeid_hash(RootID, {DBH,DBAcc}).

-spec merkle_proof(key(), any()) -> merkle_proof().
%% @doc For a given key return a proof that, along with its value, it is contained in tree.
%% Hash for root node is not included in the proof.
merkle_proof(Key, {DBH, Acc}) ->
  {{_Size, RootNode},Acc1} = DBH(get,<<"R">>,Acc),
  merkle_proof_node(Key, RootNode, {DBH, Acc1}).

%  NewLID= <<"L",Key/binary>>,
%  NewLeafNode = {Key, Value, leaf_hash(Key, Value)},
%  Acc1=DBH(put, {NewLID,NewLeafNode}, Acc),

-spec merkle_proof_node(key(), binary(), db()) -> merkle_proof().
merkle_proof_node(RKey, <<"L",K1/binary>>=Node, {DBH, Acc}) ->
  if(RKey =/= K1) ->
      throw('no_key');
    true ->
      ok
  end,
  {{Key, Value, _},_Acc1} = DBH(get,Node,Acc),
  {?HASH(Key), ?HASH(Value)};

merkle_proof_node(Key, <<"N",_/binary>>=Node, {DBH, Acc}) ->
  {{InnerKey, _, Left, Right},_}=DBH(get,Node,Acc),
  case Key < InnerKey of
    true ->
      {merkle_proof_node(Key, Left, {DBH, Acc}), nodeid_hash(Right, {DBH, Acc})};
    _ ->
      {nodeid_hash(Left, {DBH, Acc}), merkle_proof_node(Key, Right, {DBH, Acc})}
  end.

-spec verify_merkle_proof(key(), value(), Root::hash(), merkle_proof()) ->
  ok | {error, Reason} when
    Reason :: {key_hash_mismatch, hash()}
    | {value_hash_mismatch, hash()}
    | {root_hash_mismatch, hash()}.
%% @doc Verify a proof against a leaf and a root node hash.
verify_merkle_proof(Key, Value, RootHash, Proof) ->
    {KH, VH} = {?HASH(Key), ?HASH(Value)},
    {PKH, PVH} = bottom_merkle_proof_pair(Proof),
    if
        PKH =/= KH ->
            {error, {key_hash_mismatch, PKH}};
        PVH =/= VH ->
            {error, {value_hash_mismatch, PKH}};
        true ->
            PRH = merkle_fold(Proof),
            if
                PRH =/= RootHash ->
                    {error, {root_hash_mismatch, PRH}};
                true ->
                    ok
            end
    end.

-spec from_list(list({key(), value()}), dbh()|db()) -> any().
%% @doc Create a tree from a list.
%% This creates a tree by iteratively inserting elements and not necessarily results in a perfect balance, like the one obtained when running {@link from_orddict/1}.
from_list(List, DBH) when is_function(DBH,3) ->
    from_list(List, {DBH,#{<<"R">>=>empty()}});

%-spec from_list(list({key(), value()}), {fun(atom(),any(),any()), any()}) -> any().
from_list([], {_DBH,Acc}) ->
    Acc;
from_list([{Key, Value}|Rest], {DBH,Acc}) ->
    from_list(Rest, {DBH,enter(Key, Value, {DBH,Acc})}).

-spec to_orddict(db()) -> list({key(), value()}).
%% @doc Convert tree to an orddict.
to_orddict({DBH,Acc}) ->
  foldr(
    fun({K,V},A) ->
        [{K,V}|A]
    end,[],{DBH,Acc}).

 %   foldr(
 %     fun (KV, A) ->
 %             [KV|A]
 %     end,
 %     [],
 %     {DBH,Acc}).

-spec keys(any()) -> list(key()).
%% @doc Return the keys as an ordered list.
keys({DBH,Acc}) ->
  foldr(
      fun ({Key, _}, A) -> [Key|A] end,
      [],
      {DBH,Acc}).

%-spec foldr(fun(({key(), value()}, Acc :: any(), {fun(atom(),any(),any()), any()} ) -> any()), Acc :: any(), tree()) -> Acc :: any().
%% @doc Iterate through keys and values, from those with highest keys to lowest.
foldr(Fun, Acc, {DBH, DBAcc}) ->
  {{_Size,RootID},_Acc1}=DBH(get,<<"R">>,DBAcc),
  foldr_1(Fun, Acc, RootID, {DBH, DBAcc}).

%-spec foldr_1(fun(({key(), value()}, Acc :: any()) -> any()), Acc :: any(),
%                {fun(atom(),any(),any()) -> any(), any()}) -> Acc :: any().
foldr_1(_, Acc, empty, _) ->
  Acc;
foldr_1(F, Acc, <<"L",_/binary>>=LeafID, {DBH, DBAcc}) ->
  {{Key, Value, _},_Acc1}=DBH(get,LeafID,DBAcc),
  F({Key, Value}, Acc);
foldr_1(F, Acc, <<"N",_/binary>>=NodeID, {DBH, DBAcc}) ->
  {{_, _, Left, Right},_Acc1}=DBH(get,NodeID,DBAcc),
  foldr_1(F, foldr_1(F, Acc, Right, {DBH, DBAcc}), Left, {DBH, DBAcc}).

-spec nodeid_hash(binary() | 'empty', db()) -> hash() | undefined.
nodeid_hash(empty,_) ->
  undefined;

nodeid_hash(<<"N",_/binary>>=Key,{DBH,Acc}) ->
  {{_,Hash,_,_},_Acc1}=DBH(get,Key,Acc),
  Hash;

nodeid_hash(<<"L",_/binary>>=Key,{DBH,Acc}) ->
  {{_,_,Hash},_Acc1}=DBH(get,Key,Acc),
  Hash.


-spec node_hash(tree_node()) -> hash() | undefined.
node_hash(empty) ->
    undefined;

node_hash({_, _, Hash}) ->
    Hash;

node_hash({_, Hash, _, _}) ->
    Hash.


node_id({Key, _, _}) ->
    <<"L",Key/binary>>;

node_id({Key, _, _, _}) ->
    <<"N",Key/binary>>.


-spec enter(key(), value(), db()) -> any().
%% @doc Insert or update key and value into tree.
enter(Key, Value, {DBH, Acc}) ->
  {{Size, RootNode},Acc1} = DBH(get,<<"R">>,Acc),
  {NewRootNode, undefined, undefined, KeyExists, {_,Acc2}} =
                          enter_1(Key, Value, RootNode, 0, Size, {DBH, Acc1}),
  NewSize = case KeyExists of
              true -> Size;
              _ -> Size + 1
            end,
  %{NewSize, NewRootNode},
  DBH(put,{<<"R">>,{NewSize, NewRootNode}},Acc2).

-spec enter_1(key(), value(), tree_node(), Depth :: non_neg_integer(), TreeSize ::
              non_neg_integer(), db()) -> any().

%% in case of empty list
enter_1(Key, Value, empty, _, _, {DBH, Acc}) ->
  NewLID= <<"L",Key/binary>>,
  NewLeafNode = {Key, Value, leaf_hash(Key, Value)},
  Acc1=DBH(put, {NewLID,NewLeafNode}, Acc),
  {NewLID, undefined, undefined, false, {DBH, Acc1}};

%% in case of leaf node reached
enter_1(Key, Value, <<"L",ExistingKey/binary>>=ExistingLeafNode, Depth, TreeSize, {DBH, Acc}) ->
  NewLID= <<"L",Key/binary>>,
  NewLeafNode = {Key, Value, leaf_hash(Key, Value)},
  Acc1=DBH(put, {NewLID,NewLeafNode}, Acc),
  case Key =:= ExistingKey of
    true -> %update leaf
      %{NewLeafNode, undefined, undefined, true};
      {NewLID, undefined, undefined, true, {DBH, Acc1}};
    _ -> %Make node instead of leaf
      NewTreeSize = TreeSize + 1,
      NewDepth = Depth + 1,
      {InnerKey, LeftNode, RightNode} =
      case Key > ExistingKey of
        true ->
          {Key, ExistingLeafNode, NewLID};
        _ ->
          {ExistingKey, NewLID, ExistingLeafNode}
      end,
      NewNID= <<"N",InnerKey/binary>>,
      case rebalancing_needed(NewTreeSize, NewDepth) of
        true ->
          NewInnerNode={InnerKey, to_be_computed, LeftNode, RightNode},
          Acc2=DBH(put, {NewNID,NewInnerNode}, Acc1),
          {NewNID,
           2,
           1,
           false,
           {DBH, Acc2}};
        _ ->
          HashLeft=nodeid_hash(LeftNode, {DBH, Acc1}),
          HashRight=nodeid_hash(RightNode, {DBH, Acc1}),
          InHash=inner_hash(HashLeft, HashRight, {DBH, Acc1}),
          NewInnerNode={InnerKey, InHash, LeftNode, RightNode},
          Acc2=DBH(put, {NewNID,NewInnerNode}, Acc1),
          {NewNID,
           undefined,
           undefined,
           false,
           {DBH, Acc2}}
      end
  end;

%% in case of inner node
enter_1(Key, Value, <<"N",_/binary>>=InnerNode, Depth, TreeSize, {DBH, Acc}) ->
  {{InnerKey, _, LeftNode, RightNode}, Acc1} = DBH(get,InnerNode,Acc),
    NodeToFollowSymb =
        case Key < InnerKey of
            true -> left;
            _ -> right
        end,
    {NodeToFollow, NodeNotChanged} =
        case NodeToFollowSymb of
            right -> {RightNode, LeftNode};
            left -> {LeftNode, RightNode}
        end,
    {NewNode, RebalancingCount, Height, KeyExists, {_, Acc2}} = 
            enter_1(Key, Value, NodeToFollow, Depth + 1, TreeSize, {DBH, Acc1}),
    {NewLeftNode, NewRightNode} =
        case NodeToFollowSymb of
            right ->
                {LeftNode, NewNode};
            _ ->
                {NewNode, RightNode}
        end,
    case RebalancingCount of
        undefined ->
            {NewInnerNode,{_, Acc3}} = update_inner_node(InnerNode, NewLeftNode, NewRightNode, 
                                                         {DBH, Acc2}),
            {NewInnerNode, undefined, undefined, KeyExists, {DBH, Acc3}};
        _ ->
            NodeSize = node_size(NodeNotChanged, {DBH, Acc2}),
            Count = RebalancingCount + NodeSize,
            NewHeight = Height + 1,
            NewInnerNodeUnbalanced = {InnerKey, to_be_computed, NewLeftNode, NewRightNode},
            NewNID= <<"N",InnerKey/binary>>,
            Acc4=DBH(put, {NewNID,NewInnerNodeUnbalanced}, DBH(del, InnerNode, Acc2)),
            case may_be_rebalanced(Count, NewHeight) of
              true ->
                {BalancedTopNode, Acc5}=balance_node(NewNID, Count, {DBH, Acc4}),
                {node_id(BalancedTopNode),
                 undefined,
                 undefined,
                 KeyExists,
                 {DBH, Acc5}};
              _ ->
                {NewNID,
                 Count,
                 NewHeight,
                 KeyExists,
                 {DBH, Acc4}}
            end
    end.

-spec rebalancing_needed(TreeSize :: non_neg_integer(), Depth :: non_neg_integer()) -> boolean().
rebalancing_needed(TreeSize, Depth) ->
  math:pow(2, Depth) > math:pow(TreeSize, ?C).

-spec may_be_rebalanced(Count :: non_neg_integer(), Height :: non_neg_integer()) -> boolean().
may_be_rebalanced(Count, Height) ->
    math:pow(2, Height) > math:pow(Count, ?C).

-spec node_size(tree_node(), db()) -> non_neg_integer().
node_size(empty, _) ->
  0;
node_size(<<"L",_/binary>>, _) ->
  1;
node_size(<<"N",_/binary>>=NodeID, {DBH, Acc}) ->
  {{_InnerKey, _, LeftNode, RightNode}, _} = DBH(get,NodeID,Acc),
  SizeL=node_size(LeftNode,{DBH,Acc}),
  SizeR=node_size(RightNode,{DBH,Acc}),
  SizeL+SizeR.

-spec balance_orddict(list({key(), value()}), Size :: non_neg_integer(), db()) ->
  {tree_node(),any()}.
balance_orddict(KVOrdDict, Size, {DBH, Acc}) ->
  {{Node, []},Acc1} = balance_orddict_1(KVOrdDict, Size, {DBH, Acc}),
  {Node,Acc1}.

-spec balance_orddict_1(list({key(), value()}), Size :: non_neg_integer(), db()) ->
  {{tree_node(), list({key(), value()})}, any()}.

balance_orddict_1(OrdDict, Size, {DBH, Acc}) when Size > 1 ->
  Size2 = Size div 2,
  Size1 = Size - Size2,
  BOD1=balance_orddict_1(OrdDict, Size1, {DBH, Acc}),
  {{LeftNode, OrdDict1=[{Key, _} | _]}, Acc1} = BOD1,
  {{RightNode, OrdDict2}, Acc2} = balance_orddict_1(OrdDict1, Size2, {DBH, Acc1}),
  InnerHash=inner_hash(
              node_hash(LeftNode), 
              node_hash(RightNode), {DBH, Acc2}),
  InnerNode = {Key, InnerHash, node_id(LeftNode), node_id(RightNode)},
  NID = node_id(InnerNode), 
  Acc3=DBH(put, {NID,InnerNode}, Acc2),
  {{InnerNode, OrdDict2},Acc3};
balance_orddict_1([{Key, Value} | OrdDict], 1, {_DBH, Acc}) ->
  {{{Key, Value, leaf_hash(Key, Value)}, OrdDict}, Acc};
balance_orddict_1(OrdDict, 0, {_DBH, Acc}) ->
  {{empty, OrdDict}, Acc}.
%
%-spec node_to_orddict(tree_node()) -> list({key(), value()}).
node_to_orddict(Node, DBH) ->
  foldr_1(fun (KV, Acc) -> [KV|Acc] end, [], Node, DBH).

-spec balance_node(binary(), Size :: non_neg_integer(), db()) -> any().
balance_node(Node, Size, DBH) ->
  KVOrdDict = node_to_orddict(Node, DBH),
  balance_orddict(KVOrdDict, Size, DBH).

%-spec balance(tree()) -> tree().
%% @doc Perfectly balance a tree.
balance({DBH, DBAcc}) ->
  {{Size, RootNode}, _} = DBH(get,<<"R">>, DBAcc),
  if(Size==0) ->
      DBAcc;
    true ->
      {NewRoot,Acc1}=balance_orddict(node_to_orddict(RootNode, {DBH, DBAcc}), Size, {DBH, DBAcc}),
      DBH(put,{<<"R">>,{Size,node_id(NewRoot)}},Acc1)
  end.


-spec lookup(key(), db()) -> value() | none.
%% @doc Fetch value for key from tree.
lookup(Key, {_, RootNode}) ->
    lookup_1(Key, RootNode).

-spec lookup_1(key(), inner_node() | leaf_node()) -> value() | none.
lookup_1(Key, {Key, Value, _}) ->
    Value;
lookup_1(Key, {InnerKey, _, Left, Right}) ->
    case Key < InnerKey of
        true ->
            lookup_1(Key, Left);
        _ ->
            lookup_1(Key, Right)
    end;
lookup_1(_, _) ->
    none.

-spec update_inner_node(binary(), Left::binary(), Right::binary(), db()) -> {binary(),db()}.
update_inner_node(<<"N",_/binary>>=Node, NewLeft, NewRight, {DBH, Acc}) ->
  {{Key, _, Left, Right}, _} = DBH(get,Node,Acc),
  case lists:map(fun (CNode) ->
                     nodeid_hash(CNode, {DBH,Acc})
                 end, [Left, Right, NewLeft, NewRight]) of
    [LeftHash, RightHash, LeftHash, RightHash] ->
      %% Nothing changed, no need to rehash.
      {Node,{DBH,Acc}};
    [_, _, NewLeftHash, NewRightHash] ->
      NewHash=inner_hash(NewLeftHash, NewRightHash, {DBH,Acc}),
      NewNID= <<"N",Key/binary>>,
      NewInnerNode={Key, NewHash, NewLeft, NewRight},
      Acc3=DBH(put, {NewNID,NewInnerNode}, DBH(del, Node, Acc)),
      {NewNID, {DBH,Acc3}}
  end.

-spec merkle_fold(merkle_proof()) -> hash().
merkle_fold({Left, Right}) ->
    LeftHash = merkle_fold(Left),
    RightHash = merkle_fold(Right),
    ?HASH(<<LeftHash/binary, RightHash/binary>>);
merkle_fold(Hash) ->
    Hash.

-spec bottom_merkle_proof_pair(merkle_proof()) -> {hash(), hash()}.
bottom_merkle_proof_pair({Pair, Hash}) when is_tuple(Pair), is_binary(Hash) ->
    bottom_merkle_proof_pair(Pair);
bottom_merkle_proof_pair({_Hash, Pair}) when is_tuple(Pair) ->
    bottom_merkle_proof_pair(Pair);
bottom_merkle_proof_pair(Pair) ->
    Pair.

-ifdef(TEST).
empty_test_() ->
    [?_assertEqual(0, ?MODULE:size(empty()))].

%% Types for Triq.
key() ->
    binary().
value() ->
    binary().
kv_orddict() ->
    ?LET(L, list({key(), value()}), orddict:from_list(L)).
tree() ->
    %% The validity of data generated by this generator depends on the validity of the `from_list' function.
    %% This should not be a problem as long as the `from_list' function itself is tested.
    ?LET(KVO, list({key(), value()}), from_list(KVO)).
non_empty_tree() ->
    ?SUCHTHAT(Tree, tree(), element(1, Tree) > 0).

%% Helper functions for Triq.
-spec height(tree()) -> non_neg_integer().
height({_, RootNode}) ->
    node_height(RootNode).

-spec node_height(tree_node()) -> non_neg_integer().
node_height(empty) ->
    %% Strictly speaking, there is no height for empty tree.
    0;
node_height({_, _, _}) ->
    0;
node_height({_, _, Left, Right}) ->
    1 + max(node_height(Left), node_height(Right)).

-spec shallow_height(tree()) -> non_neg_integer().
shallow_height({_, RootNode}) ->
    node_shallow_height(RootNode).

-spec node_shallow_height(tree_node()) -> non_neg_integer().
node_shallow_height(empty) ->
    %% Strictly speaking, there is no height for empty tree.
    0;
node_shallow_height({_, _, _}) ->
    0;
node_shallow_height({_, _, Left, Right}) ->
    1 + min(node_shallow_height(Left), node_shallow_height(Right)).

-spec is_perfectly_balanced(tree()) -> boolean().
is_perfectly_balanced(Tree) ->
    height(Tree) - shallow_height(Tree) =< 1.

-spec fun_idempotent(F :: fun((X) -> X), X) -> boolean().
%% @doc Return true if F(X) =:= X.
fun_idempotent(F, X) ->
    F(X) =:= X.

prop_lookup_does_not_fetch_deleted_key() ->
    ?FORALL({Tree, Key, Value},
            {tree(), key(), value()},
            none =:= lookup(Key, delete(Key, enter(Key, Value, Tree)))).
prop_deletion_decreases_size_by_1() ->
    ?FORALL({Tree, Key, Value},
            {tree(), key(), value()},
            ?MODULE:size(enter(Key, Value, Tree)) - 1 =:= ?MODULE:size(delete(Key, enter(Key, Value, Tree)))).
prop_merkle_proofs_fold_to_root_hash() ->
    ?FORALL({Tree, Key, Value},
            {tree(), key(), value()},
            root_hash(enter(Key, Value, Tree)) =:= merkle_fold(merkle_proof(Key, enter(Key, Value, Tree)))).
prop_merkle_proofs_contain_kv_hashes_at_the_bottom() ->
    ?FORALL({Tree, Key, Value},
            {tree(), key(), value()},
            bottom_merkle_proof_pair(merkle_proof(Key, enter(Key, Value, Tree))) =:= {?HASH(Key), ?HASH(Value)}).
prop_merkle_proofs_can_be_verified() ->
    ?FORALL({Tree, Key, Value},
            {tree(), key(), value()},
            ok =:= verify_merkle_proof(Key, Value, root_hash(enter(Key, Value, Tree)), merkle_proof(Key, enter(Key, Value, Tree)))).
prop_merkle_proofs_verification_reports_mismatch_for_wrong_key() ->
    ?FORALL({Tree, Key, Value},
            {tree(), key(), value()},
            case verify_merkle_proof(<<"X", Key/binary>>, Value, root_hash(enter(Key, Value, Tree)), merkle_proof(Key, enter(Key, Value, Tree))) of
                {error, {key_hash_mismatch, H}} when is_binary(H) ->
                    true;
                _ ->
                    false
            end).
prop_merkle_proofs_verification_reports_mismatch_for_wrong_value() ->
    ?FORALL({Tree, Key, Value},
            {tree(), key(), value()},
            case verify_merkle_proof(Key, <<"X", Value/binary>>, root_hash(enter(Key, Value, Tree)), merkle_proof(Key, enter(Key, Value, Tree))) of
                {error, {value_hash_mismatch, H}} when is_binary(H) ->
                    true;
                _ ->
                    false
            end).
prop_merkle_proofs_verification_reports_mismatch_for_wrong_root_hash() ->
    ?FORALL({Tree, Key, Value},
            {tree(), key(), value()},
            case verify_merkle_proof(Key, Value, begin RH = root_hash(enter(Key, Value, Tree)), <<"X", RH/binary>> end, merkle_proof(Key, enter(Key, Value, Tree))) of
                {error, {root_hash_mismatch, H}} when is_binary(H) ->
                    true;
                _ ->
                    false
            end).
prop_from_list_size() ->
    ?FORALL(KVList, list({key(), value()}),
            length(proplists:get_keys(KVList)) =:= ?MODULE:size(from_list(KVList))).
prop_from_orddict_size() ->
    ?FORALL(KVO, kv_orddict(),
            length(KVO) =:= ?MODULE:size(from_list(KVO))).
prop_orddict_conversion_idempotence() ->
    ?FORALL(KVO, kv_orddict(), KVO =:= to_orddict(from_orddict(KVO))).
prop_from_orddict_returns_a_perfectly_balanced_tree() ->
    ?FORALL(KVO, kv_orddict(), is_perfectly_balanced(from_orddict(KVO))).
prop_keys() ->
    ?FORALL(Tree, tree(), keys(Tree) =:= [Key || {Key, _} <- to_orddict(Tree)]).
from_list_sometimes_doesnt_return_a_perfectly_balanced_tree_test() ->
    ?assertNotEqual(
       true,
       triq:counterexample(
         ?FORALL(
            KVList,
            list({key(), value()}),
            is_perfectly_balanced(from_list(KVList))))).
prop_foldr_iterates_on_proper_ordering_and_contains_no_duplicates() ->
    ?FORALL(Tree, tree(),
            fun_idempotent(
              fun lists:usort/1,
              foldr(
                fun({Key, _}, Acc) -> [Key|Acc] end,
                [],
                Tree)
             )).
prop_enter_is_idempotent() ->
    ?FORALL({Tree, Key, Value},
            {tree(), key(), value()},
            fun_idempotent(
              fun (Tree_) -> enter(Key, Value, Tree_) end,
              enter(Key, Value, Tree))).
prop_entered_value_can_be_retrieved() ->
    ?FORALL({Tree, Key, Value},
            {tree(), key(), value()},
            Value =:= lookup(Key, enter(Key, Value, Tree))).
prop_entered_value_can_be_retrieved_after_balancing() ->
    ?FORALL({Tree, Key, Value},
            {tree(), key(), value()},
            Value =:= lookup(Key, balance(enter(Key, Value, Tree)))).
prop_height_constrained() ->
    ?FORALL(Tree, non_empty_tree(), math:pow(2, height(Tree)) =< math:pow(?MODULE:size(Tree), ?C)).
prop_balancing_yields_same_orddict() ->
    ?FORALL(Tree, tree(), to_orddict(Tree) =:= to_orddict(balance(Tree))).
prop_entering_key_second_time_does_not_increase_size() ->
    ?FORALL({Tree, Key, Value1, Value2},
            {tree(), key(), value(), value()},
            ?MODULE:size(enter(Key, Value1, Tree)) =:= ?MODULE:size(enter(Key, Value2, enter(Key, Value1, Tree)))).
prop_tree_after_explicit_balancing_is_perfectly_balanced() ->
    ?FORALL(Tree, tree(), is_perfectly_balanced(balance(Tree))).
-endif.
