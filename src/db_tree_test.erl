-module(db_tree_test).
-compile([export_all,nowarn_export_all]).

testFun(get, Key, Acc) ->
  {maps:get(Key, Acc),Acc};

testFun(put, {Key, Value}, Acc) ->
  maps:put(Key, Value, Acc);

testFun(del, Key, Acc) ->
  maps:remove(Key, Acc);

testFun(Action, Arg, _Acc) ->
  throw({bad_action,Action,Arg}).


run() ->
  Fun=fun testFun/3,
  M=db_merkle_trees:balance(
      {Fun,
       db_merkle_trees:from_list(
         [ {<<($a+N)>>,<<N>>} || N <- lists:seq(0,8) ],
         Fun
        )
      }),
  {_,Root}=maps:get(<<"R">>,M),
  %RootNode=maps:get(Root,M),
  M1=db_merkle_trees:delete(<<"a">>,{fun db_tree_test:testFun/3, M}),
  M2=db_merkle_trees:delete(<<"b">>,{fun db_tree_test:testFun/3, M1}),
%  {
%   db_merkle_trees:to_orddict({fun db_tree_test:testFun/3, M}),
%   %db_merkle_trees:foldr(
%   % fun({K,V},Acc) ->
%   %     [{K,V}|Acc]
%   % end,[],{fun db_tree_test:testFun/3, M}),
%   db_merkle_trees:keys({fun db_tree_test:testFun/3, M1})
%   }.
  RootNode=maps:get(Root,M2),
  % display_tree(0,RootNode,M),
  display_tree(0,RootNode,M2),
  MR=db_merkle_trees:root_hash({fun db_tree_test:testFun/3,M2}),
  MP=db_merkle_trees:merkle_proof(<<"i">>,{fun db_tree_test:testFun/3,M2}),
  ok=db_merkle_trees:verify_merkle_proof(<<"i">>,<<8>>,MR,MP),
  MR=<<242,75,174,24,20,49,52,251,
       102,115,1,33,222,39,247,200,
       205,39,38,219,108,166,228,137,
       239,110,215,75,134,8,52,95>>.

display_tree(Depth, {Key,V,H}, _Acc) ->
  PadSize="~"++integer_to_list(Depth*2)++"s",
  io:format(PadSize++" ~p = ~p ~s~n",["",Key,V,h(H)]);

display_tree(Depth, {Key,H,Left,Right}, Acc) ->
  PadSize="~"++integer_to_list(Depth*2)++"s",
  io:format(PadSize++" ~p ~s~n",["",Key,h(H)]),
  LN=maps:get(Left,Acc),
  display_tree(Depth+1,LN,Acc),
  RN=maps:get(Right,Acc),
  display_tree(Depth+1,RN,Acc),
  ok.

h(<<H0,H1,H2,H3,_/binary>>) ->
  io_lib:format("~2.16.0B~2.16.0B~2.16.0B~2.16.0B",[H0,H1,H2,H3]).

