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


