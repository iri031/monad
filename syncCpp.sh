#DST=/home/abhishek/work/coq/blue/fm-workspace-snapshot3b/fm-workspace-12-16/fmdeps/monad/asts
#CPP2V=~/work/coq/blue/fm-workspace-snapshot3b/fm-workspace-12-16/_build/install/default/bin/cpp2v
DST=/home/abhishek/work/coq/blue/fm-workspace-snapshot3b/fm-workspace-live/fmdeps/monad/asts
CPP2V=~/work/coq/blue/fm-workspace-snapshot3b/fm-workspace-live/_build/install/default/bin/cpp2v
$CPP2V  ./libs/execution/src/monad/execution/execute_block.cpp --no-elaborate -o $DST/exb.v --names=$DST/exb_names.v
#$CPP2V  ./libs/execution/src/monad/execution/execute_transaction.cpp --no-elaborate -o $DST/ext.v --names=$DST/ext_names.v
#rm /home/abhishek/work/coq/blue/fm-workspace-snapshot3/fm-workspace-12-16/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/data_class/lam_names.v
#~/work/coq/blue/fm-workspace-snapshot3/fm-workspace-12-16/_build/install/default/bin/cpp2v  ../lam.cpp --no-elaborate -o /home/abhishek/work/coq/blue/fm-workspace-snapshot3/fm-workspace-12-16/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/data_class/lam.v --names=/home/abhishek/work/coq/blue/fm-workspace-snapshot3/fm-workspace-12-16/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/data_class/lam_names.v
