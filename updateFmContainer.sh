
docker stop cppfvcoq
set -e
set +x
docker start cppfvcoq
docker exec cppfvcoq mv /root/fv-workspace/monad/asts /root/ #git doesnt contain the huge ASTs of execute_block.cpp and execute_transaction.cpp
docker exec cppfvcoq rm -rf /root/fv-workspace/monad
docker cp -a monadproofs cppfvcoq:/root/fv-workspace/
docker exec cppfvcoq mv /root/fv-workspace/monadproofs /root/fv-workspace/monad
docker exec cppfvcoq rm -rf /root/fv-workspace/monad/proofs/execproofs/ # not necessary but these take several minutes to compile
docker exec cppfvcoq mv /root/asts/ /root/fv-workspace/monad/
docker exec cppfvcoq sh -c "echo 'ulimit -Ss unlimited'  > editDemo2Prf.sh"
docker exec cppfvcoq sh -c "echo 'emacs -nw fv-workspace/monad/proofs/demo2prf.v'  >> editDemo2Prf.sh"
docker exec cppfvcoq chmod +x editDemo2Prf.sh
docker exec cppfvcoq bash -login -c "cd /root/fv-workspace/monad; dune build"
echo "Success. your docker container cppfvcoq is now up to date"
