docker stop cppfvcoq
set -e
set +x
docker start cppfvcoq
docker exec cppfvcoq mv /root/fv-workspace/monad/asts /root/ #git doesnt contain the huge ASTs of execute_block.cpp and execute_transaction.cpp
docker exec cppfvcoq rm -rf /root/fv-workspace/monad
docker cp -a monadproofs cppfvcoq:/root/fv-workspace/
docker exec cppfvcoq mv /root/fv-workspace/monadproofs /root/fv-workspace/monad
docker exec cppfvcoq rm -rf /root/fv-workspace/monad/proofs/execproofs/
docker exec cppfvcoq mv /root/asts/ /root/fv-workspace/monad/
docker exec cppfvcoq sh -c "echo 'ulimit -Ss unlimited'  > editDemo2Prf.sh"
docker exec cppfvcoq sh -c "echo 'emacs -nw fv-workspace/monad/proofs/demo2prf.v'  >> editDemo2Prf.sh"
docker exec cppfvcoq chmod +x editDemo2Prf.sh
docker exec cppfvcoq bash -login -c "cd /root/fv-workspace/monad; dune build"


# docker exec cppfvcoq mkdir -p /home/coq/.config/dune/
# docker exec cppfvcoq sh -c "echo '(lang dune 3.6)' > /home/coq/.config/dune/config"
# docker exec cppfvcoq sh -c "echo '(cache enabled)' >> /home/coq/.config/dune/config"
# docker exec cppfvcoq sh -c "echo '(display short)' >> /home/coq/.config/dune/config"
# docker exec cppfvcoq sudo apt -y install expect python3-psutil
# #docker exec cppfvcoq apt get install emacs vscode ....
# docker stop cppfvcoq
# docker commit cppfvcoq coq817bhv
# #docker rm cppfvcoq # this container does not have the necessary -v flags etc. will recreate from coq817bhv
