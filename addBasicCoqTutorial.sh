docker stop cppfvcoq
set -e
set +x
docker start cppfvcoq
docker exec -it cppfvcoq bash -login -c "
    cd /root/fv-workspace && \
    git clone https://github.com/aa755/BasicCoqTutorial.git && \
    echo '-Q BasicCoqTutorial LF' >> _CoqProject &&\
    echo '-Q _build/default/BasicCoqTutorial LF' >> _CoqProject &&\
    dune build BasicCoqTutorial
"
echo "Success. your docker image now has the Basic Coq tutorials. open the first chapter in the container using emacs -nw /root/fv-workspace/BasicCoqTutorial/c1Basics.v "

