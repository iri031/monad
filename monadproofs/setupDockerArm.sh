set -e
set +x
docker pull arm64v8/debian
docker run --name fvarm -ti -w /root arm64v8/debian bash -l
docker stop fvarm
docker cp -a . fvarm:/root/
docker start fvarm
docker exec fvarm /root/fv-workspace/setupDebian.sh
