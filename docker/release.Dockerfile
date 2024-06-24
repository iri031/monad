# syntax=docker/dockerfile:1-labs

FROM ubuntu:24.04 as base

RUN apt update
RUN apt upgrade -y
RUN apt install -y ca-certificates curl gnupg software-properties-common wget

RUN add-apt-repository -y ppa:ubuntu-toolchain-r/test
RUN add-apt-repository -y ppa:mhier/libboost-latest
RUN apt update

RUN apt install -y libstdc++-13-dev

RUN apt-get install -y \
  libboost-atomic1.83.0 \
  libboost-container1.83.0 \
  libboost-fiber1.83.0 \
  libboost-filesystem1.83.0 \
  libboost-graph1.83.0 \
  libboost-json1.83.0 \
  libboost-regex1.83.0 \
  libboost-stacktrace1.83.0

RUN apt install -y \
  libarchive-dev \
  libbenchmark-dev \
  libbrotli-dev \
  libcap-dev \
  libcli11-dev \
  libgmock-dev \
  libgmp-dev \
  libgtest-dev \
  libtbb-dev \
  liburing-dev \
  libzstd-dev

FROM base as build

RUN apt install -y gcc-13 g++-13

RUN apt install -y ninja-build pkg-config
RUN apt install -y python3-pytest

######## BEGIN CMAKE
RUN wget -O - https://apt.kitware.com/keys/kitware-archive-latest.asc 2>/dev/null \
  | gpg --dearmor - \
  | tee /usr/share/keyrings/kitware-archive-keyring.gpg >/dev/null
RUN echo 'deb [signed-by=/usr/share/keyrings/kitware-archive-keyring.gpg] https://apt.kitware.com/ubuntu/ jammy main' \
  | tee /etc/apt/sources.list.d/kitware.list >/dev/null
RUN apt-get update
RUN rm /usr/share/keyrings/kitware-archive-keyring.gpg
RUN apt-get -y install kitware-archive-keyring
RUN apt-get -y install cmake
######## END CMAKE

RUN apt-get install -y \
  libboost-fiber1.83-dev \
  libboost-graph1.83-dev \
  libboost-json1.83-dev \
  libboost-stacktrace1.83-dev \
  libboost1.83-dev \
  libcgroup-dev

COPY . src
WORKDIR src

ARG GIT_COMMIT_HASH
RUN test -n "$GIT_COMMIT_HASH"
ENV GIT_COMMIT_HASH=$GIT_COMMIT_HASH

RUN CC=gcc-13 CXX=g++-13 CMAKE_BUILD_TYPE=RelWithDebInfo CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" ./scripts/configure.sh

RUN ./scripts/build.sh

# security=insecure for tests which use io_uring
RUN --security=insecure CC=gcc-13 CXX=g++-13 CMAKE_BUILD_TYPE=RelWithDebInfo ./scripts/test.sh

FROM base as runner
COPY --from=build /src/build/libs/db/monad_mpt /usr/local/bin/
COPY --from=build /src/build/cmd/replay_ethereum /usr/local/bin/
COPY --from=build /src/build/cmd/monad /usr/local/bin/
