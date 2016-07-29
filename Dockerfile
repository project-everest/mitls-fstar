FROM ubuntu:14.04
MAINTAINER Sreekanth Kannepalli 
RUN apt-get update && apt-get install -y software-properties-common
RUN add-apt-repository --yes ppa:avsm/ppa
RUN add-apt-repository --yes ppa:ubuntu-toolchain-r/test
RUN add-apt-repository --yes ppa:0k53d-karl-f830m/openssl
RUN apt-get -qq update 

RUN apt-get install --yes make m4 sqlite3 libssl-dev opam libsqlite3-dev libgmp-dev
RUN export OPAMYES=true
RUN opam init 
RUN eval $(opam config env)
RUN opam install depext conf-m4 batteries fileutils stdint zarith yojson 
WORKDIR root
ENV Z3 z3-4.4.1-x64-ubuntu-14.04
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.4.1/$Z3.zip 
RUN unzip $Z3.zip
RUN echo "export PATH=~/z3-4.4.1-x64-ubuntu-14.04/bin:\$PATH" >> ~/.bashrc
RUN echo "eval \$(opam config env)" >> ~/.bashrc 



