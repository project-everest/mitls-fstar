# Dev container for agentic-tls.
#
# This image carries ONLY the system packages required to:
#   1. build the EverParse / QuackyDucky toolchain (F*, KaRaMeL, QuackyDucky,
#      LowParse) via `make quackyducky`, which spins up its own local opam
#      switch (OCaml 5.3.0) and downloads the pinned Z3 binaries itself; and
#   2. verify, extract and interop-test agentic-tls (C compiler + OpenSSL).
#
# It deliberately omits EverParse dependencies that QuackyDucky does not need
# (clang, cmake, rust, python3-pip/venv, code-server, libsqlite3-dev, ...).
# The heavy toolchain build is performed by ./setup.sh as a post-create step,
# not baked into the image, so the image stays small and cache-friendly.
FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive

# Minimal apt set:
#   ca-certificates,curl,git  - fetch the EverParse fork, HACL* submodule, RFCs, Z3
#   opam                      - drives the local OCaml switch for the F*/KaRaMeL build
#   build-essential           - gcc/make for the OCaml build and the agentic-tls C code
#   pkg-config                - OpenSSL discovery + opam package configuration
#   libgmp-dev                - zarith (F*/Z3 bignum)
#   libffi-dev                - ctypes (EverParse opam dep)
#   libssl-dev,openssl        - OpenSSL headers/lib + CLI for the interop echo test
#   unzip                     - extract the downloaded Z3 release archives
#   python3                   - agentic-tls test scripts (port picker, payload gen)
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      ca-certificates \
      curl \
      git \
      opam \
      build-essential \
      pkg-config \
      libgmp-dev \
      libffi-dev \
      libssl-dev \
      openssl \
      unzip \
      python3 \
 && rm -rf /var/lib/apt/lists/*

# Run as a non-root user (opam refuses to operate as root, and bind-mounted
# workspace files stay owned by a normal user).  ubuntu:24.04 ships a default
# uid-1000 "ubuntu" user; replace it with the conventional "vscode" user.
ARG USERNAME=vscode
ARG USER_UID=1000
ARG USER_GID=1000
RUN userdel -r ubuntu 2>/dev/null || true \
 && groupadd --gid ${USER_GID} ${USERNAME} \
 && useradd --uid ${USER_UID} --gid ${USER_GID} -m -s /bin/bash ${USERNAME}

USER ${USERNAME}
ENV HOME=/home/${USERNAME}
WORKDIR ${HOME}
