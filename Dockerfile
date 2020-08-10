# See here for image contents: https://github.com/microsoft/vscode-dev-containers/tree/v0.131.0/containers/ubuntu/.devcontainer/base.Dockerfile
ARG VARIANT="focal"
FROM mcr.microsoft.com/vscode/devcontainers/base:0-${VARIANT}

RUN apt-get update \
    && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y install --no-install-recommends ocaml-nox ocaml opam libffi-dev pkg-config m4 libgmp-dev cmake ninja-build libcurl4-openssl-dev python3 libunwind-dev libpython3-dev python3-pip libblas-dev liblapack-dev \
    && opam init --disable-sandboxing \
    && opam install -y zarith dune menhir openQASM ctypes ctypes-foreign ppx_deriving ctypes-zarith \
    && echo 'eval `opam config env`' >>~/.bashrc \
    && apt-get -y install gcc-8 g++-8 \
    && update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-8 50 \
    && update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-8 50 \
    # LLVM Syntax handler
    && git clone https://github.com/ornl-qci/llvm-project-csp llvm \
    && cd llvm && mkdir build && cd build \
    && cmake -G Ninja ../llvm -DCMAKE_INSTALL_PREFIX=$HOME/.llvm -DBUILD_SHARED_LIBS=TRUE -DCMAKE_BUILD_TYPE=Release -DLLVM_TARGETS_TO_BUILD="X86" -DLLVM_ENABLE_PROJECTS=clang \
    && cmake --build . --target install \
    && ln -sf $HOME/.llvm/bin/llvm-config /usr/bin/ && cd ../../ && rm -rf /llvm /var/lib/apt/lists/* \
    && cd ../../ \
    # XACC build
    && git clone --recursive https://github.com/eclipse/xacc && cd xacc && mkdir build && cd build \
    && cmake .. -G Ninja \
    && ninja install \
    && cd ../../ && git clone -b master https://github.com/ornl-qci/qcor && cd qcor && mkdir build && cd build \
    && cmake .. -DXACC_DIR=~/.xacc \
    && make -j$(nproc) install