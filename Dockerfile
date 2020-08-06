# See here for image contents: https://github.com/microsoft/vscode-dev-containers/tree/v0.131.0/containers/ubuntu/.devcontainer/base.Dockerfile
ARG VARIANT="focal"
FROM mcr.microsoft.com/vscode/devcontainers/base:0-${VARIANT}

# [Optional] Uncomment this section to install additional OS packages.
RUN apt-get update \
    && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y install --no-install-recommends ocaml-nox ocaml opam libffi-dev pkg-config m4 libgmp-dev \
    && opam init --disable-sandboxing \
    && opam install -y zarith dune menhir openQASM ctypes ctypes-foreign ppx_deriving ctypes-zarith