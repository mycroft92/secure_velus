# Reproducible Velus/SIF development environment.
#
# On Apple Silicon hosts, build and run this image as linux/amd64:
#   docker buildx build --platform linux/amd64 -t secure-velus-dev .
#   docker run --platform linux/amd64 -it --rm secure-velus-dev
#
# If you bind-mount a fresh checkout into /workspace, rerun:
#   ./configure -clightgen x86_64-linux
#
FROM --platform=linux/amd64 ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    ca-certificates \
    curl \
    git \
    libgmp-dev \
    m4 \
    make \
    menhir \
    opam \
    pkg-config \
    rsync \
    sudo \
    unzip \
    && rm -rf /var/lib/apt/lists/*

RUN useradd -m -s /bin/bash velus && \
    echo "velus ALL=(ALL) NOPASSWD:ALL" >> /etc/sudoers

USER velus
SHELL ["/bin/bash", "-lc"]

ENV OPAMROOT=/home/velus/.opam

RUN opam init --disable-sandboxing -a --bare && \
    opam switch create default \
      --repos=default,archive=git+https://github.com/ocaml/opam-repository-archive.git \
      --packages=ocaml-base-compiler.4.09.1

ENV PATH=/home/velus/.opam/default/bin:${PATH}

RUN opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam install -y \
      coq.8.9.1 \
      coq-menhirlib.20200624 \
      menhir.20200624 \
      ocamlbuild \
      ocamlfind && \
    opam clean -acrs

WORKDIR /workspace
COPY --chown=velus:velus . /workspace

# Populate CompCert submodule (public repo, pinned commit matches .gitmodules)
RUN git clone https://github.com/inria-parkas/CompCert.git CompCert && \
    git -C CompCert checkout e19f81cecf4a7cca67d8491fcb4c0a259c232bfb

# Generate the repository build files for the current toolchain.
RUN ./configure -clightgen x86_64-linux

# Entrypoint re-runs configure when /workspace is bind-mounted over the
# baked copy (the mount replaces CompCert with the host's submodule).
COPY --chown=velus:velus docker-entrypoint.sh /usr/local/bin/docker-entrypoint.sh
RUN chmod +x /usr/local/bin/docker-entrypoint.sh

ENTRYPOINT ["/usr/local/bin/docker-entrypoint.sh"]
CMD ["/bin/bash"]
