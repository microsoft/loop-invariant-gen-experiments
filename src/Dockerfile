FROM ubuntu:20.04

ENV TZ=Asia/Kolkata \
    DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
    && apt-get install -y build-essential \
    && apt-get install -y wget autoconf graphviz libgmp-dev pkg-config \
    && apt-get install -y libcairo2-dev libexpat1-dev libgtk-3-dev libgtksourceview-3.0-dev \
    && apt-get install -y opam \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

ARG USER_ID
ARG GROUP_ID

RUN addgroup --gid $GROUP_ID user
RUN useradd -ms /usr/bin/bash -l -u $USER_ID -g $GROUP_ID user 

RUN mkdir -p /home/user
RUN chown -R user:user /home/user
USER user

# Install Conda
ENV CONDA_DIR=/home/user/miniconda3
RUN mkdir -p $CONDA_DIR
RUN wget https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh -O $CONDA_DIR/miniconda.sh
RUN bash $CONDA_DIR/miniconda.sh -b -u -p $CONDA_DIR
RUN rm -f $CONDA_DIR/miniconda.sh
ENV PATH=$CONDA_DIR/bin:$PATH

# Install Conda packages
RUN conda install -c conda-forge python=3.11

# Install Opam packages
RUN opam init -y --disable-sandboxing --compiler 4.14.1
ENV OPAM_SWITCH_PREFIX=/home/user/.opam/4.14.1
ENV CAML_LD_LIBRARY_PATH=/home/user/.opam/4.14.1/lib/stublibs:/home/user/.opam/4.14.1/lib/ocaml/stublibs:/home/user/.opam/4.14.1/lib/ocaml  
ENV OCAML_TOPLEVEL_PATH=/home/user/.opam/4.14.1/lib/toplevel
ENV MANPATH=':/home/user/.opam/4.14.1/man'
ENV PATH=/home/user/.opam/4.14.1/bin:$PATH
RUN opam install -y frama-c alt-ergo

RUN mkdir /home/user/solvers
ENV PATH=$PATH:/home/user/solvers

RUN wget http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.6-x86_64-linux-opt -P /home/user/solvers
RUN mv /home/user/solvers/cvc4-1.6-x86_64-linux-opt /home/user/solvers/cvc4
RUN chmod +x /home/user/solvers/cvc4

RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.12.2/z3-4.12.2-x64-glibc-2.31.zip -P /home/user/solvers
RUN unzip /home/user/solvers/z3-4.12.2-x64-glibc-2.31.zip -d /home/user/solvers
ENV PATH=$PATH:/home/user/solvers/z3-4.12.2-x64-glibc-2.31/bin

RUN opam exec -- why3 config detect

COPY --chown=user:user . /home/user/src/
WORKDIR /home/user/src/

# Install Python packages
RUN pip install -r requirements.txt

# Build tree-sitter parser
RUN rm -rf tree_sitter_lib/vendor/tree-sitter-c
RUN git clone https://github.com/tree-sitter/tree-sitter-c.git tree_sitter_lib/vendor/tree-sitter-c
RUN python build_parser.py
