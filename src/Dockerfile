FROM ubuntu:20.04

ENV TZ=Asia/Kolkata \
    DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
    && apt-get install -y build-essential \
    && apt-get install -y wget autoconf graphviz libgmp-dev pkg-config \
    && apt-get install -y libcairo2-dev libexpat1-dev libgtk-3-dev libgtksourceview-3.0-dev \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

ENV CONDA_DIR=/home/miniconda3

RUN mkdir -p $CONDA_DIR
RUN wget https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh -O $CONDA_DIR/miniconda.sh
RUN bash $CONDA_DIR/miniconda.sh -b -u -p $CONDA_DIR
RUN rm -rf $CONDA_DIR/miniconda.sh

ENV PATH=$CONDA_DIR/bin:$PATH

RUN conda install -c conda-forge python=3.11

RUN apt-get update && apt-get install -y opam \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*
RUN opam init -y --disable-sandboxing --compiler 4.14.1
RUN "eval $(opam env)"
RUN opam install -y frama-c alt-ergo

RUN mkdir ~/solvers
ENV PATH=$PATH:~/solvers

RUN wget http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.6-x86_64-linux-opt -P ~/solvers
RUN mv ~/solvers/cvc4-1.6-x86_64-linux-opt ~/solvers/cvc4

RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.12.2/z3-4.12.2-x64-glibc-2.31.zip -P ~/solvers
RUN unzip ~/solvers/z3-4.12.2-x64-glibc-2.31.zip -d ~/solvers
ENV PATH=$PATH:~/solvers/z3-4.12.2-x64-glibc-2.31/bin

RUN opam exec -- why3 config detect

RUN pip install -r requirements.txt

COPY . /home/src/

RUN git clone https://github.com/tree-sitter/tree-sitter-c.git src/tree_sitter_lib/vendor/tree-sitter-c

WORKDIR /home/src/

RUN python build_parser.py
