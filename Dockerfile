FROM ocaml/opam:ubuntu-22.04-ocaml-4.10

USER root
RUN apt-get update && apt-get install -y git python 3.9 python3.10 software-properties-common python3-pip
RUN add-apt-repository ppa:deadsnakes/ppa
RUN update-alternatives --install /usr/bin/python python /usr/bin/python3.10 1
ENV HOME /home/opam

WORKDIR ${HOME}

# Git clone Pyinder repo
RUN git clone https://github.com/kupl/Pyinder.git
RUN pip3 install --upgrade pip
RUN pip3 install GitPython
RUN (cd Pyinder ; pip3 install -r requirements.txt)

RUN pip3 install pyright==1.1.339 mypy==1.9.0 pytype==2024.4.11 numpy pandas

# Set up environemnt
RUN echo "alias pyinder='PYTHONPATH=${HOME}/Pyinder/..:\$PYTHONPATH python3 -m Pyinder.client.pyre'" >> /home/opam/.bashrc
RUN echo "export PYRE_BINARY=${HOME}/Pyinder/source/_build/default/main.exe" >> /home/opam/.bashrc

# Install opam packages
RUN opam init --disable-sandboxing
RUN opam install -y dune base64.3.5.0 core.v0.14.1 re2.v0.14.0 dune.2.9.1 yojson.1.7.0 ppx_deriving_yojson.3.6.1 ounit.2.2.4 menhir.20211230 lwt.5.5.0 ounit2-lwt.2.2.4 pyre-ast.0.1.8 mtime.1.3.0
RUN eval $(opam config env)

# Copy files
COPY configuration ${HOME}/configuration
COPY run ${HOME}/run
COPY run ${HOME}/eval

RUN chmod +x ${HOME}/run/run.sh
RUN chmod +x ${HOME}/run/run_pyright.sh
RUN chmod +x ${HOME}/run/run_mypy.sh
RUN chmod +x ${HOME}/run/run_pyre.sh
RUN chmod +x ${HOME}/run/run_pytype.sh

CMD ["/bin/bash"]
