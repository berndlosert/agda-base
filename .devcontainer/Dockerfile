FROM haskell:9.12.2

USER root
RUN apt-get update
RUN apt-get install -y cabal-install time

RUN cabal update
RUN cabal install alex
RUN cabal install happy
RUN cabal install Agda
RUN cabal install --lib text
RUN cabal install --lib ieee754
RUN cabal install --lib network
RUN cabal install --lib async

WORKDIR /root/
RUN mkdir /root/.agda
RUN echo "/workspaces/agda-base/base-library.agda-lib" >> /root/.agda/libraries
RUN echo "base-library" >> ~/.agda/defaults

RUN echo "stty -ixon" >> ~/.bashrc

RUN apt-get install -y vim
RUN echo "set ttimeoutlen=25" >> ~/.vimrc
RUN echo "set hidden" >> ~/.vimrc
RUN echo "set noswapfile" >> ~/.vimrc
RUN echo "syntax off" >> ~/.vimrc
RUN echo "export EDITOR=vim" >> ~/.bashrc

#may need to update the agda path in the general extensions settings in VS Code
ENTRYPOINT ["tail", "-f", "/dev/null"]
