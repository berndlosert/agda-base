FROM gitpod/workspace-full

# Install custom tools, runtime, etc.
RUN brew install agda; brew uninstall --ignore-dependencies emacs; brew deps emacs | xargs -n 1 brew uninstall --ignore-dependencies; \
  rm -rf /home/linuxbrew/.linuxbrew/etc/unbound; \
  rm -rf /home/linuxbrew/.linuxbrew/etc/gnutls; \
  rm -rf /home/linuxbrew/.linuxbrew/etc/openssl@1.1; \
  rm -rf /home/linuxbrew/.linuxbrew/etc/ca-certificates; \
  rm -rf /home/linuxbrew/.linuxbrew/share/emacs/site-lisp/agda; \
  cabal update; cabal install --lib ieee754; cabal install --lib network; \
  mkdir ~/.agda; \
  echo /workspace/agda-base/base-library.agda-lib >> ~/.agda/libraries; \
  echo base-library >> ~/.agda/defaults \
  sed -i -e 's/gcc-5/gcc-9/g' $(ghc --print-libdir)/settings
