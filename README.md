# WIP: Agda base library

This is an attempt at creating a base library for Agda. Unlike the agda-stdlib
library, which is designed with proving in mind, this library is meant to be a
general purpose "batteries-included" base library.

The design is mostly based on GHC's base library, but a lot of ideas were
"stolen" from PureScript too.

## How to install with `brew` (macOS Mojave)

```sh
# Install agda
brew install agda

# Set up the base library
mkdir ~/.agda
echo <path to base library>/base-library.agda-lib >> ~/.agda/libraries
echo base-library >> ~/.agda/defaults

# Needed to compile agda programs into executables
cabal update
cabal install --lib ieee754
```

N.B. `brew install agda` will install a couple of "unnecessary" things:
* the agda-stdlib (under /usr/local/lib/agda)
* emacs

To uninstall emacs, do the following:

```sh
# Uninstall emacs
brew uninstall emacs

# Uninstall emacs dependencies (brew really needs an option for this)
brew deps emacs | xargs -n 1 brew uninstall --ignore-dependencie

# Uninstall leftover files
rm -rf /usr/local/etc/unbound
rm -rf /usr/local/etc/gnutls
rm -rf /usr/local/etc/openssl@1.1
```

## Hello world!

Save the following code into a file called `hello.agda`.

```agda
open import Prelude
open import System.IO

main : IO Unit
main = print "Hello world!"
```

Compile it like so:

```
agda --compile hello.agda
```
