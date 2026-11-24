# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A WIP "batteries-included" base library for Agda, modeled on GHC's `base` (plus ideas from hackage, agda-stdlib, agda-prelude, Idris). It is meant for programming rather than proving, and avoids Unicode-heavy syntax (ASCII operators like `->`, `<<<`, `===`, `::`). Do not use agda-stdlib; modules here replace it.

## Commands

There is no build system or test runner; everything is plain `agda`. The library is registered via `~/.agda/libraries` (pointing at `base-library.agda-lib`) and `~/.agda/defaults` (`base-library`).

- Typecheck a file: `agda path/to/File.agda`
- Compile an executable: `agda --compile examples/fizzbuzz.agda` (needs GHC; Haskell packages `ieee754`, `network`, `async` installed via `cabal install --lib`)
- "Tests": `agda tests/checks.agda` — tests are propositional equalities proven by `refl`, so typechecking the file *is* the test run.
- Examples use `examples/base-library-examples.agda-lib`; tests use `tests/base-library-tests.agda-lib`.

Build artifacts (`*.agdai`, `MAlonzo`) are gitignored.

## Flags

All `.agda-lib` files enable `--type-in-type` and `--guardedness`; the library and examples additionally use `--no-positivity-check`, `--no-termination-check` and `--no-import-sorts`. Code relies on these (e.g. `Type : Type`, non-positive/ non-terminating definitions), so don't "fix" such code to be sound. Files that are compiled standalone outside the lib (like the README hello world) need `{-# OPTIONS --guardedness #-}`.

## Architecture

- `src/Prelude.agda` is the core: one large module defining basic types (`Void`, `Unit`, `Nat`, `Nat1`, `Ordering`, ...; `Set` is renamed `Type`) and the fundamental typeclasses, re-exporting Agda builtins. Nearly every file starts with `open import Prelude`, so changes there affect everything. Typeclasses are implemented as records with instance arguments.
- `src/Control/` — Functor-adjacent abstractions: comonads, free monads (`Free`, `Free/Scoped`, `Free/Classic`), monad transformers (`Monad/*/Trans.agda`) with `Class.agda` (mtl-style classes) and `Signature.agda` (effect signatures for free-monad handlers) per effect, `Selective`, `Lens`, `Concurrent` (+ `Async`, `STM`), `Reduce`.
- `src/Data/` — data structures and instances (`Functor/*`, `Monoid/*` incl. `Monoid.Foldable`, `Enum`, `String`, `List`, `Float`, `Bytes`, ...).
- `src/System/`, `src/Network/` — IO and FFI to Haskell via `COMPILE GHC` pragmas (these are why the Haskell packages are needed to compile).
- `src/Test/QC` — QuickCheck-style property testing; `src/Properties/` — reusable law/property definitions (Eq, Functor, Monoid, Semigroup).
- `examples/` — runnable demo programs (each with a `main : IO Unit`), also serving as usage documentation.
- `src/Debug.agda`, `src/Reflection.agda` — misc utilities.

## Conventions

Follow the existing style: `import`s via `open import`, section banners (`-----` comment rules) in larger files, `->`/`<-` ASCII arrows, `do`-notation and idiom brackets (`(| f x y |)`) where appropriate.
