-- https://kodimensional.dev/posts/2019-03-25-comonadic-builders

open import Prelude

open import Control.Comonad
open import Data.Monoid.Any
open import System.IO

record Settings : Set where
  constructor asSettings
  field
    hasLibrary : Any
    github : Any
    travis : Any

open Settings

record Project : Set where
  constructor asProject
  field
    name : String
    hasLibrary : Bool
    github : Bool
    travis : Bool

open Project

instance
  Show-Settings : Show Settings
  Show-Settings .showsPrec prec (asSettings x y z) =
    showString "record { "
    <> showString "hasLibrary = "
    <> showsPrec prec x
    <> showString "; github = "
    <> showsPrec prec y
    <> showString "; travis = "
    <> showsPrec prec z
    <> showString " }"

  Semigroup-Settings : Semigroup Settings
  Semigroup-Settings ._<>_ s s' = \ where
    .hasLibrary -> hasLibrary s <> hasLibrary s'
    .github -> github s <> github s'
    .travis -> travis s <> travis s'

  Monoid-Settings : Monoid Settings
  Monoid-Settings .mempty = \ where
    .hasLibrary -> asAny false
    .github -> asAny false
    .travis -> asAny false

  Show-Project : Show Project
  Show-Project .showsPrec prec (asProject w x y z) =
    showString "record { "
    <> showString "name = "
    <> showsPrec prec w
    <> showString "; hasLibrary = "
    <> showsPrec prec x
    <> showString "; github = "
    <> showsPrec prec y
    <> showString "; travis = "
    <> showsPrec prec z
    <> showString " }"

Builder : Set
Builder = Settings -> Project

build : String -> Builder
build projectName settings = \ where
  .name -> projectName
  .hasLibrary -> getAny (settings .hasLibrary)
  .github -> getAny (settings .github)
  .travis -> getAny (settings .travis)

hasLibraryBuilder : Builder -> Project
hasLibraryBuilder builder = builder $ record mempty { hasLibrary = asAny true }

githubBuilder : Builder -> Project
githubBuilder builder = builder $ record mempty { github = asAny true }

travisBuilder : Builder -> Project
travisBuilder builder =
  let project = extract builder
  in record project { travis = project .github }

main : IO Unit
main = print $ extract $ build "travis-github" =>> travisBuilder =>> githubBuilder
