-- https://kodimensional.dev/posts/2019-03-25-comonadic-builders

open import Prelude

open import Control.Comonad
open import Data.Monoid.Any
open import Data.String.Builder hiding (Builder)
open import Data.String.Show
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
  Show-Settings .show = showDefault
  Show-Settings .showsPrec prec (asSettings x y z) =
    "record { "
    <> "hasLibrary = "
    <> showsPrec prec x
    <> "; github = "
    <> showsPrec prec y
    <> "; travis = "
    <> showsPrec prec z
    <> " }"

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
  Show-Project .show = showDefault
  Show-Project .showsPrec prec (asProject w x y z) =
    "record { "
    <> "name = "
    <> showsPrec prec w
    <> "; hasLibrary = "
    <> showsPrec prec x
    <> "; github = "
    <> showsPrec prec y
    <> "; travis = "
    <> showsPrec prec z
    <> " }"

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
