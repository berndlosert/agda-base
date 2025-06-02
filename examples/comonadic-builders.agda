-- https://kodimensional.dev/posts/2019-03-25-comonadic-builders

open import Prelude

open import Control.Comonad
open import Data.Monoid.Any
open import Data.String.Builder hiding (Builder)
open import Data.String.Show
open import System.IO

record Settings : Type where
  constructor settings
  field
    hasLibrary : Any
    github : Any
    travis : Any

open Settings

record Project : Type where
  constructor project
  field
    name : String
    hasLibrary : Bool
    github : Bool
    travis : Bool

open Project

instance
  Show-Settings : Show Settings
  Show-Settings .show = showDefault
  Show-Settings .showsPrec prec (settings x y z) =
    "record { "
    <> "hasLibrary = "
    <> showsPrec prec x
    <> "; github = "
    <> showsPrec prec y
    <> "; travis = "
    <> showsPrec prec z
    <> " }"

  Semigroup-Settings : Semigroup Settings
  Semigroup-Settings ._<>_ s t = \ where
    .hasLibrary -> hasLibrary s <> hasLibrary t
    .github -> github s <> github t
    .travis -> travis s <> travis t

  Monoid-Settings : Monoid Settings
  Monoid-Settings .mempty = \ where
    .hasLibrary -> asAny false
    .github -> asAny false
    .travis -> asAny false

  Show-Project : Show Project
  Show-Project .show = showDefault
  Show-Project .showsPrec prec (project w x y z) =
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

Builder : Type
Builder = Settings -> Project

build : String -> Builder
build projectName s = \ where
  .name -> projectName
  .hasLibrary -> getAny (s .hasLibrary)
  .github -> getAny (s .github)
  .travis -> getAny (s .travis)

hasLibraryBuilder : Builder -> Project
hasLibraryBuilder builder = builder (record mempty { hasLibrary = asAny true })

githubBuilder : Builder -> Project
githubBuilder builder = builder (record mempty { github = asAny true })

travisBuilder : Builder -> Project
travisBuilder builder =
  let project = extract builder
  in record project { travis = project .github }

main : IO Unit
main = print (extract (build "travis-github" =>> travisBuilder =>> githubBuilder))
