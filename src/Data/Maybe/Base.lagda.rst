***************
Data.Maybe.Base
***************
::

  {-# OPTIONS --type-in-type #-}

  module Data.Maybe.Base where

``Maybe X`` is used for representing optional values of ``X`` by adding an extra
``nothing`` value to ``X``::

  data Maybe (X : Set) : Set where
    nothing : Maybe X
    just : X → Maybe X

This tells the Agda compiler to compile ``Maybe`` above to Haskell's ``Maybe``::

  {-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}