open import Prelude

open import Control.Lens

_ : view $snd ("hello" , "world") === "world"
_ = refl

_ : ("hello" , "world") ^# $snd === "world"
_ = refl

_ : snd ("hello" , "world") === "world"
_ = refl

_ : ('a' :: 'b' :: 'c' :: []) ^? ix 1 === just 'b'
_ = refl