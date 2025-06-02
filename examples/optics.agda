open import Prelude

open import Control.Lens
open import Data.List as List using ()
open import Data.String as String using ()
open import Data.Traversable
open import System.IO

_ : view #snd ("hello" , "world") === "world"
_ = refl

_ : ("hello" , "world") ^: #snd === "world"
_ = refl

_ : snd ("hello" , "world") === "world"
_ = refl

_ : preview (ix 1) ('a' :: 'b' :: 'c' :: []) === just 'b'
_ = refl

_ : ('a' :: 'b' :: 'c' :: []) ^? ix 1 === just 'b'
_ = refl

_ : ((1 :: 2 :: []) :: (3 :: []) :: []) ^:: traverse <<< traverse === (1 :: 2 :: 3 :: [])
_ = refl

record UserInfo : Type where
  field
    numLogins : Nat
    associatedIPs : List String

open UserInfo

#numLogins : Lens' UserInfo Nat
#numLogins = lens numLogins \ userinfo n -> record userinfo { numLogins = n }

#associatedIPs : Lens' UserInfo (List String)
#associatedIPs = lens associatedIPs \ userinfo ips -> record userinfo { associatedIPs = ips }

record User : Type where
  field
    name : String
    userid : Nat
    metadata : UserInfo

open User

#name : Lens' User String
#name = lens name \ user s -> record user { name = s }

#userid : Lens' User Nat
#userid = lens userid \ user id -> record user { userid = id }

#metadata : Lens' User UserInfo
#metadata = lens metadata \ user d -> record user { metadata = d }

user1 : User
user1 .name = "john.smith"
user1 .userid = 103
user1 .metadata .numLogins = 20
user1 .metadata .associatedIPs = "1.2.3.4" :: "5.6.7.8" :: []

user2 : User
user2 .name = "john.smith"
user2 .userid = 103
user2 .metadata .numLogins = 20
user2 .metadata .associatedIPs = "5.6.7.8" :: "1.2.3.4" :: []

_ : user1 ^: #name === user1 .name
_ = refl

_ : user1 ^: #metadata <<< #numLogins === 20
_ = refl

_ : (user1 & #metadata <<< #numLogins :~ 0) .metadata .numLogins === 0
_ = refl

_ : user1 ^: #metadata <<< #associatedIPs === user1 .metadata .associatedIPs
_ = refl

even : Nat -> Bool
even n = mod n 2 == 0

reversedEvens : List Nat
reversedEvens = 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: [] & partsOf (each <<< filtered even) %~ List.reverse

_ : reversedEvens === 1 :: 8 :: 3 :: 6 :: 5 :: 4 :: 7 :: 2 :: []
_ = refl

main : IO Unit
main = do
  print ((user1 & #metadata <<< #numLogins :~ 0) .metadata .numLogins)
  print ((user1 & #metadata <<< #numLogins %~ (_+ 1)) .metadata .numLogins)
  print ((user1 ^:: #metadata <<< #associatedIPs <<< each <<< to String.reverse))