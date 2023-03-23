open import Prelude

open import Control.Lens
open import System.IO

_ : view snd' ("hello" , "world") === "world"
_ = refl

_ : ("hello" , "world") ^: snd' === "world"
_ = refl

_ : snd ("hello" , "world") === "world"
_ = refl

_ : ('a' :: 'b' :: 'c' :: []) ^? ix 1 === just 'b'
_ = refl

record UserInfo : Set where
  field
    numLogins : Nat
    associatedIPs : List String

open UserInfo

numLogins' : Simple Lens UserInfo Nat
numLogins' = lens numLogins \ userinfo n -> record userinfo { numLogins = n }

associatedIPs' : Simple Lens UserInfo (List String)
associatedIPs' = lens associatedIPs \ userinfo ips -> record userinfo { associatedIPs = ips }

record User : Set where
  field
    name : String
    userid : Nat
    metadata : UserInfo

open User

name' : Simple Lens User String
name' = lens name \ user s -> record user { name = s }

userid' : Simple Lens User Nat
userid' = lens userid \ user id -> record user { userid = id }

metadata' : Simple Lens User UserInfo
metadata' = lens metadata \ user d -> record user { metadata = d }

user1 : User
user1 .name = "john.smith"
user1 .userid = 103
user1 .metadata .numLogins = 20
user1 .metadata .associatedIPs = "1.2.3.4" :: "5.6.7.8" :: []

_ : user1 ^: name' === user1 .name
_ = refl

_ : user1 ^: metadata' <<< numLogins' === 20
_ = refl

_ : (user1 # metadata' <<< numLogins' :~ 0) .metadata .numLogins === 0
_ = refl

main : IO Unit
main = do
  print $ (user1 # metadata' <<< numLogins' :~ 0) .metadata .numLogins
  print $ (user1 # metadata' <<< numLogins' %~ (_+ 1)) .metadata .numLogins