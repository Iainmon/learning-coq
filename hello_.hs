module Hello where

import qualified Prelude

data Bool =
   True
 | False

orb :: Bool ->
       Bool ->
       Bool
orb b1 b2 =
  case b1 of {
   True -> True;
   False -> b2}

data Nat =
   O
 | S Nat

add :: Nat -> Nat
       -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S
    (add p m)}

mul :: Nat -> Nat
       -> Nat
mul n m =
  case n of {
   O -> O;
   S p ->
    add m
      (mul p m)}

add0 :: Nat -> Nat
        -> Nat
add0 n m =
  case n of {
   O -> m;
   S p -> S
    (add0 p m)}

eqb :: Nat -> Nat
       -> Bool
eqb n m =
  case n of {
   O ->
    case m of {
     O -> True;
     S _ -> False};
   S n' ->
    case m of {
     O -> False;
     S m' ->
      eqb n' m'}}

max :: Nat -> Nat
       -> Nat
max n m =
  case n of {
   O -> m;
   S n' ->
    case m of {
     O -> n;
     S m' -> S
      (max n' m')}}

add1 :: Nat -> Nat
        -> Nat
add1 =
  add0

data Tree a =
   Empty
 | Node (Tree a) 
 a (Tree a)

height :: 
  (Tree a1) -> Nat
height t =
  case t of {
   Empty -> O;
   Node l _ r -> S
    (max
      (height l)
      (height r))}

helper' :: 
  Nat -> Nat ->
  Nat -> Bool
helper' p m n =
  case m of {
   O -> False;
   S m' ->
    case m' of {
     O -> False;
     S _ ->
      case n of {
       O -> False;
       S n' ->
        case n' of {
         O ->
         False;
         S _ ->
         orb
         (eqb
         (mul m n)
         p)
         (helper'
         p m' n)}}}}

helper :: 
  Nat -> Nat ->
  Bool
helper p m =
  case m of {
   O -> False;
   S m' ->
    orb
      (eqb
        (mul m m)
        p)
      (orb
        (helper' p
         m' m)
        (helper p
         m'))}

