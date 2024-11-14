module Hello where

import qualified Prelude

data Bool =
   True
 | False

orb :: Bool -> Bool -> Bool
orb b1 b2 =
  case b1 of {
   True -> True;
   False -> b2}

my_add :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
my_add n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\n' -> (1+) (my_add n' m))
    n

helper' :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer -> Bool
helper' p m n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> False)
    (\m' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> False)
      (\_ ->
      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
        (\_ -> False)
        (\n' ->
        (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
          (\_ -> False)
          (\_ ->
          orb ((Prelude.==) ((Prelude.*) m n) p) (helper' p m' n))
          n')
        n)
      m')
    m

helper :: Prelude.Integer -> Prelude.Integer -> Bool
helper p m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> False)
    (\m' ->
    orb ((Prelude.==) ((Prelude.*) m m) p)
      (orb (helper' p m' m) (helper p m')))
    m

