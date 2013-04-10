module Bal where

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

double : Nat -> Nat
double ze = ze
double (su n) = su (su (double n))

data Tree (X : Set) : Nat -> Set where
  ze : Tree X ze
  un : X -> Tree X (su ze)
  even : {n : Nat} -> Tree X (su n) -> Tree X (su n) -> Tree X (double (su n))
  odd : {n : Nat} -> Tree X (su n) -> Tree X n -> Tree X (su (double n))

insert : forall {X n} -> X -> Tree X n -> Tree X (su n)
insert x ze = un x
insert x (un y) = even (un x) (un y)
insert x (even l r) = odd (insert x l) r
insert x (odd l r) = even l (insert x r)

data Su (X : Set) : Set where
  ze : Su X
  <_> : X -> Su X

data Bin : Set where
  _b1 : Su Bin -> Bin
  _b0 : Bin -> Bin

bsuc : Su Bin -> Bin
bsuc ze = ze b1
bsuc < x b1 > = (bsuc x) b0
bsuc < x b0 > = < x > b1

record One : Set where constructor <>
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg
infixr 5 _,_

TF : Set -> (Su Bin -> Set) -> Su Bin -> Set
TF X R ze = One
TF X R < ze b1 > = X
TF X R < < b > b1 > = Sg (R < bsuc < b > > ) \ _ -> R < b >
TF X R < b b0 > = Sg (R < b >) \ _ -> R < b >

data Tr (X : Set)(b : Su Bin) : Set where
  <_> : TF X (Tr X) b -> Tr X b

ins : forall {X}(b : Su Bin) -> X -> Tr X b -> Tr X < bsuc b >
ins ze x t = < x >
ins < ze b1 > x < y >         = < < y > , < x > >
ins < < b > b1 > x < l , r >  = < l , ins < b > x r >
ins < b b0 > x < l , r >      = < ins < b > x l , r >
