module Expt2 where

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

data Zero : Set where
record One : Set where constructor <>
open One
data Two : Set where tt ff : Two
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg
infixr 5 _,_

Ex : {S : Set}(T : S -> Set) -> Set
Ex = Sg _

_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 5 _*_

cond1 : {P : Two -> Set1} -> P tt -> P ff -> (b : Two) -> P b
cond1 t f tt = t
cond1 t f ff = f

_+_ : Set -> Set -> Set
S + T = Sg Two (cond1 S T)
infixr 4 _+_

cond0 : {P : Two -> Set0} -> P tt -> P ff -> (b : Two) -> P b
cond0 t f tt = t
cond0 t f ff = f

data Bif : Set where
  `Par `Rec `0 `1 : Bif
  _`+_ _`*_ : (S T : Bif) -> Bif

[_]B : Bif -> Set -> Set -> Set
[ `Par ]B X R = X
[ `Rec ]B X R = R
[ `0 ]B X R = Zero
[ `1 ]B X R = One
[ S `+ T ]B X R = [ S ]B X R + [ T ]B X R
[ S `* T ]B X R = [ S ]B X R * [ T ]B X R

data Ty : Set where
  `Par `0 `1 : Ty
  _`+_ _`*_ _`&_ _`-o_ : (S T : Ty) -> Ty
  `Mu : (B : Bif) -> Ty

_/_ : Bif -> Ty -> Ty
`Par / F = `Par
`Rec / F = F
`0 / F = `0
`1 / F = `1
(S `+ T) / F = (S / F) `+ (T / F)
(S `* T) / F = (S / F) `* (T / F)

data Mu (B : Bif)(X : Set) : Set where
  <_> : [ B ]B X (Mu B X) -> Mu B X

[_]T : Ty -> Set -> Set
[ `Par ]T X = X
[ `0 ]T X = Zero
[ `1 ]T X = One
[ S `+ T ]T X = [ S ]T X + [ T ]T X
[ S `* T ]T X = [ S ]T X * [ T ]T X
[ S `& T ]T X = [ S ]T X * [ T ]T X
[ S `-o T ]T X = [ S ]T X -> [ T ]T X
[ `Mu B ]T X = Mu B X

List : Set -> Set
List = Mu (`1 `+ (`Par `* `Rec))

nil : forall {X} -> List X
nil = < tt , <> >

cons : forall {X} -> X -> List X -> List X
cons x xs = < ff , x , xs >

data Splice {X : Set} : List X -> List X -> List X -> Set where
  <> : Splice nil nil nil
  left : forall {x xs ys zs} -> Splice xs ys zs -> Splice (cons x xs) ys (cons x zs)
  right : forall {x xs ys zs} -> Splice xs ys zs -> Splice xs (cons x ys) (cons x zs)

lefts : forall {X}{xs : List X} -> Splice xs nil xs
lefts {X}{< tt , <> >} = <>
lefts {X}{< ff , x , xs >} = left lefts

rights : forall {X}{xs : List X} -> Splice nil xs xs
rights {X}{< tt , <> >} = <>
rights {X}{< ff , x , xs >} = right rights

swap : forall {X}{xs ys zs : List X} -> Splice xs ys zs -> Splice ys xs zs
swap <> = <>
swap (left s) = right (swap s)
swap (right s) = left (swap s)

rassoc : forall {X}{as bs cs ds es : List X} -> Splice as bs ds -> Splice ds cs es ->
          Sg (List X) \ fs -> Splice bs cs fs * Splice as fs es
rassoc <> <> = _ , <> , <>
rassoc (left abd) (left dce) with rassoc abd dce
... | _ , bcf , afe = _ , bcf , left afe
rassoc (right abd) (left dce) with rassoc abd dce
... | _ , bcf , afe = _ , left bcf , right afe
rassoc abd (right dce) with rassoc abd dce
... | _ , bcf , afe = _ , right bcf , right afe

lassoc : forall {X}{as bs cs ds es : List X} -> Splice bs cs ds -> Splice as ds es ->
          Sg (List X) \ fs -> Splice as bs fs * Splice fs cs es
lassoc <> <> = _ , <> , <>
lassoc bcd (left ade) with lassoc bcd ade
... | _ , abf , fce = _ , left abf , left fce
lassoc (left bcd) (right ade) with lassoc bcd ade
... | _ , abf , fce = _ , right abf , left fce
lassoc (right bcd) (right ade) with lassoc bcd ade
... | _ , abf , fce = _ , abf , right fce


data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x

subst : {X : Set}{x y : X} -> x == y -> (P : X -> Set) -> P x -> P y
subst refl P p = p

unlefts : forall {X}{xs ys : List X} -> Splice xs nil ys -> xs == ys
unlefts <> = refl
unlefts (left s) with unlefts s
... | refl = refl

unrights : forall {X}{xs ys : List X} -> Splice nil xs ys -> xs == ys
unrights <> = refl
unrights (right s) with unrights s
... | refl = refl

mutual
  PerB : {X : Set}{R : Bif}(B : Bif) -> [ B ]B X (Mu R X) -> List X -> Set
  PerB `Par x xs = xs == cons x nil
  PerB `Rec t xs = PerMu t xs
  PerB `0 () xs
  PerB `1 t xs = xs == nil
  PerB (S `+ T) (tt , s) xs = PerB S s xs
  PerB (S `+ T) (ff , t) xs = PerB T t xs
  PerB (S `* T) (s , t) xs = Ex \ ys -> Ex \ zs -> Splice ys zs xs * PerB S s ys * PerB T t zs
  PerMu : {X : Set}{B : Bif} -> Mu B X -> List X -> Set
  PerMu {B = B} < t > xs = PerB B t xs

Perm : {X : Set}(T : Ty) -> [ T ]T X -> List X -> Set
Perm `Par x xs = xs == cons x nil
Perm `0 () xs
Perm `1 t xs = xs == nil
Perm (S `+ T) (tt , s) xs = Perm S s xs
Perm (S `+ T) (ff , t) xs = Perm T t xs
Perm (S `* T) (s , t) xs = Ex \ ys -> Ex \ zs -> Splice ys zs xs * Perm S s ys * Perm T t zs
Perm (S `& T) (s , t) xs = Perm S s xs * Perm T t xs
Perm (S `-o T) f xs = forall {ys zs s} -> Perm S s ys -> Splice xs ys zs -> Perm T (f s) zs
Perm (`Mu B) t xs = PerMu t xs

_~:_ : {X : Set}(T : Ty)(xs : List X) -> Set
_~:_ {X} T xs = Sg ([ T ]T X) \ t -> Perm T t xs

mutual
  prec : forall {B X T} ->
         [ (B / (`Mu B `& T)) `-o T ]T X ->
         [ `Mu B `-o T ]T X
  prec {B} f < b > = f (precs B f b)
  precs : forall B {R X T} ->
         [ (R / (`Mu R `& T)) `-o T ]T X ->
         [ B ]B X (Mu R X) -> [ B / (`Mu R `& T) ]T X
  precs `Par f x = x
  precs `Rec f b = b , prec f b
  precs `0 f ()
  precs `1 f b = <>
  precs (S `+ T) f (tt , s) = tt , precs S f s
  precs (S `+ T) f (ff , t) = ff , precs T f t
  precs (S `* T) f (s , t) = precs S f s , precs T f t

mutual
  precLem : forall {B X T}
            (f : [ (B / (`Mu B `& T)) `-o T ]T X) ->
            Perm ((B / (`Mu B `& T)) `-o T) f nil ->
            Perm (`Mu B `-o T) (prec f) nil
  precLem {B} f fh {ys}{zs}{< b >} bh yz with unrights yz
  precLem {B} f fh {ys}{.ys}{< b >} bh yz | refl = fh (precsLem B f fh b bh) rights

  precsLem : forall B {R X T} ->
             (f : [ (R / (`Mu R `& T)) `-o T ]T X) ->
             Perm ((R / (`Mu R `& T)) `-o T) f nil ->
             (b : [ B ]B X (Mu R X)) ->
             {ys : List X} -> PerB B b ys -> Perm (B / (`Mu R `& T)) (precs B f b) ys
  precsLem `Par f fh b bh = bh
  precsLem `Rec {R} f fh b bh = bh , precLem {R} f fh {s = b} bh rights
  precsLem `0 f fh () bh
  precsLem `1 f fh b bh = bh
  precsLem (S `+ T) f fh (tt , s) bh = precsLem S f fh s bh
  precsLem (S `+ T) f fh (ff , t) bh = precsLem T f fh t bh
  precsLem (S `* T) f fh (s , t) (sxs , txs , stys , sss , ttt)
    with precsLem S f fh s sss | precsLem T f fh t ttt
  ... | sss' | ttt'  = sxs , txs , stys , sss' , ttt'

gprec : forall {B X T} ->
        ((B / (`Mu B `& T)) `-o T) ~: nil {X} ->
        (`Mu B `-o T) ~: nil {X}
gprec (f , fh) = prec f , (\ {ys}{zs}{b} -> precLem f fh {ys}{zs}{b})

gcase : forall {S T U X}{xs : List X} ->
        (S `-o U) ~: xs -> (T `-o U) ~: xs ->
        ((S `+ T) `-o U) ~: xs
gcase (us , gus) (ut , gut) =
  (\ { (tt , s) -> us s ; (ff , t) -> ut t }) ,
  (\ { {ys}{zs}{tt , s} -> gus ; {ys}{zs}{ff , t} -> gut })

gsplit : forall {S T U X}{xs : List X} ->
        (S `-o (T `-o U)) ~: xs ->
        ((S `* T) `-o U) ~: xs
gsplit (ust , gust) = (\ { (s , t) -> ust s t }) ,
  (\ { {ys}{zs}{s , t}(_ , _ , ab , sa , tb) xyz ->
   let (_ , a' , b') = lassoc ab xyz in
     gust sa a' tb b'})

gleft : forall {S T U X}{xs : List X} ->
        (S `-o U) ~: xs ->
        ((S `& T) `-o U) ~: xs
gleft (us , gus) = (\ { (s , _) -> us s }) ,
  (\ { {ys}{zs}{s , _} (sh , _) -> gus sh})

gright : forall {S T U X}{xs : List X} ->
         (T `-o U) ~: xs ->
         ((S `& T) `-o U) ~: xs
gright (ut , gut) = (\ { (_ , t) -> ut t }) ,
  (\ { {ys}{zs}{_ , t} (_ , th) -> gut th})

gdrop : forall {U X}{xs : List X} ->
  U ~: xs -> (`1 `-o U) ~: xs
gdrop (u , gu) = (\ _ -> u) ,
  (\ { {.nil}{zs}{<>} refl xz -> subst (unlefts xz) _ gu})
