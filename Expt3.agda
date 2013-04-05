module Expt3 where

data Bif : Set where
  `P `R `1 : Bif
  _`+_ _`*_ : (S T : Bif) -> Bif

data Ty : Set where
  `Mu : (B : Bif) -> Ty
  `P `1 : Ty
  _`+_ _`*_ _`&_ _`-o_ : (S T : Ty) -> Ty

infixr 2 _`-o_

_/_ : Bif -> Ty -> Ty
`P / T = `P
`R / T = T
`1 / T = `1
(A `+ B) / T = (A / T) `+ (B / T)
(A `* B) / T = (A / T) `* (B / T)

data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

record _*_ (S T : Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T
open _*_

infixr 4 _,_

record One : Set where constructor <>

BIF : Bif -> Set -> Set -> Set
BIF `P P R = P
BIF `R P R = R
BIF `1 P R = One
BIF (S `+ T) P R = BIF S P R + BIF T P R
BIF (S `* T) P R = BIF S P R * BIF T P R

data Mu (B : Bif)(X : Set) : Set where
  <_> : BIF B X (Mu B X) -> Mu B X

TY : Ty -> Set -> Set
TY (`Mu B) X = Mu B X
TY `P X = X
TY `1 X = One
TY (S `+ T) X = TY S X + TY T X
TY (S `* T) X = TY S X * TY T X
TY (S `& T) X = TY S X * TY T X
TY (S `-o T) X = TY S X -> TY T X

data Two : Set where tt ff : Two

data Cx : Set where
  C0 : Cx
  _[_-_] : (G : Cx)(T : Ty)(b : Two) -> Cx

data _>=_ : Cx -> Cx -> Set where
  C0 : C0 >= C0
  _+q_ : forall {G G' b} -> G >= G' -> (T : Ty) -> (G [ T - b ]) >= (G' [ T - b ])
  _+k_ : forall {G G'} -> G >= G' -> (T : Ty) -> (G [ T - tt ]) >= (G' [ T - ff ])

infixl 4 _+q_ _+k_

urefl : forall {G} -> G >= G
urefl {C0} = C0
urefl {G [ T - b ]} = urefl +q T

utrans : forall {G G' G''} -> G >= G' -> G' >= G'' -> G >= G''
utrans C0 C0 = C0
utrans (u +q S) (v +q ._) = utrans u v +q S
utrans (u +k S) (v +q ._) = utrans u v +k S
utrans (u +q S) (v +k ._) = utrans u v +k S

data Va (T : Ty) : {G G' : Cx} -> .(G >= G') -> Set where
  ze : forall {G} -> Va T {G [ T - tt ]} (urefl +k T)
  su : forall {G G' S b}{u : G >= G'} -> Va T u -> Va T {G [ S - b ]} (u +q S)

data Tm {G : Cx} : Ty -> {G' : Cx} -> .(G >= G') -> Set where
  va  : forall {T G'}{u : G >= G'} -> (x : Va T u) -> Tm T u
  la  : forall {S T G'}{u : G >= G'} -> Tm T (u +k S) -> Tm (S `-o T) u
  _$_ : forall {S T G' G''}{u : G >= G'}{u' : G' >= G''} ->
        Tm (S `-o T) u -> Tm S u' -> Tm T (utrans u u')
  void : Tm `1 urefl
  dull : forall {T G' G''}{u : G >= G'}{u' : G' >= G''} ->
    Tm `1 u -> Tm T u' -> Tm T (utrans u u')
  _,_ : forall {S T G' G''}{u : G >= G'}{u' : G' >= G''} ->
    Tm S u -> Tm T u' -> Tm (S `* T) (utrans u u')
  spl : forall {S T U G' G''}{u : G >= G'}{u' : G' >= G''} ->
          Tm (S `* T) u ->
          Tm U (u' +k S +k T) ->
          Tm U (utrans u u')
  inl : forall {S T G'}{u : G >= G'} -> Tm S u -> Tm (S `+ T) u
  inr : forall {S T G'}{u : G >= G'} -> Tm T u -> Tm (S `+ T) u
  case : forall {S T U G' G''}{u : G >= G'}{u' : G' >= G''} -> Tm (S `+ T) u ->
          Tm U (u' +k S) ->
          Tm U (u' +k T) ->
          Tm U (utrans u u')
  _&_ : forall {S T G'}{u : G >= G'} -> Tm S u -> Tm T u -> Tm (S `& T) u
  outl : forall {S T G'}{u : G >= G'} -> Tm (S `& T) u -> Tm S u
  outr : forall {S T G'}{u : G >= G'} -> Tm (S `& T) u -> Tm T u
  <_> : forall {B G'}{u : G >= G'} -> Tm (B / `Mu B) u -> Tm (`Mu B) u
  prec : forall {B T} -> Tm ((B / (`Mu B `& T)) `-o T) (urefl {G}) -> Tm (`Mu B `-o T) urefl
  cmp : forall {G0 G1 G' T}{u0 : G >= G'}{u1 : G >= G0}{u : G >= G1} ->
          Tm `P u0 -> Tm `P u1 -> Tm T u -> Tm T u -> Tm T u

Env : Cx -> Set -> Set
Env C0 X = One
Env (G [ T - tt ]) X = Env G X * TY T X
Env (G [ T - ff ]) X = Env G X

spare : forall {G G' X} -> G >= G' -> Env G X -> Env G' X
spare C0 <> = <>
spare {G [ T - tt ]} (u +q ._) (g , s) = spare u g , s
spare {G [ T - ff ]} (u +q ._) g = spare u g
spare (u +k _) (g , _) = spare u g

! : {X : Set}{{x : X}} -> X
! {X} {{x}} = x

get : forall {G G' T X}{{u : G >= G'}} -> Va T u -> Env G X -> TY T X
get ze (g , t) = t
get {G = G [ S - tt ]} (su x) (g , s) = get x g
get {G = G [ S - ff ]} (su x) g = get x g

after : forall {G G' T X}{{u : G >= G'}} ->
        .(Tm T u) -> Env G X -> Env G' X
after {{u}} t g = spare u g

eval : forall {G G' T X}(u : G >= G') ->
       (X -> X -> Two) -> Env G X -> Tm T u -> TY T X
eval u c g (va x) = get x g
eval u c g (la t) = \ s -> eval (u +k _) c (g , s) t
eval u c g (f $ s) = eval ! c g f (eval ! c (after f g) s)
eval u c g void = <>
eval u c g (dull v t) = eval ! c (after v g) t
eval u c g (s , t) = eval ! c g s , eval ! c (after s g) t
eval u c g (spl p k) with eval ! c g p
... | (s , t) = eval (! +k _ +k _) c ((after p g , s) , t) k
eval u c g (inl s) = inl (eval u c g s)
eval u c g (inr t) = inr (eval u c g t)
eval u c g (case z ks kt) with eval ! c g z
... | inl s = eval (! +k _) c (after z g , s) ks
... | inr t = eval (! +k _) c (after z g , t) kt
eval u c g (s & t) = eval u c g s , eval u c g t
eval u c g (outl p) = fst (eval u c g p)
eval u c g (outr p) = snd (eval u c g p)
eval {T = `Mu B}{X} u c g < t > = < pack B (eval u c g t) > where
  pack : (B' : Bif) -> TY (B' / `Mu B) X -> BIF B' X (Mu B X)
  pack `P x = x
  pack `R r = r
  pack `1 <> = <>
  pack (S `+ T) (inl s) = inl (pack S s)
  pack (S `+ T) (inr t) = inr (pack T t)
  pack (S `* T) (s , t) = pack S s , pack T t
eval {T = `Mu B `-o T}{X} u c g (prec f) = pr where
  r : TY ((B / (`Mu B `& T)) `-o T) X
  r = eval u c g f
  pr : Mu B X → TY T X
  unpack : (B' : Bif) -> BIF B' X (Mu B X) -> TY (B' / (`Mu B `& T)) X
  pr < t > = r (unpack B t)
  unpack `P x = x
  unpack `R b = b , pr b
  unpack `1 <> = <>
  unpack (U `+ V) (inl u) = inl (unpack U u)
  unpack (U `+ V) (inr v) = inr (unpack V v)
  unpack (U `* V) (u , v) = unpack U u , unpack V v
eval u c g (cmp a b le ge) with c (eval ! c g a) (eval ! c g b)
... | tt = eval u c g le
... | ff = eval u c g ge

LIST : Bif
LIST = `1 `+ (`P `* `R)

insert : forall {G} -> Tm (`Mu LIST `-o `P `-o `Mu LIST) (urefl {G})
insert = prec (la {!la ?!})