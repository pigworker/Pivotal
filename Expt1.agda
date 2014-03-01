module Expt1 where

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

Pi : (S : Set)(T : S -> Set) -> Set
Pi S T = (s : S) -> T s

Pi1 : (S : Set)(T : S -> Set1) -> Set1
Pi1 S T = (s : S) -> T s

cond1 : {P : Two -> Set1} -> P tt -> P ff -> Pi1 Two P
cond1 t f tt = t
cond1 t f ff = f

_+_ : Set -> Set -> Set
S + T = Sg Two (cond1 S T)
infixr 4 _+_

cond0 : {P : Two -> Set0} -> P tt -> P ff -> (b : Two) -> P b
cond0 t f tt = t
cond0 t f ff = f

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x

data U (I : Set) : Set where
  `Rec : (i : I) -> U I
  `0 : U I
  `1 : U I
  _`+_ : (S T : U I) -> U I
  _`^_ : (S T : U I) -> U I

infixr 5 _`^_
infixr 4 _`+_

[_]u : forall {I} -> U I -> Set -> (I -> Set) -> Set
[ `Rec i ]u X R = R i
[ `0 ]u X R = Zero
[ `1 ]u X R = One
[ S `+ T ]u X R = [ S ]u X R + [ T ]u X R
[ S `^ T ]u X R = X * [ S ]u X R * [ T ]u X R

data Muu {I : Set}(F : I -> U I)(X : Set)(i : I) : Set where
  <_> : [ F i ]u X (Muu F X) -> Muu F X i

LIST : One -> U One
LIST _ = `1  `+  `1 `^ `Rec <>

TREE : One -> U One
TREE _ = `1  `+  `Rec <> `^ `Rec <>

INTV : One -> U One
INTV _ = `1 `^ `1

TR23 : Nat -> U Nat
TR23 ze      = `1
TR23 (su n)  = `Rec n `^ (`Rec n  `+ `Rec n `^ `Rec n)

data TB (X : Set) : Set where
  bot top : TB X
  # : (x : X) -> TB X

#[_] : {X : Set} -> (X -> X -> Set) -> TB X -> TB X -> Set
#[ R ] bot u = One
#[ R ] _ bot = Zero
#[ R ] _ top = One
#[ R ] top u = Zero
#[ R ] (# l) (# u) = R l u

[_]o : forall {I X} -> U I -> (X -> X -> Set) ->
         (I -> TB X -> TB X -> Set) -> TB X -> TB X -> Set
[ `Rec i ]o  L R l u = R i l u
[ `0 ]o      L R l u = Zero
[ `1 ]o      L R l u = #[ L ] l u
[ S `+ T ]o  L R l u = [ S ]o L R l u + [ T ]o L R l u
[ S `^ T ]o  L R l u = Ex \ x -> [ S ]o L R l (# x) * [ T ]o L R  (# x) u

! : {X : Set}{{_ : X}} -> X
! {X}{{x}} = x

data Muo {I X : Set}(F : I -> U I)(L : X -> X -> Set)
         (i : I)(l u : TB X) : Set where
  <_> : [ F i ]o L (Muo F L) l u -> Muo F L i l u

data Der (I X : Set) : Set1 where
  ll : (TB X -> TB X -> Set) -> Der I X
  rr : (I -> TB X -> TB X -> Set) -> Der I X

[_]d1 : forall {I X} -> U I -> (X -> X -> Set) ->
         (I -> U I) -> (TB X -> TB X -> Set) -> TB X -> TB X -> Set
[ `Rec i ]d1  L F H l u = Zero
[ `0 ]d1      L F H l u = Zero
[ `1 ]d1      L F H l u = #[ L ] l u * H l u
[ S `+ T ]d1  L F H l u = [ S ]d1 L F H l u + [ T ]d1 L F H l u
[ S `^ T ]d1  L F H l u = Ex \ x ->
  [ S ]d1 L F H l (# x) * [ T ]o L (Muo F L)  (# x) u   +
  [ S ]o L (Muo F L) l (# x) * [ T ]d1 L F H (# x) u

[_]dr : forall {I X} -> U I -> (X -> X -> Set) ->
         (I -> U I) -> (I -> TB X -> TB X -> Set) -> TB X -> TB X -> Set
[ `Rec i ]dr  L F H l u = H i l u
[ `0 ]dr      L F H l u = Zero
[ `1 ]dr      L F H l u = Zero
[ S `+ T ]dr  L F H l u = [ S ]dr L F H l u + [ T ]dr L F H l u
[ S `^ T ]dr  L F H l u = Ex \ x ->
  [ S ]dr L F H l (# x) * [ T ]o L (Muo F L)  (# x) u   +
  [ S ]o L (Muo F L) l (# x) * [ T ]dr L F H (# x) u

data Muz {I X : Set}(F : I -> U I)(L : X -> X -> Set)
         (H : TB X -> TB X -> Set)(i : I)(l u : TB X) : Set where
  <_> : [ F i ]dr L F (Muz F L H) l u -> Muz F L H i l u
  ><_>< : [ F i ]d1 L F H l u -> Muz F L H i l u

plug :  forall {I X F}{L : X -> X -> Set}{H}{i : I}{l u} ->
        Muz F L H i l u -> Muo F L i l u
plug {I}{X}{F}{L}{H}{i} < x > = < plugr (F i) x > where
  plugr : forall G {l u} -> [ G ]dr L F (Muz F L H) l u -> [ G ]o L (Muo F L) l u
  plugr (`Rec i) d = plug d
  plugr `0 ()
  plugr `1 ()
  plugr (S `+ T) (tt , d) = tt , plugr S d
  plugr (S `+ T) (ff , d) = ff , plugr T d
  plugr (S `^ T) (p , tt , d , t) = p , plugr S d , t
  plugr (S `^ T) (p , ff , s , d) = p , s , plugr T d
plug {I}{X}{F}{L}{H}{i} >< x >< = < plug1 (F i) x > where
  plug1 : forall G {l u} -> [ G ]d1 L F H l u -> [ G ]o L (Muo F L) l u
  plug1 (`Rec i) ()
  plug1 `0 ()
  plug1 `1 (l , _) = l
  plug1 (S `+ T) (tt , d) = tt , plug1 S d
  plug1 (S `+ T) (ff , d) = ff , plug1 T d
  plug1 (S `^ T) (p , tt , d , t) = p , plug1 S d , t
  plug1 (S `^ T) (p , ff , s , d) = p , s , plug1 T d

In : forall {X}(L : X -> X -> Set)(x : X)(l u : TB X) -> Set
In L x l u = #[ L ] l (# x) * #[ L ] (# x) u

data Find {I X F}{L : X -> X -> Set}{i : I}{l u}(x : X) : Muo F L i l u -> Set where
  found : (d : Muz F L (In L x) i l u) ->
           Find x (plug d)

{-
find : forall {I X F}{L : X -> X -> Set}{i : I}{l u}(x : X) ->
       In L x l u -> (t : Muo F L i l u) -> Find x t
find {I}{X}{F}{L}{i} x lxu < t > = {!!}
  help : forall G {l u} -> In L x l u ->
         (t : [ G ]o L (Muo F L) l u) ->
           (Sg ([ G ]d1 L (Muo F L) (In L X)) \ d -> t == plug
-}


Leaf : forall {I X} -> U I -> (X -> X -> Set) ->
         (I -> TB X -> TB X -> Set) -> (TB X -> TB X -> Set) ->
         TB X -> TB X -> Set
Leaf (`Rec i)  L R F l u = Zero
Leaf `0        L R F l u = Zero
Leaf `1        L R F l u = #[ L ] l u * F l u
Leaf (S `+ T)  L R F l u = Leaf S L R F l u + Leaf T L R F l u
Leaf (S `^ T)  L R F l u = Ex \ x ->
  Leaf S L R F l (# x) * [ T ]o L R  (# x) u +
  [ S ]o L R l (# x) * Leaf T L R F (# x) u

mkLeaf : forall {I X}(T : U I)(L : X -> X -> Set)
         (R : I -> TB X -> TB X -> Set)(F : TB X -> TB X -> Set) ->
         (l u : TB X) ->
         Leaf T L R F l u -> [ T ]o L R l u
mkLeaf (`Rec i) L R F l u ()
mkLeaf `0 L R F l u ()
mkLeaf `1 L R F l u (fst , snd) = fst
mkLeaf (S `+ T) L R F l u (tt , s) = tt , mkLeaf S L R F l u s
mkLeaf (S `+ T) L R F l u (ff , t) = ff , mkLeaf T L R F l u t
mkLeaf (S `^ T) L R F l u (p , tt , s , t) = p , mkLeaf S L R F _ _ s , t
mkLeaf (S `^ T) L R F l u (p , ff , s , t) = p , s , mkLeaf T L R F _ _ t

intv : forall {X}{L : X -> X -> Set}{l u} -> Muo INTV L <> l u -> X
intv < x , _ , _ > = x

mutual
  flattenk : forall {I X}{F : I -> U I}{L : X -> X -> Set}{i l u v} ->
            Muo F L i l u ->
            (forall {t} -> #[ L ] t u -> Muo LIST L <> t v) -> Muo LIST L <> l v
  flattenk {F = F}{i = i} < lu > k = flattenks (F i) lu k

  flattenks : forall {I X}{F : I -> U I}{L : X -> X -> Set}{l u v}
           (T : U I) -> [ T ]o L (Muo F L) l u -> 
           (forall {t} -> #[ L ] t u -> Muo LIST L <> t v) -> Muo LIST L <> l v
  flattenks (`Rec i) lu k = flattenk lu k
  flattenks `0 () k
  flattenks `1 _ k = k !
  flattenks (S `+ T) (tt , lu) k = flattenks S lu k
  flattenks (S `+ T) (ff , lu) k = flattenks T lu k
  flattenks (S `^ T) (x , lx , xu) k =
    flattenks S lx \ tx -> < ff , x , tx , flattenks T xu k >

flatten : forall {I X}{F : I -> U I}{L : X -> X -> Set}{i l u} ->
           Muo F L i l u -> Muo LIST L <> l u
flatten t = flattenk t \ tu -> < tt , tu >

data OWOTO {X : Set}(L : X -> X -> Set)(x y : X) : Set where
  le : {{_ : L x y}} -> OWOTO L x y
  ge : {{_ : L y x}} -> OWOTO L x y

Owoto : forall {X}(L : X -> X -> Set) -> Set
Owoto {X} L = (x y : X) -> OWOTO L x y

merge : forall {X}{L : X -> X -> Set}{l u} -> Owoto L
        -> Muo LIST L <> l u -> Muo LIST L <> l u -> Muo LIST L <> l u
merge ow < tt , _ > lu = lu
merge {L = L}{u = u} ow < ff , x , _ , xu > lu = help ! lu where
  help : forall {l} -> #[ L ] l (# x) -> Muo LIST L <> l u -> Muo LIST L <> l u
  help _ < tt , _ > = < ff , x , ! , xu >
  help _ < ff , y , _ , yu > with ow x y
  ... | le = < ff , x , ! , merge ow xu < ff , y , ! , yu > >
  ... | ge = < ff , y , ! , help ! yu >

insertList : forall {X}{L : X -> X -> Set}{l u} -> Owoto L
        -> Muo INTV L <> l u -> Muo LIST L <> l u -> Muo LIST L <> l u
insertList ow lu lu' = merge ow (flatten lu) lu'


isort : forall {X}{L : X -> X -> Set} -> Owoto L -> 
        Muu LIST X <> -> Muo LIST L <> bot top
isort ow < tt , _ >           = < tt , _ >
isort ow < ff , x , _ , xs >  = insertList ow < x , _ , _ > (isort ow xs)

insertTree : forall {X : Set}{L : X -> X -> Set}{l u} -> Owoto L
        -> Muo INTV L <> l u -> Muo TREE L <> l u -> Muo TREE L <> l u
insertTree ow < x , _ , _ > < tt , _ > = < ff , x , < tt , ! > , < tt , ! > >
insertTree ow < x , _ , _ > < ff , y , ly , yu > with ow x y
... | le = < ff , y , insertTree ow < x , ! , ! > ly , yu >
... | ge = < ff , y , ly , insertTree ow < x , ! , ! > yu >

makeTree : forall {X}{L : X -> X -> Set} -> Owoto L
           -> Muu LIST X <> -> Muo TREE L <> bot top
makeTree ow < tt , _ >           = < tt , _ >
makeTree ow < ff , x , _ , xs >  = insertTree ow < x , _ , _ > (makeTree ow xs)

treeSort : forall {X}{L : X -> X -> Set} -> Owoto L -> 
        Muu LIST X <> -> Muo LIST L <> bot top
treeSort ow xs = flatten (makeTree ow xs)

data LTree (X : Set) : Set where
  none : LTree X
  leaf : X -> LTree X
  node : LTree X -> LTree X -> LTree X

twistin : forall {X} -> X -> LTree X -> LTree X
twistin x none = leaf x
twistin x (leaf y) = node (leaf x) (leaf y)
twistin x (node l r) = node (twistin x r) l

deal : forall {X} -> Muu LIST X <> -> LTree X
deal < tt , _ > = none
deal < ff , x , _ , xs > = twistin x (deal xs)

mtree : forall {X}{L : X -> X -> Set} -> Owoto L -> 
        LTree X -> Muo LIST L <> bot top
mtree ow none = < tt , ! >
mtree ow (leaf x) = < ff , x , ! , < tt , ! > >
mtree ow (node l r) = merge ow (mtree ow l) (mtree ow r)

msort : forall {X}{L : X -> X -> Set} -> Owoto L -> 
        Muu LIST X <> -> Muo LIST L <> bot top
msort ow xs = mtree ow (deal xs)

insert23 : forall {X : Set}{L : X -> X -> Set} -> Owoto L -> forall {l u}(n : Nat) ->
           Muo INTV L <> l u -> Muo TR23 L n l u ->
           Muo TR23 L n l u +
           Sg X \ x -> Muo TR23 L n l (# x) * Muo TR23 L n (# x) u
insert23 ow ze < x , _ , _ > < lu > = ff , x , < ! > , < ! >
insert23 ow (su n) < x , _ , _ > < y , ly , yu > with ow x y
insert23 ow (su n) < x , _ , _ > < y , ly , yu >
  | le with insert23 ow n < x , ! , ! > ly
insert23 ow (su n) < x , _ , _ > < y , ly , yu >
  | le | tt , ly' = tt , < y , ly' , yu >
insert23 ow (su n) < x , _ , _ > < y , ly , tt , yu >
  | le | ff , z , lz , zy = tt , < z , lz , ff , y , zy , yu >
insert23 ow (su n) < x , _ , _ > < y , ly , ff , z , yz , zu >
  | le | ff , w , lw , wy
  = ff , y , < w , lw , tt , wy > , < z , yz , tt , zu >
insert23 ow (su n) < x , _ , _ > < y , ly , tt , yu >
  | ge with insert23 ow n < x , ! , ! > yu
insert23 ow (su n) < x , _ , _ > < y , ly , tt , yu >
  | ge | tt , yu' = tt , < y , ly , tt , yu' >
insert23 ow (su n) < x , _ , _ > < y , ly , tt , yu >
  | ge | ff , z , yz , zu = tt , < y , ly , ff , z , yz , zu >
insert23 ow (su n) < x , _ , _ > < y , ly , ff , z , yz , zu >
  | ge with ow x z
insert23 ow (su n) < x , _ , _ > < y , ly , ff , z , yz , zu >
  | ge | le with insert23 ow n < x , ! , ! > yz
insert23 ow (su n) < x , _ , _ > < y , ly , ff , z , yz , zu >
  | ge | le | tt , yz' = tt , < y , ly , ff , z , yz' , zu >
insert23 ow (su n) < x , _ , _ > < y , ly , ff , z , yz , zu >
  | ge | le | ff , w , yw , wz
  = ff , w , < y , ly , tt , yw > , < z , wz , tt , zu >
insert23 ow (su n) < x , _ , _ > < y , ly , ff , z , yz , zu >
  | ge | ge with insert23 ow n < x , ! , ! > zu
insert23 ow (su n) < x , _ , _ > < y , ly , ff , z , yz , zu >
  | ge | ge | tt , zu' = tt , < y , ly , ff , z , yz , zu' >
insert23 ow (su n) < x , _ , _ > < y , ly , ff , z , yz , zu >
  | ge | ge | ff , w , zw , wu
  = ff , z , < y , ly , tt , yz > , < w , zw , tt , wu >

make23 : forall {X}{L : X -> X -> Set} -> Owoto L ->
         Muu LIST X <> -> Sg Nat \ n -> Muo TR23 L n bot top
make23 ow < tt , <> > = ze , < <> >
make23 ow < ff , x , <> , xs > with make23 ow xs
... | n , t with insert23 ow n < x , <> , <> > t
... | tt , t' = n , t'
... | ff , y , by , yt = su n , < y , by , tt , yt >

sort23 : forall {X}{L : X -> X -> Set} -> Owoto L -> 
         Muu LIST X <> -> Muo LIST L <> bot top
sort23 ow xs = flatten (snd (make23 ow xs))
