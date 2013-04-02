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

cond1 : {P : Two -> Set1} -> P tt -> P ff -> (b : Two) -> P b
cond1 t f tt = t
cond1 t f ff = f

_+_ : Set -> Set -> Set
S + T = Sg Two (cond1 S T)
infixr 4 _+_

cond0 : {P : Two -> Set0} -> P tt -> P ff -> (b : Two) -> P b
cond0 t f tt = t
cond0 t f ff = f


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
TR23 (su n)  = `Rec n `^ `Rec n  `+  `Rec n `^ `Rec n `^ `Rec n

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

data Muo {I X : Set}(F : I -> U I)(L : X -> X -> Set)
         (i : I)(l u : TB X) : Set where
  <_> : [ F i ]o L (Muo F L) l u -> Muo F L i l u

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
  flattenks `1 lu k = k lu
  flattenks (S `+ T) (tt , lu) k = flattenks S lu k
  flattenks (S `+ T) (ff , lu) k = flattenks T lu k
  flattenks (S `^ T) (x , lx , xu) k =
    flattenks S lx \ tx -> < ff , x , tx , flattenks T xu k >

flatten : forall {I X}{F : I -> U I}{L : X -> X -> Set}{i l u} ->
           Muo F L i l u -> Muo LIST L <> l u
flatten t = flattenk t \ tu -> < tt , tu >

OWOTO : forall {X}(L : X -> X -> Set) -> Set
OWOTO {X} L = (l u : X) -> Sg Two (cond1 (L l u) (L u l))

merge : forall {X}{L : X -> X -> Set}{l u} -> OWOTO L
        -> Muo LIST L <> l u -> Muo LIST L <> l u -> Muo LIST L <> l u
merge ow < tt , _ > lu = lu
merge {L = L}{u = u} ow < ff , x , lx , xu > lu = help lx lu where
  help : forall {l} -> #[ L ] l (# x) -> Muo LIST L <> l u -> Muo LIST L <> l u
  help lx < tt , lu > = < ff , x , lx , xu >
  help lx < ff , y , ly , yu > with ow x y
  ... | tt , xy = < ff , x , lx , merge ow xu < ff , y , xy , yu > >
  ... | ff , yx = < ff , y , ly , help yx yu >

insertList : forall {X}{L : X -> X -> Set}{l u} -> OWOTO L
        -> Muo INTV L <> l u -> Muo LIST L <> l u -> Muo LIST L <> l u
insertList ow lu lu' = merge ow (flatten lu) lu'


isort : forall {X}{L : X -> X -> Set} -> OWOTO L -> 
        Muu LIST X <> -> Muo LIST L <> bot top
isort ow < tt , <> > = < tt , <> >
isort ow < ff , x , <> , xs > = insertList ow < x , <> , <> > (isort ow xs)

insertTree : forall {X}{L : X -> X -> Set}{l u} -> OWOTO L
        -> Muo INTV L <> l u -> Muo TREE L <> l u -> Muo TREE L <> l u
insertTree ow < x , lx , xu > < tt , lu > =
  < ff , x , < tt , lx > , < tt , xu > >
insertTree ow < x , lx , xu > < ff , y , ly , yu > with ow x y
... | tt , xy = < ff , y , insertTree ow < x , lx , xy > ly , yu >
... | ff , yx = < ff , y , ly , insertTree ow < x , yx , xu > yu >

makeTree : forall {X}{L : X -> X -> Set} -> OWOTO L
           -> Muu LIST X <> -> Muo TREE L <> bot top
makeTree ow < tt , <> > = < tt , <> >
makeTree ow < ff , x , <> , xs > =
  insertTree ow < x , <> , <> > (makeTree ow xs)

treeSort : forall {X}{L : X -> X -> Set} -> OWOTO L -> 
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
deal < tt , <> > = none
deal < ff , x , <> , xs > = twistin x (deal xs)

mtree : forall {X}{L : X -> X -> Set} -> OWOTO L -> 
        LTree X -> Muo LIST L <> bot top
mtree ow none = < tt , <> >
mtree ow (leaf x) = < ff , x , <> , < tt , <> > >
mtree ow (node l r) = merge ow (mtree ow l) (mtree ow r)

msort : forall {X}{L : X -> X -> Set} -> OWOTO L -> 
        Muu LIST X <> -> Muo LIST L <> bot top
msort ow xs = mtree ow (deal xs)

insert23 : forall {X}{L : X -> X -> Set} -> OWOTO L -> forall {l u}(n : Nat) ->
           Muo INTV L <> l u -> Muo TR23 L n l u ->
           Muo TR23 L n l u +
           Sg X \ x -> Muo TR23 L n l (# x) * Muo TR23 L n (# x) u
insert23 ow ze < x , lx , xu > < lu > = ff , x , < lx > , < xu >
insert23 ow (su n) < x , lx , xu > < tt , y , ly , yu > with ow x y
insert23 ow (su n) < x , lx , xu > < tt , y , ly , yu >
  | tt , xy with insert23 ow n < x , lx , xy > ly
insert23 ow (su n) < x , lx , xu > < tt , y , ly , yu >
  | tt , xy | tt , ly' = tt , < tt , y , ly' , yu >
insert23 ow (su n) < x , lx , xu > < tt , y , ly , yu >
  | tt , xy | ff , z , lz , zy = tt , < ff , z , lz , y , zy , yu >
insert23 ow (su n) < x , lx , xu > < tt , y , ly , yu >
  | ff , yx with insert23 ow n < x , yx , xu > yu
insert23 ow (su n) < x , lx , xu > < tt , y , ly , yu >
  | ff , yx | tt , yu' = tt , < tt , y , ly , yu' >
insert23 ow (su n) < x , lx , xu > < tt , y , ly , yu >
  | ff , yx | ff , z , yz , zu = tt , < ff , y , ly , z , yz , zu >
insert23 ow (su n) < x , lx , xu > < ff , y , ly , z , yz , zu > with ow x y
insert23 ow (su n) < x , lx , xu > < ff , y , ly , z , yz , zu >
  | tt , xy with insert23 ow n < x , lx , xy > ly
insert23 ow (su n) < x , lx , xu > < ff , y , ly , z , yz , zu >
  | tt , xy | tt , ly' = tt , < ff , y , ly' , z , yz , zu >
insert23 ow (su n) < x , lx , xu > < ff , y , ly , z , yz , zu >
  | tt , xy | ff , w , lw , wy
  = ff , y , < tt , w , lw , wy > , < tt , z , yz , zu >
insert23 ow (su n) < x , lx , xu > < ff , y , ly , z , yz , zu >
  | ff , yx with ow x z
insert23 ow (su n) < x , lx , xu > < ff , y , ly , z , yz , zu >
  | ff , yx | tt , xz with insert23 ow n < x , yx , xz > yz
insert23 ow (su n) < x , lx , xu > < ff , y , ly , z , yz , zu >
  | ff , yx | tt , xz | tt , yz' = tt , < ff , y , ly , z , yz' , zu >
insert23 ow (su n) < x , lx , xu > < ff , y , ly , z , yz , zu >
  | ff , yx | tt , xz | ff , w , yw , wz
  = ff , w , < tt , y , ly , yw > , < tt , z , wz , zu >
insert23 ow (su n) < x , lx , xu > < ff , y , ly , z , yz , zu >
  | ff , yx | ff , zx with insert23 ow n < x , zx , xu > zu
insert23 ow (su n) < x , lx , xu > < ff , y , ly , z , yz , zu >
  | ff , yx | ff , zx | tt , zu' = tt , < ff , y , ly , z , yz , zu' >
insert23 ow (su n) < x , lx , xu > < ff , y , ly , z , yz , zu >
  | ff , yx | ff , zx | ff , w , zw , wu
  = ff , z , < tt , y , ly , yz > , < tt , w , zw , wu >

make23 : forall {X}{L : X -> X -> Set} -> OWOTO L ->
         Muu LIST X <> -> Sg Nat \ n -> Muo TR23 L n bot top
make23 ow < tt , <> > = ze , < <> >
make23 ow < ff , x , <> , xs > with make23 ow xs
... | n , t with insert23 ow n < x , <> , <> > t
... | tt , t' = n , t'
... | ff , t' = su n , < tt , t' >

sort23 : forall {X}{L : X -> X -> Set} -> OWOTO L -> 
         Muu LIST X <> -> Muo LIST L <> bot top
sort23 ow xs = flatten (snd (make23 ow xs))
