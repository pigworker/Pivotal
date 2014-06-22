\documentclass{sigplanconf}                    % onecolumn (standard format)

\usepackage[all]{xy}
\usepackage{alltt}
\usepackage{graphicx}
\usepackage{upgreek}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{url}
\usepackage{stmaryrd}
\usepackage{ifpdf}
\usepackage[usenames]{color}
\definecolor{citationcolour}{rgb}{0,0.4,0.2}
\definecolor{linkcolour}{rgb}{0,0,0.8}
\usepackage{hyperref}
\hypersetup{colorlinks=true,
            urlcolor=linkcolour,
            linkcolor=linkcolour,
            citecolor=citationcolour,
            pdftitle=How to Keep Your Neighbours in Order,
            pdfauthor={Conor McBride},
            pdfkeywords={}}  

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"
%subst numeral a = "\C{" a "}"

\usepackage{color}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.4,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor{yellow}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0,0,0}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\red}{\redFG}
  \newcommand{\green}{\greenFG}
  \newcommand{\blue}{\blueFG}
  \newcommand{\orange}{\orangeFG}
  \newcommand{\purple}{\purpleFG}
  \newcommand{\yellow}{\yellowFG}
  \newcommand{\brown}{\brownFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\whiteFG}
}

\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
}

\ColourStuff

\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\C}[1]{\red{\mathsf{#1}}}
\newcommand{\F}[1]{\green{\mathsf{#1}}}
\newcommand{\V}[1]{\purple{\mathit{#1}}}

\newtheorem{princ}{Principle}

%format Set = "\D{Set}"
%format Set1 = "\D{Set_1}"

\title{How to Keep Your Neighbours in Order}
\authorinfo{Conor McBride}
           {University of Strathclyde}
           {Conor.McBride@@strath.ac.uk}

\begin{document}
\conferenceinfo{ICFP~'14}{September 1--6, 2014, Gothenburg, Sweden}
\copyrightyear{2014}
\copyrightdata{978-1-4503-2873-9/14/09}
\doi{2628136.2628163} 
\maketitle

\begin{abstract}
I present a datatype-generic treatment of recursive container
types whose elements are guaranteed to be stored in increasing order,
with the ordering invariant rolled out systematically. Intervals, lists and
binary search trees are instances of the generic treatment.
On the journey to this treatment, I report a variety of failed experiments
and the transferable learning experiences they triggered. I demonstrate that
a \emph{total} element ordering is enough to deliver insertion and
flattening algorithms, and show that (with care about the formulation of the
types) the implementations remain as usual. Agda's \emph{instance arguments} and
\emph{pattern synonyms} maximize the proof search done by the typechecker and
minimize the appearance of proofs in program text, often eradicating them
entirely. Generalizing to indexed recursive container types, invariants such as
\emph{size} and \emph{balance} can be expressed in addition to \emph{ordering}.
By way of example, I implement insertion and deletion for 2-3 trees, ensuring
both order and balance by the discipline of type checking.
\end{abstract}

%if False
\begin{code}

module Pivotal where

\end{code}
%endif
%format (HOLE n) = "\yellowBG{\(?_{" n "}\)}"
%format (BROWN x) = "\brownBG{\(" x "\)}"
%format (LIE p (x)) = "\brownBG{\(" x "\)}"
%format (YELLOW x) = "\yellowBG{\(" x "\)}"
%format (FOOL y x) = y
%format -> = "\rightarrow"

\section{Introduction}

It has taken years to see what was under my nose. I have been
experimenting with ordered container structures for a \emph{long}
time \cite{dtpTalkLFCS}: how to keep lists ordered, how to keep binary
search trees ordered, how to flatten the latter to the
former. Recently, the pattern common to the structures and methods I
had often found effective became clear to me. Let me tell you about
it.  Patterns are, of course, underarticulated
abstractions. Correspondingly, let us construct a \emph{universe} of
container-like datatypes ensuring that elements are in increasing
order, good for intervals, ordered lists, binary search trees, and
more besides.

This paper is a literate Agda program. The entire development is available
at \url{https://github.com/pigworker/Pivotal}. As well as making the headline
contributions
\begin{itemize}
\item a datatype-generic treatment of ordering invariants and operations
  which respect them
\item a technique for hiding proofs from program texts
\item a precise implementation of insertion and deletion for 2-3 trees 
\end{itemize}
I take the time to explore the design space, reporting a selection of
the wrong turnings and false dawns I encountered on my journey to these
results. I try to extrapolate transferable design principles, so that
others in future may suffer less than I.

%format id = "\F{id}"
%format pattern = "\mathkw{pattern}"
%format constructor = "\mathkw{constructor}"
%format One = "\D{1}"
%format it = "\C{\langle\rangle}"
%format + = "\D{+}"
%format _+_ = "\_\!" + "\!\_"
%format inl = "\C{\triangleleft}"
%format inr = "\C{\triangleright}"
%format Sg = "\D{\Upsigma}"
%format * = "\F{\times}"
%format _*_ = "\_\!" * "\!\_"
%format / = "\!\!\C{,}\!"
%format _/_ = "\_\,\," / "\,\_"
%format fst = "\F{\uppi_1}"
%format snd = "\F{\uppi_2}"
%format Zero = "\D{0}"
%format Two = "\D{2}"
%format tt = "\C{t\!t}"
%format ff = "\C{f\!f}"
%format not = "\F{\neg}"
%format forall = "\D{\forall}\!\!"
%format o = "\F{\circ}"
%format _o_ = "\_\!" o "\!\_"
%format So = "\F{So}"
%format so = "\F{so}"
%format Maybe = "\D{Maybe}"
%format yes = "\C{yes}"
%format no = "\C{no}"
%format if = "\F{if}"
%format then = "\F{then}"
%format else = "\F{else}"
%format if_then_else_ = if "\_" then "\_" else "\_"
%format Nat = "\D{\mathbb{N}}"
%format ze = "\C{0}"
%format su = "\C{s}"
%format >> = "\F{\dot{\rightarrow}}"
%format _>>_ = "\_\!" >> "\!\_"
%format == = "\D{\equiv}"
%format _==_ = "\_\!" == "\!\_"


\section{How to Hide the Truth}

If we intend to enforce invariants, we shall need to mix a little bit of
logic in with our types and a little bit of proof in with our programming.
It is worth taking some trouble to set up our logical apparatus to maximize
the effort we can get from the computer and to minimize the textual cost
of proofs. We should prefer to encounter logic only when it is dangerously
absent!

Our basic tools are the types representing falsity and truth by virtue of
their number of inhabitants:

\begin{code}
data Zero : Set where                  -- no constructors!
record One : Set where constructor it  -- no fields!
\end{code}

Dependent types allow us to compute sets from data. E.g., we can
represent evidence for the truth of some Boolean expression which we might
have tested.

\begin{code}
data Two : Set where tt ff : Two

So : Two -> Set
So tt  = One
So ff  = Zero
\end{code}

A set |P| which evaluates to |Zero| or to |One| might be
considered `propositional' in that we are unlikely to
want to \emph{distinguish} its inhabitants. We might even
prefer not even to \emph{see} its inhabitants. I define a wrapper
type for propositions whose purpose is to hide proofs.

%format <P = "\D{\ulcorner}\!\!"
%format P> = "\!\!\D{\urcorner}"
%format <P_P> = <P "\," _ "\," P>
%format prf = "\F{prf}"
%format ! = "\C{!}"
\begin{code}
record <P_P> (P : Set) : Set where
  constructor !
  field {{prf}} : P
\end{code}

Agda uses braces to indicate that an argument or field is to be
suppressed by default in program texts and inferred somehow by the
typechecker. Single-braced variables are solved by unification, in the
tradition of Milner~\cite{DBLP:journals/jcss/Milner78}. Doubled braces
indicate \emph{instance arguments}, inferred by \emph{contextual
search}: if just one hypothesis can take the place of an instance
argument, it is silently filled in, allowing us a tiny bit of proof
automation~\cite{DBLP:conf/icfp/DevrieseP11}.  If an inhabitant of |<P
So b P>| is required, we may write |!| to indicate that we expect the
truth of |b| to be known.

Careful positioning of instance arguments seeds the context with useful
information. We may hypothesize over them quietly, and support forward
reasoning with a `therefore' operator.
%format => = "\F{\Rightarrow}"
%format _=>_ = _ => _
%format :- = "\F{\therefore}"
%format _:-_ = _ :- _
\begin{code}
_=>_ : Set -> Set -> Set
P => T = {{p : P}} -> T
infixr 3 _=>_

_:-_ : forall {P T} -> <P P P> -> (P => T) -> T
! :- t = t
\end{code}

This apparatus can give the traditional conditional a subtly more
informative type, thus:
\begin{code}
not : Two -> Two ; not tt  = ff ; not ff  = tt

if_then_else_ :
  forall {X} b -> (So b => X) -> (So (not b) => X) -> X
if tt  then t else f = t
if ff  then t else f = f
infix 1 if_then_else_
\end{code}

If ever there is a proof of |Zero| in the context, we should be able to
ask for anything we want. Let us define
%format magic = "\F{magic}"
\begin{code}
magic :  {X : Set} -> Zero => X
magic {{()}}
\end{code}
using Agda's \emph{absurd pattern} to mark the impossible instance argument
which shows that no value need be returned. E.g.,
|if tt then ff else magic : Two|.
%if False
\begin{code}
test : Two
test = if tt then ff else magic
\end{code}
%endif

Instance arguments are not a perfect fit for proof search: they were intended
as a cheap alternative to type classes, hence the requirement for exactly
one candidate instance. For proofs we might prefer to be less fussy about
redundancy, but we shall manage perfectly well for the purposes of this paper.


%\section{A Dump of Setting Up}


%if False
\begin{code}
data Nat : Set where
  ze : Nat
  su : Nat -> Nat
\end{code}

\begin{code}
{-# BUILTIN NATURAL Nat #-}

postulate BROWN : {X Y : Set} -> X -> Y
postulate LIE : (P : Set){X : Set} -> (P => X) -> X
postulate HOLE : {X : Set} -> Nat -> X
postulate FOOL : {X Y : Set} -> Y -> X -> Y

_o_ : {A : Set}{B : A -> Set}{C : (a : A) -> B a -> Set}
      (f : {a : A}(b : B a) -> C a b)(g : (a : A) -> B a) ->
      (a : A) -> C a (g a)
(f o g) x = f (g x)
infixr 3 _o_

id : {A : Set} -> A -> A
id a = a
\end{code}
%endif




\section{Barking Up the Wrong Search Trees}

%if False
\begin{code}
module BinarySearchTreeBad (P : Set)(le : P -> P -> Two) where
\end{code}
%endif

David Turner \cite{turner:ESFP} notes that whilst \emph{quicksort} is
often cited as a program which defies structural recursion, it
performs the same sorting algorithm (although not with the same memory
usage pattern) as building a binary search tree and then flattening
it. The irony is completed by noting that the latter sorting algorithm
is the archetype of structural recursion in Rod Burstall's development
of the concept \cite{burstall:induction}. Binary search trees have
empty leaves and nodes labelled with elements which act like \emph{pivots}
in quicksort: the left subtree stores elements which precede the pivot,
the right subtree elements which follow it. Surely this
invariant is crying out to be a dependent type! Let us search
for a type for search trees.

We could, of course, define binary search trees as ordinary
node-labelled trees with parameter |P| giving the type of pivots:
%format TrS = "\D{Tree}"
%format lfS = "\C{leaf}"
%format ndS = "\C{node}"
%format IsBST = "\F{IsBST}"

\begin{code}
  data TrS : Set  where
    lfS  : TrS ;  ndS  : TrS -> P -> TrS -> TrS
\end{code}
We might then define the invariant as a predicate |IsBST : TrS -> Set|,
implement insertion in our usual way, and prove separately
that our program maintains the invariant. However, the joy of dependently
typed programming is that refining the types of the data themselves
can often alleviate or obviate the burden of proof. Let us try to
bake the invariant in.

\paragraph{What should the type of a subtree tell us?} If we want to
check the invariant at a given node, we shall need some information
about the subtrees which we might expect comes from their type. We
require that the elements left of the pivot precede it, so we could
require the whole set of those elements represented somehow, but of
course, for any order worthy of the name, it suffices to check only
the largest. Similarly, we shall need to know the smallest element of
the right subtree. It would seem that we need the type of a search
tree to tell us its extreme elements (or that it is empty).

%format BST = "\D{BST}"
%format STRange = "\D{STRange}"
%format empty = "\C{\emptyset}"
%format - = "\!\C{{}- }\!"
%format _-_ = "\_\," - "\,\_"
\begin{code}
  data STRange : Set    where
    empty  : STRange ;  _-_    : P -> P -> STRange
  infix 9 _-_
\end{code}

\paragraph{From checking the invariant to enforcing it.}
%format valid = "\F{valid}"
%format ?> = "\F{?\rangle}"
%format _?>_ = _ ?> _
Assuming we can test the order on |P| with some |le : P -> P -> Two|,
we could write a recursive function to check whether a |TrS| is a valid
search tree and compute its range if it has one. Of course, we must
account for the possibility of invalidity, so let us admit failure in
the customary manner.
\begin{code}
  data Maybe (X : Set) : Set  where
    yes  : X -> Maybe X ;     no   : Maybe X

  _?>_ : forall {X} -> Two -> Maybe X -> Maybe X
  b  ?> mx  = if b then mx else no
  infixr 4 _?>_
\end{code}
The guarding operator |?>| allows us to attach a Boolean test.
We may now |valid|ate the range of a |TrS|.
\begin{code}
  valid : TrS -> Maybe STRange
  valid lfS = yes empty
  valid (ndS l p r) with valid l | valid r
  ... | yes empty    | yes empty    = yes (p - p)
  ... | yes empty    | yes (c - d)  = le p c ?> yes (p - d)
  ... | yes (a - b)  | yes empty    = le b p ?> yes (a - p)
  ... | yes (a - b)  | yes (c - d)
    = le b p ?> le p c ?> yes (a - d)
  ... | _            | _            = no
\end{code}

As |valid| is a \emph{fold} over the structure of |TrS|, we can follow
my colleagues Bob Atkey, Neil Ghani and Patricia Johann in computing
the \emph{partial refinement} \cite{DBLP:journals/corr/abs-1205-2492}
of |TrS| which |valid| induces. We seek a type |BST : STRange -> Set|
such that \(|BST r| \cong \{|t : TrS| \mid |valid t| = |yes r|\}\) and
we find it by refining the type of each constructor of |TrS| with the
check performed by the corresponding case of |valid|, assuming that
the subtrees yielded valid ranges. We can calculate the conditions to
check and the means to compute the output range if successful.

%format leftOK = "\F{lOK}"
%format rightOK = "\F{rOK}"
%format nodeRange = "\F{outRan}"
\begin{code}
  leftOK   : STRange -> P -> Two
  leftOK   empty    p  = tt
  leftOK   (_ - u)  p  = le u p

  rightOK  : P -> STRange -> Two
  rightOK  p  empty    = tt
  rightOK  p  (l - _)  = le p l

  nodeRange : STRange -> P -> STRange -> STRange
  nodeRange empty    p  empty    = p - p
  nodeRange empty    p  (_ - u)  = p - u
  nodeRange (l - _)  p  empty    = l - p
  nodeRange (l - _)  _  (_ - u)  = l - u
\end{code}

We thus obtain the following refinement from |TrS| to |BST|:
\begin{code}
  data BST : STRange -> Set where
    lfS  :  BST empty
    ndS  :  forall {l r} -> BST l -> (p : P) -> BST r ->
      So (leftOK l p) => So (rightOK p r) => BST (nodeRange l p r)
\end{code}

\paragraph{Attempting to implement insertion.}
Now that each binary search tree tells us its type, can we implement
insertion? Rod Burstall's implementation is as follows
%format insertS = "\F{insert}"
\begin{code}
  insertS : P -> TrS -> TrS
  insertS y lfS            = ndS lfS y lfS
  insertS y (ndS lt p rt)  =
    if le y p  then  ndS (insertS y lt) p rt
               else  ndS lt p (insertS y rt)
\end{code}
but we shall have to try a little harder to give a type to |insertS|,
as we must somehow negotiate the ranges. If we are inserting a new
extremum, then the range will be wider afterwards than before.
%format oRange = "\F{insRan}"
\begin{code}
  oRange : STRange -> P -> STRange
  oRange empty    y = y - y
  oRange (l - u)  y =
    if le y l then y - u else if le u y then l - y else l - u
\end{code}

So, we have the right type for our data and for our program. Surely the
implementation will go like clockwork!
%format shite = "\F{insert}"
\begin{spec}
  shite : forall {r} y -> BST r -> BST (oRange r y)
  shite y lfS            = ndS lfS y lfS
  shite y (ndS lt p rt)  =
    if le y p  then  (BROWN (ndS (shite y lt) p rt))
               else  (BROWN (ndS lt p (shite y rt)))
\end{spec}
The |lfS| case checks easily, but alas for |ndS|! We have |lt : BST l|
and |rt : BST r| for some ranges |l| and |r|. The |then| branch delivers
a |BST (nodeRange (oRange l y) p r)|, but the type required is
|BST (oRange (nodeRange l p r) y)|, so we need some theorem-proving to
fix the types, let alone to discharge the
obligation |So (leftOK (oRange l y) p)|. We could plough on
with proof and, coughing, push this definition through, but tough work ought to
make us ponder if we might have thought askew.

We have defined a datatype which is logically correct but
which is pragmatically disastrous. Is it thus inevitable that all
datatype definitions which enforce the ordering invariant will be
pragmatically disastrous? Or are there lessons we can learn about
dependently typed programming that will help us to do better?


\section{Why Measure When You Can Require?}

Last section, we got the wrong answer because we asked the
wrong question: ``What should the type of a subtree tell us?''
somewhat presupposes that information bubbles outward from subtrees to
the nodes which contain them. In Milner's
tradition, we are used to synthesizing the type of a thing. Moreover,
the very syntax of |data| declarations treats the index
delivered from each constructor as an output. It seems
natural to treat datatype indices as measures of the data.
That is all very well for the length of a vector, but when the
measurement is intricate, as when computing
a search tree's extrema, programming becomes vexed by the need for
theorems about the measuring functions. The presence of `green
slime'---defined functions in the return types of constructors---is a
danger sign.

We can take an alternative view of types, not as synthesized
measurements of data, bubbled outward, but as checked
\emph{requirements} of data, pushed \emph{inward}. To enforce the
invariant, let us rather ask ``What should we tell the
type of a subtree?''.

The elements of the left subtree must precede the pivot in the order;
those of the right must follow it. Correspondingly, our requirements
on a subtree amount to an \emph{interval} in which its elements must
fall. As any element can find a place somewhere in a search tree, we
shall need to consider unbounded intervals also. We can extend any
type with top and bottom elements as follows.
%format <$  = "\!\!"
%format $>D = "\D{\!\!_\bot^\top}"
%format <$_$>D = "\_\," $>D
%format tb = "\C{\scriptscriptstyle{\#}\!\!}"
%format top = "\C{\top}"
%format bot = "\C{\bot}"
\begin{code}
data <$_$>D (P : Set) : Set where
  top  :       <$ P $>D ; tb   : P ->  <$ P $>D ;  bot  :       <$ P $>D
\end{code}
and extend the order accordingly:
%format $>B = "\F{\!\!_\bot^\top}"
%format <$_$>B = "\_\," $>B
\begin{code}
<$_$>B : forall {P} -> (P -> P -> Two) -> <$ P $>D -> <$ P $>D -> Two
<$ le $>B _       top     = tt
<$ le $>B (tb x)  (tb y)  = le x y
<$ le $>B bot     _       = tt
<$ le $>B _       _       = ff
\end{code}

We can now index search trees by a pair of \emph{loose bounds}, not measuring
the range of the contents exactly, but constraining it sufficiently. At
each node, we can require that the pivot falls in the interval, then use the
pivot to bound the subtrees.
%if False
\begin{code}
module BinarySearchTreeBetter where
  postulate
    P : Set
    le : P -> P -> Two
\end{code}
%endif
%format leaf = "\C{leaf}"
%format pnode = "\C{pnode}"
%format node = "\C{node}"
\begin{code}
  data BST (l u : <$ P $>D) : Set where
    leaf   :   BST l u
    pnode  :  (p : P) -> BST l (tb p) -> BST (tb p) u ->
      So (<$ le $>B l (tb p)) => So (<$ le $>B (tb p) u) => BST l u
\end{code}
In doing so, we eliminate all the `green slime' from the indices of the
type. The |leaf| constructor now has many types, indicating all its elements
satisfy any requirements. We also gain |BST bot top| as the general type of
binary search trees for |P|. Unfortunately, we have been forced to make the
pivot value |p|, the first argument to |pnode|, as the type of the subtrees
now depends on it. Luckily, Agda now supports
\emph{pattern synonyms}, allowing
linear macros to abbreviate both patterns on the left and pattern-like
expressions on the right~\cite{aitken.reppy}.
We may fix up the picture:
\begin{code}
  pattern node lp p pu = pnode p lp pu
\end{code}

%format insert2 = "\F{insert}"
Can we implement |insert2| for this definition? We can certainly give it a
rather cleaner type. When we insert a new element into the left subtree of a
node, we must ensure that it precedes the pivot: that is, we expect
insertion to \emph{preserve} the bounds of the subtree, and we should already
know that the new element falls within them.
\begin{code}
  insert2 :  forall {l u} y -> BST l u ->
    So (<$ le $>B l (tb y)) => So (<$ le $>B (tb y) u) => BST l u
  insert2 y leaf            = node leaf y leaf
  insert2 y (node lt p rt)  =
    if le y p  then  node (insert2 y lt) p rt
               else  node lt p ((LIE (So (le p y)) (insert2 y rt)))
\end{code}
We have no need to repair type errors by theorem proving, and most of
our proof obligations follow directly from our assumptions. The recursive
call in the |then| branch requires a proof of |So (le y p)|, but that is
just the evidence delivered by our evidence-transmitting conditional.
However, the |else| case snatches defeat from the jaws of victory: the
recursive call needs a proof of |So (le p y)|, but all we have is a proof
of |So (not (le y p))|. For any given total ordering,
we should be able to fix this mismatch up by proving a theorem, but this is
still more work than I enjoy. The trouble is that we couched our definition
in terms of the truth of bits computed in a particular way, rather than the
ordering \emph{relation}. Let us now tidy up this detail.


\section{One Way Or The Other}

%format REL = "\F{Rel}"
%format ^>P = "\F{\!\!\urcorner}"
%format <^ = "\F{\ulcorner\!\!\!}"
%format <^_^>P = <^ _ "\," ^>P
%format $>F = "\F{\!^\top_\bot}"
%format <$_$>F = _ $>F
%format $>II = "\F{\!\!^\bullet}"
%format <$_$>II = _ "\," $>II
%format $>ii = "\C{\!\!^\circ}"
%format <$_$>ii = _ "\," $>ii
%format ival = "\F{ival}"
%format ihi = "\F{ihi}"
%format ilo = "\F{ilo}"
We can recast our definition in terms of relations---families of sets |REL P|
indexed by pairs.
\begin{spec}
REL : Set -> Set1
REL P = P * P -> Set
\end{spec}
giving us types which directly make statements about elements of |P|, rather
than about bits.

I must, of course, say how such pairs are defined: the habit of
dependently typed programmers is to obtain them as the degenerate case
of dependent pairs: let us have them.
\begin{code}
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _/_
  field
    fst : S
    snd : T fst
open Sg
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 5 _*_ _/_
\end{code}
%if False
\begin{code}
REL : Set -> Set1
REL P = P * P -> Set
\end{code}
%endif

Now, suppose we have some `less or equal' ordering
|L : REL P|. Let us have natural numbers by way of example,
%format Le = "\F{L}_{" Nat "}"
%format <= = "\F{\le}"
%format _<=_ = "\_\!" <= "\!\_"
%format NatD = Nat
%format zeD = ze
%format suD = su
\begin{code}
data NatD : Set where zeD : NatD ; suD : NatD -> NatD

Le : REL Nat
Le (x / y) = x <= y where
  _<=_ : Nat -> Nat -> Set
  ze    <= y     =  One
  su x  <= ze    =  Zero
  su x  <= su y  =  x <= y
\end{code}

%format OWOTO = "\F{OWOTO}"
The information we shall need is exactly the totality
of |L|: for any given |x| and |y|, |L| must hold \emph{One Way Or The Other},
as captured by the disjoint sum type, |OWOTO L (x / y)|, defined as follows:
%format le = "\C{le}"
%format ge = "\C{ge}"
\begin{code}
data _+_ (S T : Set) :  Set where
  inl : S -> S + T ;    inr : T -> S + T
infixr 4 _+_

OWOTO : forall {P}(L : REL P) -> REL P
OWOTO L (x / y) = <P L (x / y) P> + <P L (y / x) P>

pattern le  = inl !
pattern ge  = inr !
\end{code}
I have used pattern synonyms to restore the impression that we are just
working with a Boolean type, but the |!| serves to unpack evidence when
we test and to pack it when we inform.
We shall usually be able to keep silent about
ordering evidence, even from the point of its introduction.
For |Nat|, let us have
%format nowoto = "\F{owoto}"
\begin{code}
nowoto : forall x y -> OWOTO Le (x / y)
nowoto ze      y       = le
nowoto (su x)  ze      = ge
nowoto (su x)  (su y)  = nowoto x y
\end{code}
Note that we speak only of the crucial bit of information. 
Moreover, we especially benefit from type-level computation in the step case:
|OWOTO Le (su x / su y)| is the very same type as |OWOTO Le (x / y)|.

Any ordering relation on elements lifts readily to bounds: I have overloaded
the notation for lifting in the typesetting of this paper, but sadly not in
the Agda source code. Let us take the
opportunity to add propositional wrapping, to help us hide ordering proofs.
\begin{code}
<$_$>F <^_^>P : forall {P} -> REL P -> REL <$ P $>D
<$ L $>F (_     / top)   = One
<$ L $>F (tb x  / tb y)  = L (x / y)
<$ L $>F (bot   / _)     = One
<$ L $>F (_     / _)     = Zero
<^ L ^>P xy = <P <$ L $>F xy P>
\end{code}
The type |<^ L ^>P (x / y)| thus represents ordering evidence on bounds
with matching and construction by |!|, unaccompanied.


\section{Equipment for Relations and Other Families}

Before we get back to work in earnest, let us build a few tools for working
with relations and other such indexed type families: a relation is a family
which happens to be indexed by a pair. We shall have need of
pointwise truth, falsity, conjunction, disjunction and implication.
%format Never = "\F{\dot{0}}"
%format Always = "\F{\dot{1}}"
%format -+- = "\F{\dot{+}}"
%format _-+-_ = "\_\!" -+- "\!\_"
%format -*- = "\F{\dot{\times}}"
%format _-*-_ = "\_\!" -*- "\!\_"
\begin{code}
Never Always : {I : Set} -> I -> Set
Never   i = Zero
Always  i = One

_-+-_ _-*-_ _>>_ : {I : Set} ->
  (I -> Set) -> (I -> Set) -> I -> Set
(S -+- T)  i = S i + T i
(S -*- T)  i = S i * T i
(S >> T)   i = S i -> T i
infixr 3 _-+-_ ; infixr 4 _-*-_ ; infixr 2 _>>_
\end{code}

Pointwise implication will be useful for writing \emph{index-respecting}
functions, e.g., bounds-preserving operations.
It is useful to be able to state that something holds at every index
(i.e., `always works').
\begin{code}
[_] : {I : Set} -> (I -> Set) -> Set
[ F ] = forall {i} -> F i
\end{code}
With this apparatus, we can quite often talk about indexed things without
mentioning the indices, resulting in code which almost looks like its simply
typed counterpart. You can check that for any |S| and |T|,
  |inl : [ S >> S -+- T ]|
and so forth.
%if False
\begin{code}
mytest : forall {I}{S T : I -> Set} -> [ S >> S -+- T ]
mytest = inl
\end{code}
%endif


\section{Working with Bounded Sets}

%format ^ = "\F{\dot{\wedge}}"
%format _^_ = "\_\!" ^ "\!\_"
It will be useful to consider sets indexed by bounds in the same framework
as relations on bounds: \emph{propositions-as-types} means we have been doing
this from the start!
Useful combinator on such sets is the \emph{pivoted pair}, |S ^ T|,
indicating that some pivot value |p| exists, with |S| holding
before |p| and |T| afterwards. A pattern synonym arranges the order neatly.
%format \\ = "\!\!\C{\raisebox{ -0.07in}[0in][0in]{`}\!}"
%format _\\_\\_ = _ \\ _ \\ _
\begin{code}
_^_ : forall {P} -> REL <$ P $>D -> REL <$ P $>D -> REL <$ P $>D
_^_ {P} S T (l / u) = Sg P \ p -> S (l / tb p) * T (tb p / u)

pattern _\\_\\_ s p t = p / s / t
infixr 5 _\\_\\_ 
\end{code}

Immediately, we can define an \emph{interval} to be the type of
an element proven to lie within given bounds.
\begin{code}
<$_$>II : forall {P}(L : REL P) -> REL <$ P $>D
<$ L $>II = <^ L ^>P ^ <^ L ^>P
pattern <$_$>ii p = ! \\ p \\ !
\end{code}
With habitual tidiness, a pattern synonym conceals the evidence.

Let us then parametrize over some
\[ |owoto : forall x y -> OWOTO L (x / y)| \]
and reorganise our development.
%if False
\begin{code}
module BinarySearchTreeWorks where
  postulate
    P : Set
    L : REL P
    owoto : forall x y -> OWOTO L (x / y)
\end{code}
%endif
%format pnode = "\C{pnode}"
\begin{code}
  data BST (lu : <$ P $>D * <$ P $>D) : Set where
    leaf   :  BST lu
    pnode  :  ((<^ L ^>P -*- BST) ^ (<^ L ^>P -*- BST) >> BST) lu
  pattern node lt p rt = pnode (p / (! / lt) / (! / rt))
\end{code}

%format insert3 = "\F{insert}"
Reassuringly, the standard undergraduate error, arising from thinking
about \emph{doing} rather than \emph{being}, is now ill typed.
\begin{code}
  insert3 :  [ <$ L $>II >> BST >> BST ]
  insert3 <$ y $>ii leaf            = node leaf y leaf
  insert3 <$ y $>ii (node lt p rt)  with owoto y p
  ... | le  = (BROWN (insert3 <$ y $>ii lt))
  ... | ge  = (BROWN (insert3 <$ y $>ii rt))
\end{code}

However, once we remember to restore the unchanged parts of the tree,
we achieve victory, at last!
\begin{code}
  insert2 :  [ <$ L $>II >> BST >> BST ]
  insert2 <$ y $>ii leaf            = node leaf y leaf
  insert2 <$ y $>ii (node lt p rt)  with owoto y p
  ... | le  = node (insert2 <$ y $>ii lt) p rt
  ... | ge  = node lt p (insert2 <$ y $>ii rt)
\end{code}

The evidence generated by testing |owoto y p| is just what is needed
to access the appropriate subtree. We have found a method
which seems to work! But do not write home yet.

\section{The Importance of Local Knowledge}

Our current representation of an ordered tree with $n$ elements
contains $2n$ pieces of ordering evidence, which is $n-1$ too many. We
should need only $n+1$ proofs, relating the lower bound to the least
element, then comparing neighbours all the way along to the greatest
element (one per element, so far) which must then fall below the upper
bound (so, one more). As things stand, the pivot at the root is known
to be greater than every element in the right spine of its left subtree
and less than every element in the left spine of its right subtree.
If the tree was built by iterated insertion, these comparisons will
surely have happened, but that does not mean we should retain the
information.

Suppose, for example, that we want to rotate a tree, perhaps to keep it
balanced, then we have a little local difficulty:
%format rotR = "\F{rotR}"
\begin{spec}
  rotR : [ BST >> BST ]
  rotR (node (node lt m mt) p rt)
    = (BROWN node) lt (BROWN m) (node mt p rt)
  rotR t                           = t
\end{spec}
Agda rejects the outer |node| of the rotated tree for lack of evidence.
I expand the pattern synonyms to show what is missing.
\begin{code}
  rotR : [ BST >> BST ]
  rotR  (pnode
    ((! {{lp}} / pnode ((! {{lm}} / lt) \\ m \\ (! {{mp}} / mt)))
    \\ p \\ (! {{pu}} / rt))) = pnode ((! {{lm}} / lt) \\ m \\
    (! {{(HOLE 0)}} / pnode ((! {{mp}} / mt) \\ p \\ (! {{pu}} / rt))))
  rotR t = t
\end{code}
We can discard the non-local ordering evidence |lp : <$ L $>F (l / tb p)|,
but now we need the non-local |(HOLE 0) : <$ L $>F (tb m / u)| that we lack.
Of course, we can prove this goal from |mp| and |pu| if
|L| is transitive, but if we want to make less work, we
should rather not demand non-local ordering evidence in the first place.

Looking back at the type of |node|, note that the indices at which we
demand \emph{ordering} are the same as the indices at which we demand
\emph{subtrees}. If we strengthen the invariant on trees to ensure that
there is a sequence of ordering steps from the lower to the upper bound,
we could dispense with the sometimes non-local evidence stored in |node|s,
at the cost of a new constraint for |leaf|.

%if False
\begin{code}
module BinarySearchTreeBest where
  postulate
    P : Set
    L : REL P
    owoto : forall x y -> OWOTO L (x / y)
\end{code}
%endif
%format pleaf = "\C{pleaf}"
\begin{code}
  data BST (lu : <$ P $>D * <$ P $>D) : Set where
    pleaf  :  (<^ L ^>P >> BST) lu
    pnode  :  (BST ^ BST >> BST) lu

  pattern leaf          = pleaf !
  pattern node lt p rt  = pnode (lt \\ p \\ rt)
\end{code}

Indeed, a binary tree with $n$ nodes will have $n+1$ leaves. An in-order
traversal of a binary tree is a strict alternation,
leaf-node-leaf-\ldots -node-leaf, making a leaf the ideal place to keep
the evidence that neighbouring nodes are in order! Insertion remains easy.

\begin{code}
  insert2 :  [ <$ L $>II >> BST >> BST ]
  insert2 <$ y $>ii leaf = node leaf y leaf
  insert2 <$ y $>ii (node lt p rt)  with owoto y p
  ... | le  = node (insert2 <$ y $>ii lt) p rt
  ... | ge  = node lt p (insert2 <$ y $>ii rt)
\end{code}

Rotation becomes very easy: the above code now typechecks, with
no leaves in sight, so no proofs to rearrange!
\begin{code}
  rotR : [ BST >> BST ]
  rotR (node (node lt m mt) p rt)
     = node lt m (node mt p rt)
  rotR t = t
\end{code}

We have arrived at a neat way to keep a search tree in order,
storing pivot elements at nodes and proofs in leaves. Phew!

%format OList = "\D{OList}"
%format nil = "\C{nil}"
%format cons = "\C{cons}"
But it is only the end of the beginning. To complete our sorting
algorithm, we need to flatten binary search trees to ordered
\emph{lists}. Are we due another long story about the discovery
of a good definition of the latter? Fortunately not! The key idea
is that an ordered list is just a particularly badly balanced binary
search tree, where every left subtree is a |leaf|. We can nail that
down in short order, just by inlining |leaf|'s data in the left
subtree of |node|, yielding a sensible |cons|.
\begin{code}
  data OList (lu : <$ P $>D * <$ P $>D) : Set where
    nil   :  (<^ L ^>P >> OList) lu
    cons  :  (<^ L ^>P ^ OList >> OList) lu 
\end{code}
These are exactly the ordered lists Sam Lindley and I defined in
Haskell~\cite{DBLP:conf/haskell/LindleyM13}, but now we can see where the
definition comes from.

By figuring out how to build ordered binary search trees, we have
actually discovered how to build quite a variety of in-order data
structures. We simply need to show how the data are built from
particular patterns of |BST| components. So, rather than flattening
binary search trees, let us pursue a generic account of in-order datatypes,
then flatten them \emph{all}.


\section{Jansson and Jeuring's PolyP Universe}

%format JJ = "\D{JJ}"
%format qP = "\C{`P}"
%format qR = "\C{`R}"
%format q1 = "\C{`1}"
%format q+ = "\C{`+}"
%format _q+_ = "\_\!" q+ "\!\_"
%format q* = "\C{`\times}"
%format _q*_ = "\_\!" q* "\!\_"
%format (ElJJ) = "\F{\llbracket\_\rrbracket_{" JJ "}}}"
%format (ElJJ (t)) = "\F{\llbracket}" t "\F{\rrbracket_{" JJ "}}"
%format <! = "\F{\llbracket}\!"
%format !>JJ = "\!\F{\rrbracket_{" JJ "}}"
%format <!_!>JJ = <! _ !>JJ
%format MuJJ = "\D{\upmu_{" JJ "}}"
%format la = "\C{\langle}\!"
%format ra = "\!\C{\rangle}"
%format la_ra = la "\_" ra

If we want to see how to make the treatment of ordered container structures
systematic, we shall need some datatype-generic account of recursive types
with places for elements. A compelling starting point is the `PolyP' system
of Patrik Jansson and Johan Jeuring~\cite{DBLP:conf/popl/JanssonJ97},
which we can bottle as a
universe---a system of codes for types---in Agda, as follows:
\begin{code}
data JJ : Set where
  qR qP q1   : JJ
  _q+_ _q*_  : JJ -> JJ -> JJ
infixr 4 _q+_
infixr 5 _q*_
\end{code}

The |qR| stands for `recursive substructure' and the |qP| stands for
`parameter'---the type of elements stored in the container. Given meanings
for these, we interpret a code in |JJ| as a set.
\begin{code}
<!_!>JJ : JJ -> Set -> Set -> Set
<! qR !>JJ      R P = R
<! qP !>JJ      R P = P
<! q1 !>JJ      R P = One
<! S q+ T !>JJ  R P = <! S !>JJ R P + <! T !>JJ R P
<! S q* T !>JJ  R P = <! S !>JJ R P * <! T !>JJ R P
\end{code}
When we
`tie the knot' in |MuJJ F P|, we replace |F|'s |qP|s by some
actual |P| and its |qR|s by recursive uses of |MuJJ F P|.
\begin{code}
data MuJJ (F : JJ)(P : Set) : Set where
  la_ra : <! F !>JJ (MuJJ F P) P -> MuJJ F P
\end{code}

%format Applicative = "\D{Applicative}"
%format Monoid = "\D{Monoid}"
%format pure = "\F{pure}"
%format ap = "\F{ap}"
%format neutral = "\F{neutral}"
%format combine = "\F{combine}"
%format traverse = "\F{traverse}"
%format map = "\F{map}"
%format crush = "\F{crush}"
%format compMon = "\F{compMon}"
%format idApp = "\F{idApp}"
%format monApp = "\F{monApp}"
%format foldr = "\F{foldr}"
%format go = "\F{go}"

Being finitary and first-order, all of the containers encoded by |JJ|
are \emph{traversable} in the sense defined by Ross Paterson
and myself \cite{conor.ross:applicative.functors}.

\begin{code}
record Applicative (H : Set -> Set) : Set1 where
  field
    pure  : forall {X} -> X -> H X
    ap    : forall {S T} -> H (S -> T) -> H S -> H T
open Applicative
\end{code}

%format <*> = "\F{\circledast}"
%format _<*>_ = "\_\!" <*> "\!\_"
%format pur = "\F{pu}"
\begin{code}
traverse : forall {H F A B} -> Applicative H ->
  (A -> H B) -> MuJJ F A -> H (MuJJ F B)
traverse {H}{F}{A}{B} AH h t = go qR t where
  pur = pure AH ; _<*>_ = ap AH
  go : forall G ->
    <! G !>JJ (MuJJ F A) A -> H (<! G !>JJ (MuJJ F B) B)
  go qR        la t ra  = pur la_ra <*> go F t
  go qP        a        = h a
  go q1        it       = pur it
  go (S q+ T)  (inl s)  = pur inl <*> go S s
  go (S q+ T)  (inr t)  = pur inr <*> go T t
  go (S q* T)  (s / t)  = (pur _/_ <*> go S s) <*> go T t
\end{code}

We can specialise |traverse| to standard functorial |map|.
\begin{code}
idApp : Applicative (\ X -> X)
idApp = record {pure = id ; ap = id}

map : forall {F A B} ->
  (A -> B) -> MuJJ F A -> MuJJ F B
map = traverse idApp
\end{code}

We can equally well specialise |traverse| to a monoidal |crush|.
\begin{code}
record Monoid (X : Set) : Set where
  field neutral : X ;  combine : X -> X -> X
  monApp : Applicative (\ _ -> X)
  monApp = record
    {pure = \ _ -> neutral ; ap = combine}
  crush : forall {P F} -> (P -> X) -> MuJJ F P -> X
  crush = traverse {B = Zero} monApp
open Monoid
\end{code}

Endofunctions on a given set form a monoid with respect to
composition, which allows us a generic |foldr|-style operation.
\begin{code}
compMon : forall {X} -> Monoid (X -> X)
compMon = record
  {neutral = id ; combine = \ f g -> f o g}

foldr : forall {F A B} ->
  (A -> B -> B) -> B -> MuJJ F A -> B
foldr f b t = crush compMon f t b
\end{code}
We can use |foldr| to build up |B|s from any structure containing |A|s,
given a way to `insert' an |A| into a |B|, and an `empty' |B| to start with.
Let us check that our generic machinery is fit for purpose.


\section{The Simple Orderable Subuniverse of |JJ|}

%format SO = "\D{SO}"
%format !>SO = "\!\F{\rrbracket_{" SO "}}"
%format <!_!>SO = <! _ !>SO
%format MuSO = "\F{\upmu_{" SO "}}"
%format q^ = "\C{`\wedge}"
%format _q^_ = "\_\!" q^ "\!\_"

The quicksort algorithm divides a sorting problem in two by
partitioning about a selected \emph{pivot} element the remaining
data. Rendered as the process of building then flattening a binary
search tree \cite{burstall:induction}, the pivot element clearly marks
the upper bound of the lower subtree and the lower bound of the upper
subtree, giving exactly the information required to guide insertion.

We can require the presence of pivots between substructures by combining
the parameter |qP| and pairing |q*| constructs of the PolyP universe into a
single pivoting construct, |q^|, with two substructures and a pivot in between.
We thus acquire the simple orderable universe, |SO|, a subset of
|JJ| picked out as the image of a function, |<!_!>SO|. Now, |qP| stands also for
pivot!

\begin{code}
data SO : Set where
  qR q1      : SO
  _q+_ _q^_  : SO -> SO -> SO
infixr 5 _q^_

<!_!>SO : SO -> JJ
<! qR !>SO      = qR
<! q1 !>SO      = q1
<! S q+ T !>SO  = <! S !>SO q+ <! T !>SO
<! S q^ T !>SO  = <! S !>SO q* qP q* <! T !>SO

MuSO : SO -> Set -> Set
MuSO F P = MuJJ <! F !>SO P
\end{code}

Let us give |SO| codes for structures we often order and bound:

%format qListSO = "\F{`List}"
%format qTreeSO = "\F{`Tree}"
%format qIntervalSO = "\F{`Interval}"
\begin{code}
qListSO qTreeSO qIntervalSO : SO
qListSO      = q1 q+ (q1 q^ qR)
qTreeSO      = q1 q+ (qR q^ qR)
qIntervalSO  = q1 q^ q1
\end{code}

%format treeSO = "\F{tree}"
Every data structure described by |SO| is a regulated variety of
node-labelled binary trees. Let us check that we can turn anything
into a tree, preserving the substructure relationship. The
method\footnote{If you try constructing the division
operator as a primitive recursive function, this method will teach
itself to you.}
is to introduce a helper function, |go|, whose type separates |G|,
the structure of the top node, from |F| the structure of recursive
subnodes, allowing us to take the top node apart: we kick off with
|G = F|.

\begin{code}
treeSO : forall {P F} -> MuSO F P -> MuSO qTreeSO P
treeSO {P}{F} la f ra = go F f where
  go : forall G -> <! <! G !>SO !>JJ (MuSO F P) P -> MuSO qTreeSO P
  go qR        f            = treeSO f
  go q1        it           = la inl it ra
  go (S q+ T)  (inl s)      = go S s
  go (S q+ T)  (inr t)      = go T t
  go (S q^ T)  (s / p / t)  = la inr (go S s / p / go T t) ra
\end{code}

All |treeSO| does is strip out the |inl|s and |inr|s corresponding to
the structural choices offered by the input type and instead label the
void leaves |inl| and the pivoted nodes |inr|. Note well that a
singleton tree has void leaves as its left and right substructures,
and hence that the inorder traversal is a strict alternation of leaves
and pivots, beginning with the leaf at the end of the left spine and
ending with the leaf at the end of the right spine. As our |treeSO|
function preserves the leaf/pivot structure of its input, we learn that
\emph{every} datatype we can define in |SO| stores such an alternation
of leaves and pivots.

\newcommand{\blob}[5]{*++[o][F-]{#2} \ar@@{-}"#3,#4" \ar@@{-}"#3,#5" \ar@@{.>}"7,#1"}
\newcommand{\rect}[1]{*+[F-]{\;} \ar@@{.>}"7,#1"}
\newcommand{\rct}{*+[F-]{\,}}
\newcommand{\blo}[1]{\rct&*++[o][F-]{#1}&}
%%%%% -} -}
\[\xymatrix @@C=0in @@R=0in {
&&&&&&&\blob{8}{4}{2}{4}{16}&&&&&&&&&&&   \\
&&&\blob{4}{2}{3}{2}{6}&&&&&&&&&&&&\blob{16}{8}{3}{12}{18}&&& \\
&\blob{2}{1}{4}{1}{3}&&&&\blob{6}{3}{4}{5}{7}&&&&&&\blob{12}{6}{4}{10}{14}&&&&&&\blob{18}{9}{4}{17}{19}& \\
\rect{1}&&\rect{3}&&\rect{5}&&\rect{7}&&&\blob{10}{5}{5}{9}{11}&&&&\blob{14}{7}{5}{13}{15}&&&\rect{17}&&\rect{19}\\
&&&&&&&&\rect{9}&&\rect{11}&&\rect{13}&&\rect{15}&&&&\\
&&&&&&&&&&&&&&&&&& \raisebox{0in}[0.3in][0in]{}\\
\blo{1}\blo{2}\blo{3}\blo{4}\blo{5}\blo{6}\blo{7}\blo{8}\blo{9}\rct\\
}\]


We are now in a position to roll out the ``loose bounds'' method to
the whole of the |SO| universe. We need to ensure that each pivot is
in order with its neighbours and with the outer bounds, and the
alternating leaf/pivot structure gives us just what we need: let us store
the ordering evidence at the leaves!

%format MuOSO = "\F{\upmu^\le_{" SO "}}"
%format !>OSO = "\F{\rrbracket^\le_{" SO "}}"
%format <!_!>OSO = <! "\_" !>OSO
%if False
\begin{code}
pattern SHUNT X = X
\end{code}
%endif
%format SHUNT = "\hspace*{0.6in}"
\begin{code}
<!_!>OSO : SO -> forall {P} -> REL <$ P $>D -> REL P -> REL <$ P $>D
<! qR !>OSO       R L = R
<! q1 !>OSO       R L = <^ L ^>P
<! S q+ T !>OSO   R L = <! S !>OSO R L -+- <! T !>OSO R L
<! S q^ T !>OSO   R L = <! S !>OSO R L ^ <! T !>OSO R L

data MuOSO  (F : SO){P : Set}(L : REL P)
            (lu : <$ P $>D * <$ P $>D) : Set where
  la_ra : <! F !>OSO (MuOSO F L) L lu -> MuOSO F L lu
\end{code}
We have shifted from sets to relations, in that our types are indexed
by lower and upper bounds. The leaves demand evidence that the bounds
are in order, whilst the nodes require the pivot first, then use it to
bound the substructures appropriately.

Meanwhile, the need in nodes to bound the left substructure's type
with the pivot value disrupts the left-to-right spatial ordering of the
data, but we can apply a little cosmetic treatment, thanks to the
availability of pattern synonyms.


%format treeOSO = "\F{tree}"
%format $>T = "\F{\!\!^\Delta}"
%format <$_$>T = "\_\," $>T
%format $>I = $>II
%format <$_$>I = "\_\," $>I
%format $>ic = "\C{\!\!^\circ}"
%format <$_$>ic = "\_\," $>ii
With these two devices available, let us check that we can still turn
any ordered data into an ordered tree, writing |<$ L $>T (l / u)| for
|MuOSO qTreeSO L (l / u)|, and redefining intervals accordingly.
\begin{code}
<$_$>T <$_$>I : forall {P} -> REL P -> REL <$ P $>D

<$ L $>T  = MuOSO qTreeSO      L
pattern leaf          = la inl ! ra
pattern node lp p pu  = la inr (lp \\ p \\ pu) ra

<$ L $>I  = MuOSO qIntervalSO  L
pattern <$_$>ic p = la (p / ! / !) ra

treeOSO :  forall {P F}{L : REL P} -> [ MuOSO F L >> <$ L $>T ]
treeOSO {P}{F}{L} la f ra = go F f where
  go : forall G -> [ <! G !>OSO (MuOSO F L) L >> <$ L $>T ]
  go qR        f              = treeOSO f
  go q1        !              = leaf
  go (S q+ T)  (inl s)        = go S s
  go (S q+ T)  (inr t)        = go T t
  go (S q^ T)  (s \\ p \\ t)  = node (go S s) p (go T t)
\end{code}

We have acquired a collection of orderable datatypes which all amount
to specific patterns of node-labelled binary trees: an interval is a
singleton node; a list is a right spine. All share the treelike
structure which ensures that pivots alternate with leaves bearing the
evidence the pivots are correctly placed with respect to their
immediate neighbours.

%if False
\begin{code}
module BinarySearchTreeGen
  {P : Set}(L : REL P)(owoto : forall x y -> OWOTO L (x / y)) where
\end{code}
%endif

Let us check that we are where we were, so to speak.
Hence we can rebuild our binary search tree insertion for an element
in the corresponding interval:
\begin{code}
  insert2 : [ <$ L $>I >> <$ L $>T >> <$ L $>T ]
  insert2 <$ y $>ic leaf            = node leaf y leaf
  insert2 <$ y $>ic (node lt p rt)  with owoto y p
  ... | le  = node (insert2 <$ y $>ic lt) p rt
  ... | ge  = node lt p (insert2 <$ y $>ic rt)
\end{code}
The constraints on the inserted element are readily expressed via our
|qIntervalSO| type, but at no point need we ever name the ordering
evidence involved. The |owoto| test brings just enough new evidence into
scope that all proof obligations on the right-hand side can be
discharged by search of assumptions. We can now make a search tree from any
input container.
%format makeTree = "\F{makeTree}"
\begin{code}
  makeTree : forall {F} -> MuJJ F P -> <$ L $>T (bot / top)
  makeTree = foldr (\ p -> insert2 <$ p $>ic) leaf
\end{code}


\section{Digression: Merging Monoidally}


%format $>+ = "\!\!\F{^{+}}"
%format <$_$>+ = "\_\," $>+
%format mergeSO = "\F{merge}"
%format // = "\C{::}"
%format _//_ = _ // _
%format nil = "\C{[]}"
Let us name our family of ordered lists |<$ L $>+|, as the
leaves form a nonempty chain of |<^ L ^>P| ordering evidence.

\begin{code}
<$_$>+ : forall {P} -> REL P -> REL <$ P $>D
<$ L $>+ = MuOSO qListSO L

pattern nil        = la inl ! ra
pattern _//_ x xs  = la inr (x / ! / xs) ra
infixr 6 _//_
\end{code}


The next section addresses the issue of how to \emph{flatten} ordered
structures to ordered lists, but let us first consider how to
\emph{merge} them. Merging sorts differ from flattening sorts in that
order is introduced when `conquering' rather than `dividing'.

We can be sure that whenever two ordered lists share lower and upper bounds,
they can be merged within the same bounds. Again, let us assume a type
|P| of pivots, with |owoto| witnessing the totality of order |L|.
%format mergeNO = "\F{merge}"
%if False
\begin{code}
module MergeSO where
  postulate
    P : Set
    L : REL P
    owoto : forall x y -> OWOTO L (x / y)
\end{code}
%endif
The familiar definition of |mergeNO| typechecks but falls just
outside the class of lexicographic recursions accepted by Agda's termination
checker. I have locally expanded pattern synonyms to dig out the concealed
evidence which causes the trouble.
\begin{spec}
  mergeNO : [ <$ L $>+ >> <$ L $>+ >> <$ L $>+ ]
  mergeNO  nil                                     ys         = ys
  mergeNO  xs                                      nil        = xs  
  mergeNO  la inr (BROWN (! {{_}}) \\ x \\ xs) ra  (y // ys)  with owoto x y
  ... | le  = x // mergeNO xs (y //ys)
  ... | ge  = y // mergeNO la inr ((BROWN (! {{_}})) \\ x \\ xs) ra ys
\end{spec}
In one step case, the first list gets smaller, but in the other,
where we decrease the second list, the first does not remain the
same: it contains fresh evidence that |x| is above the tighter lower bound, |y|.
Separating the recursion on the second list is sufficient to show that both
recursions are structural.

\begin{code}
  mergeSO : [ <$ L $>+ >> <$ L $>+ >> <$ L $>+ ]
  mergeSO          nil        = id
  mergeSO {l / u}  (x // xs)  = go where
    go :  forall {l}{{_ : <$ L $>F (l / tb x)}} -> (<$ L $>+ >> <$ L $>+) (l / u)
    go nil        = x // xs
    go (y // ys)  with owoto x y
    ... | le  = x // mergeSO xs (y // ys)
    ... | ge  = y // go ys

\end{code}
The helper function |go| inserts |x| at its
rightful place in the second list, then resumes merging with |xs|.

Merging equips ordered lists with monoidal structure.
%format olistMon = "\F{olMon}"
\begin{code}
  olistMon : forall {lu} -> <$ L $>F lu => Monoid (<$ L $>+ lu)
  olistMon = record {neutral = nil ; combine = mergeSO}
\end{code}

An immediate consequence is that we gain a family of sorting algorithms
which amount to depth-first merging of a given intermediate data structure,
making a singleton from each pivot.
%format mergeJJ = mergeSO "_{" JJ "}"
\begin{code}
  mergeJJ : forall {F} -> MuJJ F P -> <$ L $>+ (bot / top)
  mergeJJ = crush olistMon \ p -> p // nil
\end{code}

%format mergeSort = "\F{mergeSort}"
The instance of |mergeJJ| for \emph{lists} is exactly \emph{insertion} sort:
at each cons, the singleton list of the head is merged with the sorted tail.
To obtain an efficient |mergeSort|, we should arrange the inputs as
a leaf-labelled binary tree.

%format qLTree = "\F{`qLTree}"
%format twistIn = "\F{twistIn}"
%format none = "\C{none}"
%format one = "\C{one}"
%format fork = "\C{fork}"
\begin{code}
  qLTree : JJ
  qLTree = (q1 q+ qP) q+ qR q* qR

  pattern none      = la inl (inl it) ra
  pattern one p     = la inl (inr p) ra
  pattern fork l r  = la inr (l / r) ra
\end{code}

We can add each successive elements to the tree with a twisting insertion,
placing the new element at the bottom of the left spine, but swapping the
subtrees at each layer along the way to ensure fair distribution.
\begin{code}
  twistIn : P -> MuJJ qLTree P -> MuJJ qLTree P
  twistIn p none        = one p
  twistIn p (one q)     = fork (one p) (one q)
  twistIn p (fork l r)  = fork (twistIn p r) l
\end{code}

If we notice that |twistIn| maps elements to endofunctions on trees, we can
build up trees by a monoidal |crush|, obtaining an efficient generic sort for
any container in the |JJ| universe.
\begin{code}
  mergeSort : forall {F} -> MuJJ F P -> <$ L $>+ (bot / top)
  mergeSort = mergeJJ o foldr twistIn none
\end{code}



\section{Flattening With Concatenation}

Several sorting algorithms amount to building an ordered intermediate structure,
then flattening it to an ordered list.
As all of our orderable structures amount to trees, it suffices to flatten
trees to lists. Let us take the usual na{\"\i}ve approach as our starting
point. In Haskell, we might write
\begin{alltt}
flatten Leaf         = []
flatten (Node l p r) = flatten l ++ p : flatten r
\end{alltt}
so let us try to do the same in Agda with ordered lists. We shall need
concatenation, so let us try to join lists with a shared bound |p| in the
middle.
%format ++ = "\F{+\!\!+}"
%format _++_ = "\_\!" ++ "\!\_"
\begin{code}
infixr 8 _++_
_++_ :  forall {P}{L : REL P}{l p u} ->
  <$ L $>+ (l / p) -> <$ L $>+ (p / u) -> <$ L $>+ (l / u)
nil        ++ ys = (BROWN ys)
(x // xs)  ++ ys = x // xs ++ ys
\end{code}

The `cons' case goes without a hitch, but there is trouble at `nil'.
We have |ys : MuOSO qListSO L (p / u)| and we know |<$ L $>F (l / p)|, but
we need to return a |MuOSO qListSO L (l / u)|.

\[\xymatrix @@C=0in @@R=0in {
\rct&*++[][F-]{|++|}&\blo{4}\blo{5}\blo{6}\blo{7}\blo{8}\blo{9}\rct\\
}\]

``The trouble is easy to fix,'' one might confidently assert, whilst
secretly thinking, ``What a nuisance!''. We can readily write a helper
function which unpacks |ys|, and whether it is nil or cons, extends its
leftmost order evidence by transitivity. And this really is a nuisance,
because, thus far, we have not required transitivity to keep our code
well typed: all order evidence has stood between neighbouring elements.
Here, we have two pieces of ordering evidence which we must join, because
we have nothing to put in between them.
Then, the penny drops. Looking back at the code for flatten, observe that
|p| is the pivot and the whole plan is to put it between the lists. You
can't always get what you want, but you can get what you need.

%format sandwich = "\F{sandwich}"
\begin{code}
sandwich :  forall {P}{L : REL P} -> [ (<$ L $>+ ^ <$ L $>+) >> <$ L $>+ ]
sandwich (nil      \\ p \\ ys)  = p // ys
sandwich (x // xs  \\ p \\ ys)  = x // sandwich (xs \\ p \\ ys)
\end{code}

%format flattenT = "\F{flatten}"
%format flattenOSO = "\F{flatten}^\le_{" SO "}"
We are now ready to flatten trees, thence any ordered
structure: 

\begin{code}
flattenT : forall {P}{L : REL P} -> [ <$ L $>T >> <$ L $>+ ]
flattenT leaf          = nil
flattenT (node l p r)  = sandwich (flattenT l \\ p \\ flattenT r)

flattenOSO : forall {P}{L : REL P}{F} -> [ MuOSO F L >> <$ L $>+ ]
flattenOSO = flattenT o treeOSO
\end{code}

For a little extra speed we might fuse that composition, but it seems
frivolous to do so as the benefit is outweighed by the quadratic penalty
of left-nested concatenation. The standard remedy applies: we can introduce
an accumulator \cite{Wadler87theconcatenate}, but our experience with |++|
should alert us to the possibility that it may require some thought.


\section{Faster Flattening, Generically}

%format flandwich = "\F{flandwich}"
%format fflatten = "\F{flatten}"
We may define |fflatten| generically, and introduce an accumulator yielding a
combined flatten-and-append which works right-to-left, growing the
result with successive conses. But what should be the bounds of the
accumulator? If we have not learned our lesson, we might be tempted by
%format flapp = "\F{flapp}"
\begin{spec}
flapp : forall {F P}{L : REL P}{l p u} ->
  MuOSO F L (l / p) -> <$ L $>+ (p / u) -> <$ L $>+ (l / u)
\end{spec}
but again we face the question of what to do when we reach a leaf. We
should not need transitivity to rearrange a tree of ordered neighbours
into a sequence. We can adopt the previous remedy of inserting the element
|p| in the middle, but we shall then need to think about where |p| will
come from in the first instance, for example when flattening an empty
structure.
\begin{code}
flapp : forall {F P}{L : REL P} G ->
    [ <! G !>OSO (MuOSO F L) L ^ <$ L $>+ >> <$ L $>+ ]
flapp {F} qR    (la t ra         \\ p \\ ys)  = flapp F (t \\ p \\ ys)
flapp q1        (!               \\ p \\ ys)  = p // ys
flapp (S q+ T)  (inl s           \\ p \\ ys)  = flapp S (s \\ p \\ ys)
flapp (S q+ T)  (inr t           \\ p \\ ys)  = flapp T (t \\ p \\ ys)
flapp (S q^ T)  ((s \\ p' \\ t)  \\ p \\ ys)
  = flapp S (s \\ p' \\ flapp T (t \\ p \\ ys))
\end{code}
To finish the job, we need to work our way down the right spine of the
input in search of its rightmost element, which initialises |p|.
\begin{code}
fflatten : forall {F P}{L : REL P} -> [ MuOSO F L >> <$ L $>+ ]
fflatten {F}{P}{L}{l / u} la t ra = go F t  where
  go : forall {l} G -> <! G !>OSO (MuOSO F L) L (l / u) -> <$ L $>+ (l / u)
  go qR        t              = fflatten t
  go q1        !              = nil
  go (S q+ T)  (inl s)        = go S s
  go (S q+ T)  (inr t)        = go T t
  go (S q^ T)  (s \\ p \\ t)  = flapp S (s \\ p \\ go T t)
\end{code}

This is effective, but it is more complicated than I should like. It
is basically the same function twice, in two different modes,
depending on what is to be affixed \emph{after} the rightmost order
evidence in the structure being flattened: either a pivot-and-tail in
the case of |flapp|, or nothing in the case of |fflatten|. The problem
is one of parity: the thing we must affix to one odd-length
leaf-node-leaf alternation to get another is an even-length node-leaf
alternation. Correspondingly, it is hard to express the type of the
accumulator cleanly. Once again, I begin to suspect that this is a
difficult thing to do because it is the wrong thing to do. How can we
reframe the problem, so that we work only with odd-length leaf-delimited
data?


\section{A Replacement for Concatenation}

My mathematical mentor, Tom K\"orner, is fond of remarking ``A
mathematician is someone who knows that $0$ is $0+0$". It is often
difficult to recognize the structure you need when the problem in front of
you is a degenerate case of it. If we think again about concatenation,
we might realise that it does not amount to \emph{affixing} one list
to another, but rather \emph{replacing} the `nil' of the first list
with the whole of the second. We might then notice that the
\emph{monoidal} structure of lists is in fact degenerate
\emph{monadic} structure.

Any syntax has a monadic structure, where `return' embeds variables as
terms and `bind' is substitution. Quite apart from their `prioritised
choice' monadic structure, lists are the terms of a degenerate syntax
with one variable (called `nil') and only unary operators (`cons' with
a choice of element). Correspondingly, they have this substitution
structure: substituting nil gives concatenation, and the monad laws
are the monoid laws.

Given this clue, let us consider concatenation and flattening in terms
of \emph{replacing} the rightmost leaf by a list, rather than affixing
more data to it. We replace the list to append with a function which
maps the contents of the rightmost leaf---some order evidence---to its
replacement. The type looks more like that of `bind' than `append',
because in some sense it is!

%format +++ = ++
%format _+++_ = _++_
%format Replacement = "\F{RepL}"
\begin{code}
infixr 8 _+++_
Replacement : forall {P} -> REL P -> REL <$ P $>D
Replacement L (n / u) = forall {m} -> <$ L $>F (m / n) => <$ L $>+ (m / u)

_+++_ : forall {P}{L : REL P}{l n u} ->
  <$ L $>+ (l / n) -> Replacement L (n / u) -> <$ L $>+ (l / u)
nil        +++ ys = ys
(x // xs)  +++ ys = x // xs +++ ys
\end{code}

Careful use of instance arguments leaves all the manipulation of
evidence to the machine. In the |nil| case, |ys| is silently
instantiated with exactly the evidence exposed in the |nil| pattern
on the left.

Let us now deploy the same technique for |fflatten|.

%format fflapp = "\F{flapp}"
%format flatten = "\F{flatten}"
\begin{code}
fflapp : forall {P}{L : REL P}{F}{l n u} ->
  MuOSO F L (l / n) ->  Replacement L (n / u) -> <$ L $>+ (l / u)
fflapp {P}{L}{F}{u = u} t ys = go qR t ys where
  go :   forall {l n} G -> <! G !>OSO (MuOSO F L) L (l / n) ->
          Replacement L (n / u) -> <$ L $>+ (l / u)
  go qR        la t ra        ys  = go F t ys
  go q1        !              ys  = ys
  go (S q+ T)  (inl s)        ys  = go S s ys
  go (S q+ T)  (inr t)        ys  = go T t ys
  go (S q^ T)  (s \\ p \\ t)  ys  = go S s (p // go T t ys)

flatten : forall {P}{L : REL P}{F} -> [ MuOSO F L >> <$ L $>+ ]
flatten t = fflapp t nil
\end{code}


\section{An Indexed Universe of Orderable Data}

%format IO = "\D{IO}"
%format !>IO = "\F{\rrbracket^\le_{" IO "}}"
%format <!_!>IO = <! "\_" !>IO
%format MuIO = "\D{\upmu^\le_{" IO "}}"
%format q0 = "\C{`0}"

Ordering is not the only invariant we might want to enforce on
orderable data structures. We might have other properties in mind,
such as size, or balancing invariants. It is straightforward to extend
our simple universe to allow general indexing as well as
orderability. We can extend our simple orderable universe |SO| to an
indexed orderable universe |IO|, just by marking each recursive
position with an index, then computing the code for each node as a
function of its index. We may add a |q0| code to rule out some cases
as illegal.

\begin{code}
data IO (I : Set) : Set where
  qR         : I -> IO I
  q0 q1      : IO I
  _q+_ _q^_  : IO I -> IO I -> IO I

<!_!>IO :  forall {I P} -> IO I ->
           (I -> REL <$ P $>D) -> REL P -> REL <$ P $>D
<! qR i !>IO    R L  = R i
<! q0 !>IO      R L  = \ _ -> Zero
<! q1 !>IO      R L  = <^ L ^>P
<! S q+ T !>IO  R L  = <! S !>IO R L -+- <! T !>IO R L
<! S q^ T !>IO  R L  = <! S !>IO R L ^ <! T !>IO R L

data MuIO  {I P : Set}(F : I -> IO I)(L : REL P)
           (i : I)(lu : <$ P $>D * <$ P $>D) : Set where
  la_ra : <! F i !>IO (MuIO F L) L lu -> MuIO F L i lu
\end{code}

We recover all our existing data structures by trivial indexing.
%format qListIO = "\F{`List}"
%format qTreeIO = "\F{`Tree}"
%format qIntervalIO = "\F{`Interval}"
%format qVecIO = "\F{`Vec}"
%format qEvenIO = "\F{`Even}"
\begin{code}
qListIO qTreeIO qIntervalIO : One -> IO One
qListIO      _ = q1 q+ (q1 q^ qR it)
qTreeIO      _ = q1 q+ (qR it q^ qR it)
qIntervalIO  _ = q1 q^ q1
\end{code}
We also lift our existing type-forming abbreviations:
%format $>i+ = $>+
%format <$_$>i+ = "\_\," $>i+
%format $>iT = "\F{\!\!^\Delta}"
%format <$_$>iT = "\_\," $>iT
%format $>iI = $>I
%format <$_$>iI = "\_\," $>iI
%format $>ic = "\C{\!\!^\circ}"
%format <$_$>ic = "\_\," $>ic
%format $>io = "\C{\!\!^\circ}"
%format <$_$>io = "\_\," $>io
\begin{code}
<$_$>i+ <$_$>iT <$_$>iI : forall {P} -> REL P -> REL <$ P $>D
<$ L $>i+  = MuIO qListIO      L it
<$ L $>iT  = MuIO qTreeIO      L it
<$ L $>iI  = MuIO qIntervalIO  L it
\end{code}
%if False
\begin{code}
pattern <$_$>io p = la p / ! / ! ra
\end{code}
%endif

However, we may also make profitable use of indexing: here are ordered
\emph{vectors}.
\begin{code}
qVecIO : Nat -> IO Nat
qVecIO ze      = q1
qVecIO (su n)  = q1 q^ qR n
\end{code}
Note that we need no choice of constructor or storage of length information:
the index determines the shape. If we want, say, even-length tuples, we can use
|q0| to rule out the odd cases.
\begin{code}
qEvenIO : Nat -> IO Nat
qEvenIO ze           = q1
qEvenIO (su ze)      = q0
qEvenIO (su (su n))  = q1 q^ q1 q^ qR n
\end{code}
We could achieve a still more flexible notion of data structure by allowing
a general |Sg|-type rather than our binary |q+|, but we have what we need
for finitary data structures with computable conditions on indices.

%format treeIO = "\F{tree}"

The |treeIO| operation carries over unproblematically, with more indexed
input but plain output.
\begin{code}
treeIO :  forall {I P F}{L : REL P}{i : I} ->
  [ MuIO F L i >> <$ L $>iT ]
\end{code}
%if False
\begin{code}
pattern leif = la inl ! ra
pattern nodi lp p pu = la inr (p / lp / pu) ra
treeIO {F = F}{L = L}{i = i} la t ra = go (F i) t where
  go : forall G -> [ <! G !>IO (MuIO F L) L >> <$ L $>iT ]
  go (qR i)    t              = treeIO t
  go q0        ()
  go q1        !              = leif
  go (S q+ T)  (inl s)        = go S s
  go (S q+ T)  (inr t)        = go T t
  go (S q^ T)  (s \\ p \\ t)  = nodi (go S s) p (go T t)
\end{code}
%endif

%format flattenIO = "\F{flatten}"
Similarly, |flattenIO| works (efficiently) just as before.
\begin{code}
flattenIO :  forall {I P F}{L : REL P}{i : I} ->
  [ MuIO F L i >> <$ L $>i+ ]
\end{code}
%if False
\begin{code}
pattern _/i/_ x xs = la inr (x / ! / xs) ra
flattenIO {I}{P}{F}{L}{i}{l / u} la t ra = go (F i) t la inl ! ra where
  go : forall G {l n} -> <! G !>IO (MuIO F L) L (l / n) ->
       (forall {m} -> <$ L $>F (m / n) => <$ L $>i+ (m / u)) ->
       <$ L $>i+ (l / u)
  go (qR i)    la t ra        ys = go (F i) t ys
  go q0        ()             ys
  go q1        !              ys = ys
  go (S q+ T)  (inl s)        ys = go S s ys
  go (S q+ T)  (inr t)        ys = go T t ys
  go (S q^ T)  (s \\ p \\ t)  ys = go S s (p /i/ go T t ys)
\end{code}
%endif

We now have a universe of indexed orderable data structures with efficient
flattening. Let us put it to work.


\section{Balanced 2-3 Trees}

%format q23TIO = "\F{`Tree23}"
To ensure a logarithmic access time for search trees, we can keep them
balanced. Maintaining balance as close to perfect as possible is
rather fiddly, but we can gain enough balance by allowing a little
redundancy.  A standard way to achieve this is to insist on uniform height, but
allow internal nodes to have
either one pivot and two subtrees, or two pivots and three subtrees.
We may readily encode these \emph{2-3 trees} and give pattern synonyms
for the three kinds of structure. This approach is much
like that of \emph{red-black} (effectively, 2-3-4) trees, for which
typesafe balancing has a tradition going back to
Hongwei Xi and Stefan Kahrs \cite{xi99waaapl,DBLP:journals/jfp/Kahrs01}.
%format $>23 = "\F{\!\!\!^{23}}"
%format <$_$>23 = "\_" $>23
%format no0 = "\C{no}_{\C{0}}"
%format no2 = "\C{no}_{\C{2}}"
%format no3 = "\C{no}_{\C{3}}"
\begin{code}
q23TIO : Nat -> IO Nat
q23TIO ze      = q1
q23TIO (su h)  = qR h q^ (qR h q+ (qR h q^ qR h))

<$_$>23 : forall {P}(L : REL P) -> Nat -> REL <$ P $>D
<$ L $>23 = MuIO q23TIO L

pattern no0               = la ! ra
pattern no2 lt p rt       = la p / lt / inl rt ra
pattern no3 lt p mt q rt  = la p / lt / inr (q / mt / rt) ra

\end{code}

%if False
\begin{code}
pattern via p = p / ! / !
pattern _-\_ t p = p / t / !
\end{code}
%endif

When we map a 2-3 tree of height $n$ back to binary trees, we get a
tree whose left spine has length $n$ and whose right spine has a length
between $n$ and $2n$.

Insertion is quite similar to binary search tree insertion, except that
it can have the impact of increasing height. The worst that can happen
is that the resulting tree is too tall but has just one pivot at the root.
Indeed, we need this extra wiggle room immediately for the base case!
%if False
\begin{code}
module Tree23
  {P : Set}(L : REL P)(owoto : forall x y -> OWOTO L (x / y)) where
\end{code}
%endif
%format ins23 = "\F{ins23}"
\begin{code}
  ins23 :  forall h {lu} -> <$ L $>iI lu -> <$ L $>23 h lu ->
           <$ L $>23 h lu +
           Sg P \ p -> <$ L $>23 h (fst lu / tb p) * <$ L $>23 h (tb p / snd lu)
  ins23 ze      <$ y $>io no0 = inr (la ! ra \\ y \\ la ! ra)
\end{code}
In the step case, we must find our way to the appropriate subtree by
suitable use of comparison.
\begin{spec}
  ins23 (su h)  <$ y $>io la lt \\ p \\ rest ra  with owoto y p
  ins23 (su h)  <$ y $>io la lt \\ p \\ rest ra  | le  =   (HOLE 0)
  ins23 (su h)  <$ y $>io (no2 lt p rt)          | ge  =   (HOLE 1)
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)     | ge with owoto y q
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)     | ge  |  le  = (HOLE 2)
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)     | ge  |  ge  = (HOLE 3)
\end{spec}
Our |(HOLE 0)| covers the case where the new element belongs in the
left subtree of either a 2- or 3-node; |(HOLE 1)| handles the right
subtree of a 2-node; |(HOLE 2)| and |(HOLE 3)| handle middle and right subtrees
of a 3-node after a further comparison. Note that we inspect |rest| only
after we have checked the result of the first comparison, making real
use of the way the |with| construct brings more data to the case analysis but
keeps the existing patterns open to further refinement, a need foreseen by
the construct's designers \cite{conor.james:viewfromleft}.

Once we have identified the appropriate subtree, we can make the recursive
call. If we are lucky, the result will plug straight back into the same hole.
Here is the case for the left subtree.
%if False
\begin{code}
  ins23 (su h)  <$ y $>io la lt \\ p \\ rest ra with owoto y p
\end{code}
%endif
\begin{code}
  ins23 (su h)  <$ y $>io la lt \\ p \\ rest ra | le
    with ins23 h <$ y $>io lt
  ins23 (su h)  <$ y $>io la lt \\ p \\ rest ra | le
    | inl lt'                = inl la lt' \\ p \\ rest ra
\end{code}
However, if we are unlucky, the result of the recursive call is too big.
If the top node was a 2-node, we can accommodate the extra data by returning
a 3-node. Otherwise, we must rebalance and pass the `too big' problem upward.
Again, we gain from delaying the inspection of |rest| until we are sure
reconfiguration will be needed.
\begin{code}
  ins23 (su h)  <$ y $>io (no2 lt p rt)       | le
    | inr (llt \\ r \\ lrt)  = inl (no3 llt r lrt p rt)
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)  | le
    | inr (llt \\ r \\ lrt)  = inr (no2 llt r lrt \\ p \\ no2 mt q rt)
\end{code}
For the |(HOLE 1)| problems, the top 2-node can always accept the
result of the recursive call somehow, and the choice offered by the
return type conveniently matches the node-arity choice, right of the
pivot.
%if False
\begin{code}
  ins23 (su h)  <$ y $>io (no2 lt p rt) | ge  with ins23 h <$ y $>io rt
  ins23 (su h)  <$ y $>io (no2 lt p rt) | ge  | rt' = inl la lt \\ p \\ rt' ra
\end{code}
%endif
%if False
\begin{code}
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt) | ge  with owoto y q
\end{code}
%endif
For completeness, I give the middle (|(HOLE 2)|) and right (|(HOLE 3)|)
cases for 3-nodes,
but it works just as on the left.
\begin{code}
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)  | ge  |   le
    with ins23 h <$ y $>io mt
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)  | ge  |   le
    | inl mt'                = inl (no3 lt p mt' q rt)
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)  | ge  |   le
    | inr (mlt \\ r \\ mrt)  = inr (no2 lt p mlt \\ r \\ no2 mrt q rt)

  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)  | ge  |   ge
    with ins23 h <$ y $>io rt
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)  | ge  |   ge
    | inl rt'                = inl (no3 lt p mt q rt')
  ins23 (su h)  <$ y $>io (no3 lt p mt q rt)  | ge  |   ge
    | inr (rlt \\ r \\ rrt)  = inr (no2 lt p mt \\ q \\ no2 rlt r rrt)
\end{code}

Pleasingly, the task of constructing suitable return values in each of
these cases is facilitated by Agda's type directed search gadget,
\emph{Agsy}~\cite{DBLP:conf/types/LindbladB04}. There are but two
valid outputs constructible from the pieces available: the original
tree reconstituted, and the correct output.

To complete the efficient sorting algorithm based on 2-3 trees, we can
use a |Sg|-type to hide the height data, giving us a type which
admits iterative construction.
%format T23 = "\F{Tree23}"
%format sort = "\F{sort}"
\begin{code}
  T23 = Sg Nat \ h -> <$ L $>23 h (bot / top)

  insert2 : P -> T23 -> T23
  insert2 p (h / t) with ins23 h <$ p $>io t
  ... | inl t'               = h     / t'
  ... | inr (lt \\ r \\ rt)  = su h  / no2 lt r rt

  sort : forall {F} -> MuJJ F P -> <$ L $>i+ (bot / top)
  sort = flattenIO o snd o foldr insert2 (ze / no0)
\end{code}


\section{Deletion from 2-3 Trees}

Might is right: the omission of \emph{deletion} from treatments of
balanced search trees is always a little unfortunate~\cite{might:delete}. Deletion is a
significant additional challenge because we can lose a key from the
\emph{middle} of the tree, not just from the \emph{fringe} of nodes
whose children are leaves. Insertion acts always to extend the fringe,
so the problem is only to bubble an anomaly up from the fringe to the root.
Fortunately, just as nodes and leaves alternate in the traversal of a tree,
so do middle nodes and fringe nodes: whenever we need to delete a middle
node, it always has a neighbour at the fringe which we can move into the
gap, leaving us once more with the task of bubbling a problem up from the
fringe.

Our situation is further complicated by the need to restore the
neighbourhood ordering invariant when one key is removed. At last, we
shall need our ordering to be transitive. We shall also need a
decidable equality on keys.

\begin{code}
  data _==_ {X : Set}(x : X) : X -> Set where
    it : x == x
  infix 6 _==_
\end{code}


%if False
\begin{code}
  module Delete23 (
\end{code}
%endif
\begin{code}
    trans : forall {x} y {z} -> L (x / y) => L (y / z) => <P L (x / z) P>
\end{code}
%if False
\begin{code}
    )(
\end{code}
%endif
\begin{code}
    eq? : (x y : P) -> x == y + (x == y -> Zero)
\end{code}
%if False
\begin{code}
    ) where
\end{code}
%endif

Correspondingly, a small amount of theorem proving is indicated, ironically,
to show that it is sound to throw information about local ordering away.

\paragraph{Transitivity for bounds.}
Transitivity we may readily lift to bounds with a key in the middle:
%format via = "\C{via}"
\begin{spec}
    pattern via p = p / ! / !
\end{spec}
%format transTB = "\F{trans}_{\F{\bot}}^{\F{\top}}"
\begin{code}
    transTB : [ (<^ L ^>P ^ <^ L ^>P) >> <^ L ^>P ]
    transTB {_     / top}   _         = !
    transTB {bot   / bot}   _         = !
    transTB {bot   / tb u}  _         = !
    transTB {top   / _}     (via _)   = magic
    transTB {tb l  / tb u}  (via p)   = trans p :- !
    transTB {tb l  / bot}   (via _)   = magic
\end{code}

\paragraph{What is the type of deletion?}
When we remove an element from a 2-3 tree of height $n$, the tree will
often stay the same height, but there will be situations in which it
must get shorter, becoming a 3-node or a leaf, as appropriate.

%format Del23 = "\F{Del}^{\F{23}}"
%format Short23 = "\F{Short}^{\F{23}}"
\begin{code}
    Del23 Short23 : Nat -> REL <$ P $>D
    Del23    h      lu  =  Short23 h lu + <$ L $>23 h lu
    Short23  ze     lu  =  Zero
    Short23  (su h) lu  =  <$ L $>23 h lu
\end{code}

The task of deletion has three phases: finding the key to delete;
moving the problem to the fringe; plugging a short tree into a tall hole.
The first of these will be done by our main function,
%format del23 = "\F{del}^{\F{23}}"
\[
  |del23 : forall {h} -> [ <$ L $>iI >> <$ L $>23 h >> Del23 h ]|
\]
and the second by extracting the extreme right key from a nonempty left subtree,
%format extr = "\F{extr}"
\[
  |extr :  forall {h} -> [ <$ L $>23 (su h) >> (Del23 (su h) ^ <$ L $>F) ]|
\]
recovering the (possily short) remainder of the tree and the evidence that the key
is below the upper bound (which will be the deleted key). Both of these operations
will need to reconstruct trees with one short subtree, so let us build `smart
constructors' for just that purpose, then return to the main problem.

\paragraph{Rebalancing reconstructors.}
%format Re2 = "\F{Re2}"
%format d2t = "\F{d2t}"
%format t2d = "\F{t2d}"
%format rd = "\F{rd}"
If we try to reconstruct a 2-node with a possibly-short subtree, we might
be lucky enough to deliver a 2-node, or we might come up short. We certainly
will not deliver a 3-node of full height and it helps to reflect that in
the type. Shortness can be balanced out if we are adjacent to a 3-node, but if we
have only a 2-node, we must give a short answer.
\begin{code}
    Re2 :  Nat -> REL <$ P $>D
    Re2 h =  Short23 (su h) -+- (<$ L $>23 h ^ <$ L $>23 h)

    d2t :  forall {h} -> [ (Del23 h ^ <$ L $>23 h) >> Re2 h ]
    d2t {h}     (inr lp  \\ p \\ pu)           = inr (lp \\ p \\ pu)
    d2t {ze}    (inl ()  \\ p \\ pu)
    d2t {su h}  (inl lp  \\ p \\ no2 pq q qu)  = inl (no3 lp p pq q qu)
    d2t {su h}  (inl lp  \\ p \\ no3 pq q qr r ru)
      = inr (no2 lp p pq \\ q \\ no2 qr r ru)

    t2d :  forall {h} -> [ (<$ L $>23 h ^ Del23 h) >> Re2 h ]
    t2d {h}     (lp \\ p \\ inr pu)           = inr (lp \\ p \\ pu)
    t2d {ze}    (lp \\ p \\ inl ())
    t2d {su h}  (no2 ln n np \\ p \\ inl pu)  = inl (no3 ln n np p pu)
    t2d {su h}  (no3 lm m mn n np  \\ p \\ inl pu)
      = inr (no2 lm m mn \\ n \\ no2 np p pu)

    rd : forall {h} -> [ Re2 h >> Del23 (su h) ]
    rd (inl s)                = (inl s)
    rd (inr (lp \\ p \\ pu))  = inr (no2 lp p pu)
\end{code}
The adaptor |rd| allows us to throw away the knowledge that the full
height reconstruction must be a 2-node if we do not need it, but the
extra detail allows us to use 2-node reconstructors in the course of
3-node reconstruction.  To reconstruct a 3-node with one
possibly-short subtree, rebuild a 2-node containing the suspect, and
then restore the extra subtree. We thus need to implement the latter.

%format r3t = "\F{r3t}"
%format t3r = "\F{t3r}"
\begin{code}
    r3t :  forall {h} -> [ (Re2 h ^ <$ L $>23 h) >> Del23 (su h) ]
    r3t (inr (lm \\ m \\ mp) \\ p \\ pu)    = inr (no3 lm m mp p pu)
    r3t (inl lp \\ p \\ pu)                 = inr (no2 lp p pu)

    t3r :  forall {h} -> [ (<$ L $>23 h ^ Re2 h) >> Del23 (su h) ]
    t3r (lp \\ p \\ inr (pq \\ q \\ qu))    = inr (no3 lp p pq q qu)
    t3r (lp \\ p \\ inl pu)                 = inr (no2 lp p pu)
\end{code}

\paragraph{Cutting out the extreme right.}
We may now implement |extr|, grabbing the rightmost key from a tree. I use
%format -\ = "\C{\bigtriangleup\!\!\!\!_{\not\;}}"
%format _-\_ = _ -\ _
\begin{spec}
    pattern _-\_ lr r = r / lr / !
\end{spec}
to keep the extracted element on the right and hide the ordering proofs.
\begin{code}
    extr : forall {h} -> [ <$ L $>23 (su h) >> (Del23 (su h) ^ <^ L ^>P) ]
    extr {ze} (no2 lr r no0)        = inl lr -\ r
    extr {ze} (no3 lp p pr r no0)   = inr (no2 lp p pr) -\ r
    extr {su h} (no2 lp p pu)       with extr pu
    ... | pr -\ r = rd (t2d (lp \\ p \\ pr)) -\ r
    extr {su h} (no3 lp p pq q qu)  with extr qu
    ... | qr -\ r = t3r (lp \\ p \\ t2d (pq \\ q \\ qr)) -\ r
\end{code}

To delete the pivot key from between two trees, we extract the rightmost key
from the left tree, then weaken the bound on the right tree
(traversing its left spine only). Again, we are sure that if the height
remains the same, we shall deliver a 2-node.
%format delp = "\F{delp}"
%format weak = "\F{weak}"
\begin{code}
    delp : forall {h} -> [ (<$ L $>23 h ^ <$ L $>23 h) >> Re2 h ]
    delp {ze}    {lu}  (no0 \\ p \\ no0) = transTB {lu} (via p) :- inl no0
    delp {su h}        (lp \\ p \\ pu) with extr lp
    ... | lr -\ r = d2t (lr \\ r \\ weak pu) where
      weak : forall {h u} -> <$ L $>23 h (tb p / u) -> <$ L $>23 h (tb r / u)
      weak {ze} {u}  no0 = transTB {tb r / u} (via p) :- no0
      weak {su h} la pq \\ q \\ qu ra = la weak pq \\ q \\ qu ra
\end{code}

\paragraph{A remark on weakenings.}  It may seem regrettable that we
have to write |weak|, which is manifestly an obfuscated identity
function, and programmers who do not wish the ordering guarantees are
entitled not to pay and not to receive. If we took an extrinsic
approach to managing these invariants, |weak| would still be present,
but it would just be the proof of the proposition that you can lower a
lower bound that you know for a tree. Consequently, the truly
regrettable thing about |weak| is not that it is written but that it
is \emph{executed}. The `colored' analysis of Bernardy and Moulin
offers a suitable method to ensure that the weakening operation
belongs to code which is erased at run
time~\cite{DBLP:conf/icfp/BernardyM13}. An alternative might be
a notion of `propositional subtyping', allowing us to establish
coercions between types which are guaranteed erasable at runtime because all
they do is fix up indexing and the associated content-free proof objects.

\paragraph{The completion of deletion.}
Now that we can remove a key, we need only find the key to remove. I
have chosen to delete the topmost occurrence of the given key, and to
return the tree unscathed if the key does not occur at all.
\begin{code}
    del23 : forall {h} -> [ <$ L $>iI >> <$ L $>23 h >> Del23 h ]
    del23 {ze}   _           no0                  = inr no0
    del23 {su h} <$ y $>io   la lp \\ p \\ pu ra  with eq? y p
    del23 {su h} <$ .p $>io  (no2 lp p pu)        | inl it
      = rd (delp (lp \\ p \\ pu))
    del23 {su h} <$ .p $>io  (no3 lp p pq q qu)   | inl it
      = r3t (delp (lp \\ p \\ pq) \\ q \\ qu)
    del23 {su h} <$ y $>io   la lp \\ p \\ pu ra  | inr _ with owoto y p
    del23 {su h} <$ y $>io   (no2 lp p pu)        | inr _ | le
      = rd (d2t (del23 <$ y $>io lp \\ p \\ pu))
    del23 {su h} <$ y $>io   (no2 lp p pu)        | inr _ | ge
      = rd (t2d (lp \\ p \\ del23 <$ y $>io pu))
    del23 {su h} <$ y $>io   (no3 lp p pq q qu)   | inr _ | le
      = r3t (d2t (del23 <$ y $>io lp \\ p \\ pq) \\ q \\ qu)
    del23 {su h} <$ y $>io   (no3 lp p pq q qu)   | inr _ | ge with eq? y q
    del23 {su h} <$ .q $>io  (no3 lp p pq q qu)   | inr _ | ge | inl it
      = t3r (lp \\ p \\ delp (pq \\ q \\ qu))
    ... | inr _ with owoto y q
    ... | le = r3t (t2d (lp \\ p \\ del23 <$ y $>io pq) \\ q \\ qu)
    ... | ge = t3r (lp \\ p \\ t2d (pq \\ q \\ del23 <$ y $>io qu))
\end{code}

As with insertion, the discipline of indexing by bounds and height is quite
sufficient to ensure that rebalancing works as required. The proof effort
is just to reestablish the local ordering invariant around the deleted
element.

At no point did we need to construct trees with the invariant broken.
Rather, we chose types which expressed with precision the range of possible
imbalances arising from a deletion. It is exactly this precision which allowed
us to build and justify the rebalancing reconstruction operators we reused so
effectively to avoid an explosion of cases.


\section{Discussion}

We have seen \emph{intrinsic} dependently typed
programming at work. Internalizing ordering and balancing invariants to
our datatypes, we discovered not an explosion of proof obligations,
but rather that unremarkable programs check at richer
types because they \emph{accountably} do the testing which
justifies their choices.

Of course, to make the programs fit neatly into the types, we must take
care of how we craft the latter. I will not pretend for one moment that
the good definition is the first to occur to me, and it is certainly the
case that one is not automatically talented at designing dependent types,
even when one is an experienced programmer in Haskell or ML. There is a
new skill to learn. Hopefully, by taking the time to explore the design
space for ordering invariants, I have exposed some transferable lessons.
In particular, we must overcome our type inference training and learn to
see types as pushing requirements inwards, as well as pulling guarantees
out.

It is positive progress that work is shifting from the program definitions
to the type definitions, cashing out in our tools as considerable
mechanical assistance in program construction. A precise type structures
its space of possible programs so tightly that an ineractive editor can
often offer us a small choice of plausible alternatives, usually including
the thing we want. It is exhilarating being drawn to one's code by the
strong currents of a good design. But that happens only in the last
iteration: we are just as efficiently dashed against the rocks by a bad
design, and the best tool to support recovery remains, literally, the
drawing board. We should give more thought to machine-assisted exploration.

A real pleasure to me in doing this work was the realisation that I
not only had `a good idea for ordered lists' and `a good idea for
ordered trees', but that they were the \emph{same} idea, and moreover that
I could implement the idea in a datatype-generic manner. The key underpinning
technology is first-class datatype description. By the end of the paper,
we had just one main datatype |MuIO|, whose sole role was to `tie the knot'
in a recursive node structure determined by a computable code. The resulting
raw data are strewn with artefacts of the encoding, but pattern synonyms
do a remarkably good job of recovering the appearance of bespoke constructors
whenever we work specifically to one encoded datatype.

Indeed, there is clearly room for even more datatype-generic
technology in the developments given here. On the one hand, the
business of finding the substructure in which a key belongs, whether
for insertion or deletion, is crying out for a generic construction of
G\'erard Huet's `zippers'~\cite{huet:zipper}.  Moreover, the treatment
of ordered structures as variations on the theme of the binary search
tree demands consideration in the framework of `ornaments', as studied
by Pierre-\'Evariste Dagand and others~\cite{DBLP:conf/icfp/DagandM12}.
Intuitively, it seems likely that the |IO| universe corresponds closely
to the ornaments on node-labelled binary trees which add only finitely
many bits (because |IO| has |q+| rather than a general |Sg|). Of course,
one node of a |MuIO| type corresponds to a region of nodes in a tree:
perhaps ornaments, too, should be extended to allow the unrolling of
recursive structure.

Having developed a story about ordering invariants to the extent that
our favourite sorting algorithms silently establish them, we still do
not have total correctness intrinsically. \emph{What about permutation?}
It has always maddened me that the insertion and flattening operations
manifestly construct their output by rearranging their input: the proof
that sorting permutes should thus be \emph{by inspection}. Experiments
suggest that many sorting algorithms can be expressed in a
domain specific language whose type system is linear for keys. We should
be able to establish a general purpose permutation invariant for this
language, once and for all, by a logical relations argument. We are used
to making sense of programs, but it is we who make the sense, not the
programs. It is time we made programs make their own sense.


\bibliographystyle{plainnat} % basic style, author-year citations
\bibliography{Ornament} % name your BibTeX data base

\end{document}