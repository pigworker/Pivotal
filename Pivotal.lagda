\documentclass[]{sigplanconf}                    % onecolumn (standard format)

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

\title{How to Keep Your Neighbours in Order}
\authorinfo{Conor McBride}
           {University of Strathclyde}
           {Conor.McBride@@strath.ac.uk}

\begin{document}
\maketitle

\begin{abstract} 
\end{abstract}

%if False
\begin{code}

module Pivotal where

\end{code}
%endif


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

\section{Preliminaries}

%format pattern = "\mathkw{pattern}"
%format constructor = "\mathkw{constructor}"
%format One = "\D{1}"
%format it = "\C{\langle\rangle}"
%format + = "\D{+}"
%format _+_ = "\_\!" + "\!\_"
%format inl = "\C{inl}"
%format inr = "\C{inr}"
%format Sg = "\D{\Upsigma}"
%format * = "\F{\times}"
%format _*_ = "\_\!" * "\!\_"
%format / = "\C{,}"
%format _/_ = "\_\!" / "\!\_"
%format fst = "\F{\uppi_1}"
%format snd = "\F{\uppi_2}"
%format Zero = "\D{0}"
%format Two = "\D{2}"
%format tt = "\C{t\!t}"
%format ff = "\C{f\!f}"
%format forall = "\D{\forall}"

\begin{code}
data Zero : Set where

record One : Set where constructor it
\end{code}

\begin{code}
data Two : Set where tt ff : Two
\end{code}

\begin{code}
data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T
infixr 4 _+_
\end{code}

\begin{code}
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _/_
  field
    fst : S
    snd : T fst
open Sg
infixr 5 _/_

_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 5 _*_
\end{code}


\section{Searching for Search Trees}

\textbf{Throw in a few painful variations, then discover loose bounds.}

We can extend any type with top and bottom elements as follows.

%format (TB x) = x "\D{\!_\bot^\top}"
%format tb = "\C{\scriptscriptstyle{\#}}"
%format top = "\C{\top}"
%format bot = "\C{\bot}"

\begin{code}
data TB (P : Set) : Set where
  top  :       (TB P)
  tb   : P ->  (TB P)
  bot  :       (TB P)
\end{code}

Of course, we shall need to extend the order, putting |top| at the
top and |bot| at the bottom.

%format REL = "\F{Rel}"
%format TBR r = r "\F{\!_\bot^\top}"
\begin{code}
REL : Set -> Set1
REL P = P -> P -> Set

TBR : forall {P} -> REL P -> REL (TB P)
TBR L x       top     = One
TBR L (tb x)  (tb y)  = L x y
TBR L bot     y       = One
TBR L _       _       = Zero
\end{code}

\textbf{Use |Two| here?}

\section{One Way Or The Other}

\textbf{In which we learn to present the \emph{totality} of the order,
rather than its \emph{decidability}.}


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
%format MuJJ = "\D{\upmu_{" JJ "}}"
%format la = "\C{\langle}"
%format ra = "\C{\rangle}"
%format la_ra = la "\_" ra

\begin{code}

data JJ : Set where
  qR qP q1   : JJ
  _q+_ _q*_  : JJ -> JJ -> JJ
infixr 4 _q+_
infixr 5 _q*_

ElJJ : JJ -> Set -> Set -> Set
ElJJ qR        R P = R
ElJJ qP        R P = P
ElJJ q1        R P = One
ElJJ (S q+ T)  R P = (ElJJ S) R P + (ElJJ T) R P
ElJJ (S q* T)  R P = (ElJJ S) R P * (ElJJ T) R P

data MuJJ (F : JJ)(P : Set) : Set where
  la_ra : (ElJJ F) (MuJJ F P) P -> MuJJ F P

\end{code}

The |qR| stands for `recursive substructure' and the |qP| stands for
`parameter'---the type of elements stored in the container. When we
`tie the knot' in |MuJJ F P|, we replace interpret |F|'s |qP|s by some
actual |P| and its |qR|s by |MuJJ F P|.


\section{The Simple Orderable Universe}

%format SO = "\D{SO}"
%format ElSO = "\F{\llbracket\_\rrbracket_{" SO "}}}"
%format (ElSO (t)) = "\F{\llbracket}" t "\F{\rrbracket_{" SO "}}"
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
|JJ| picked out as the image of a function, |ElSO|. Now, |P| stands also for
pivot!

\begin{code}
data SO : Set where
  qR q1      : SO
  _q+_ _q^_  : SO -> SO -> SO
infixr 5 _q^_

ElSO : SO -> JJ
ElSO qR        = qR
ElSO q1        = q1
ElSO (S q+ T)  = (ElSO S) q+ (ElSO T)
ElSO (S q^ T)  = (ElSO S) q* qP q* (ElSO T)

MuSO : SO -> Set -> Set
MuSO F P = MuJJ (ElSO F) P
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
%format go = "\F{go}"
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
  go : forall G -> (ElJJ (ElSO G)) (MuSO F P) P -> MuSO qTreeSO P
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

\textbf{draw a diagram, showing a tree projected onto a line}

We are now in a position to roll out the ``loose bounds'' method to
the whole of the |SO| universe. We need to ensure that each pivot is
in order with its neighbours and with the outer bounds, and the
alternating leaf/pivot structure gives us just what we need: let us store
the ordering evidence at the leaves!

%format MuOSO = "\F{\upmu^\le_{" SO "}}"
%format ElOSO = "\F{\llbracket\_\rrbracket^\le_{" SO "}}}"
%format (ElOSO (t)) = "\F{\llbracket}" t "\F{\rrbracket^\le_{" SO "}}"
%if False
\begin{code}
pattern SHUNT X = X
\end{code}
%endif
%format SHUNT = "\hspace*{0.5in}"
\begin{code}
ElOSO : SO -> forall {P} -> REL (TB P) -> REL P -> REL (TB P)
ElOSO qR        R L l u = R l u
ElOSO q1        R L l u = (TBR L) l u
ElOSO (S q+ T)  R L l u = (ElOSO S) R L l u + (ElOSO T) R L l u
ElOSO (S q^ T)  R L l u = Sg _ \ p ->
  SHUNT (ElOSO S) R L l (tb p) * (ElOSO T) R L (tb p) u

data MuOSO  (F : SO){P : Set}(L : REL P)
            (l u : (TB P)) : Set where
  la_ra : (ElOSO F) (MuOSO F L) L l u -> MuOSO F L l u
\end{code}
We have shifted from sets to relations, in that our types are indexed
by lower and upper bounds. The leaves demand evidence that the bounds
are in order, whilst the nodes require the pivot first, then use it to
bound the substructures appropriately. I promise that I shall never name
the evidence: I shall always match it with the |_| pattern and construct
it by means of the following device, making use of \emph{instance arguments}:

%format ! = "\F{\scriptstyle{!}}"
\begin{code}
! : forall {X : Set}{{x : X}} -> X
! {X}{{x}} = x
\end{code}

When we use |!| at type |X|, Agda treats the |x| as an implicit argument,
but rather than solving for |x| by \emph{unification}, Agda
seeks an \emph{assumption} of type |X| in the context, succeeding if there
is exactly one.

Meanwhile, the need in nodes to bound the left substructure's type
with the pivot value disrupts the left-to-right spatial ordering of the
data, but we can apply a little cosmetic treatment, thanks to the
availability of \emph{pattern synonyms}~\cite{aitken.reppy}.

%format \\ = "\C{\raisebox{ -0.07in}[0in][0in]{`}}"
%format _\\_\\_ = "\_\!" \\ "\!\_" \\ "\!\_"
\begin{code}
pattern _\\_\\_ s p t = p / s / t
infixr 5 _\\_\\_ 
\end{code}

%format treeOSO = "\F{tree}"
With these two devices available, let us check that we can still turn
any ordered data into an ordered tree.
\begin{code}
treeOSO :  forall {P F}{L : REL P}{l u} ->
           MuOSO F L l u                -> MuOSO qTreeSO L l u
treeOSO {P}{F}{L} la f ra = go F f where
  go : forall G {l u}  ->
           (ElOSO G) (MuOSO F L) L l u  -> MuOSO qTreeSO L l u
  go qR        f              = treeOSO f
  go q1        _              = la inl ! ra
  go (S q+ T)  (inl s)        = go S s
  go (S q+ T)  (inr t)        = go T t
  go (S q^ T)  (s \\ p \\ t)  = la inr (go S s \\ p \\ go T t) ra
\end{code}


\bibliographystyle{plainnat}      % basic style, author-year citations
\bibliography{Ornament}   % name your BibTeX data base

\end{document}