%include setup.fmt

\usepackage{tikz-cd}
\usepackage{MnSymbol}
\usepackage{mathtools}

\usetikzlibrary{decorations.pathmorphing}

\newcommand\cat[1]{\mathcal{#1}}
\newcommand\catc{\cat{C}}
\newcommand\catt{\cat{T}}
\newcommand\set{\underline{\mathrm{Set}}}
\newcommand\eql[2]{\mathrm{Eq}_{#1,#2}}
\newcommand\eq[2]{\mathrm{eq}_{#1,#2}}
\newcommand\rec[2]{\mathrm{rec}_{#1,#2}}
\newcommand\bool{\mathbb{B}}
\newcommand\nat{\mathbb{N}}
\newcommand\true{\mathrm{true}}
\newcommand\false{\mathrm{false}}
\newcommand\zero{\mathrm{zero}}
\newcommand\suc{\mathrm{succ}}
\newcommand\hask{\underline{\mathrm{Hask}}}
\newcommand\dq[1]{``#1''}

\title{Protop - Dependent Types through Topoi}
\date{2018-09-20}

%if style /= newcode
%format === = "\ensuremath{=}"
%else
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE GADTs #-}
>
> import Data.Kind     (Type)
> import Data.Proxy    (Proxy)
> import Data.Typeable (Typeable)
>
> class Singleton a where
>     singleton :: a
%endif

\begin{document}

\maketitle

\begin{frame}{Motivation}
\begin{itemize}
    \item
        Using \emph{dependent types},
        it is possible to model large parts of mathematics
        in a computational way.
    \pause
    \item
        However, classical mathematics ist mostly formulated using
        \alert{set theory}, not type theory.
    \pause
    \item
        Many mathematical constructions use \alert{set comprehension},
        for example, defining a set as a subset of elements with
        a specified property.
    \pause
    \item
        It would be nice to be able to model mathematics in a style
        closer to what mathematicians are used to.
    \pause
    \item
        Many set-theoretic constructions can be done in any
        \alert{elementary topos}.
\end{itemize}
\end{frame}

\section{Elementary Topoi}

\begin{frame}{Topos}
An \alert{elementary topos}
is a category $\catt$ with the following properties:
\begin{overprint}
\onslide<1>
\begin{itemize}
\item
    $\catt$ has \alert{finite limits}.
\item
    $\catt$ has \alert{exponentials}.
\item
    $\catt$ has a \alert{subobject classifier}.
\end{itemize}
\onslide<2>
\begin{itemize}
\item
    $\catt$ has finite limits.
    \begin{itemize}
        \item
            $\catt$ has a \alert{terminal object}.
        \item
            $\catt$ has \alert{(finite) products}.
        \item
            $\catt$ has \alert{equalizers}.
    \end{itemize}
\item
    $\catt$ has \alert{exponentials}.
\item
    $\catt$ has a \alert{subobject classifier}.
\end{itemize}
\end{overprint}
\end{frame}

\begin{frame}[fragile]{Equalizers}
Let $f,g:X\rightarrow Y$ be two morphisms in a category $\catc$.
Then an \alert{equalizer} of $f$ and $g$ in $\catc$
is an object $\eql{f}{g}$ in $\catc$,
together with a morphism $\eq{f}{g}:\eql{f}{g}\rightarrow X$,
which is \alert{universal} for the property
$f\circ\eq{f}{g}=g\circ\eq{f}{g}$:
\[
\begin{tikzcd}[row sep=huge, column sep=huge]
        T
        \ar[rd]
        \ar[d, red, "\exists!"'] \\
        {\eql{f}{g}}
        \ar[r, "\eq{f}{g}"'] &
        X
        \ar[r, shift left=1ex, "f"]
        \ar[r, shift right=1ex, "g"'] &
        Y &
\end{tikzcd}
\]
\pause
In $\set$, the equalizer of two functions
$f,g:M\rightarrow N$ is
\[
    \eql{f}{g}
    :=
    \bigl\{
        m\in M
        \bigm\mid
        f(m)=g(m)\in N
    \bigr\}.
\]
\end{frame}

\begin{frame}[fragile]{Monomorphisms}
In any category, a morphism $f:X\rightarrow Y$ is a
\alert{monmorphism} if for each pair of morphisms
$i,j:T\rightarrow X$ with $f\circ i=f\circ j$, we have $i=j$:
\[
\begin{tikzcd}[row sep=huge, column sep=huge]
    T
    \ar[rr, bend left=40, "f\circ i"]
    \ar[r, shift left=1ex, "i"]
    \ar[r, shift right=1ex, "j"']
    \ar[rr, bend right=40, "f\circ j"'] &
    X
    \ar[r, "f"] &
    Y &
\end{tikzcd}
\]
In $\set$, monomorphisms are exactly the \alert{injective functions}, i.e.
functions $f$ with $\forall x,y\in X: f(x)=f(y)\Rightarrow x=y$.
\end{frame}

\begin{frame}[fragile]{Elementary Characterization of Monomorphisms}
\small
In any category with fibre products, there is this nice equivalent
characterization of monomorphisms: A morphism $f:X\rightarrow Y$ is a
monomorphism iff the following diagram commutes:
\[
\begin{tikzcd}[row sep=huge, column sep=huge]
    X\times_YX
    \ar[d, "pr_1"'] 
    \ar[r, "pr_2"] &
    X
    \ar[d, "f"] \\
    X
    \ar[ur, equal]
    \ar[r, "f"'] &
    Y &
\end{tikzcd}
\]
\pause
In $\set$:
\[
    f(x_1)=f(x_2)
    \Rightarrow (x_1,x_2)\in X\times_YX
    \Rightarrow x_1=x_2.
\]
\pause
If it wasn't for this, being a monomorphism would be "rank 2" in Haskell.
\end{frame}

\begin{frame}[fragile]{Subobject classifiers}
Let $\catc$ be a category with terminal object $*$.
An object $\Omega$ in $\catc$,
together with a morphism
$\true:*\hookrightarrow\Omega$
is a \alert{subobject classifier}
if for all monomorphisms $m:Y\hookrightarrow X$,
there is a unique morphism $\chi_m$,
such that the following diagram is Cartesian:
\[
\begin{tikzcd}[row sep=huge, column sep=huge]
    Y
    \ar[r, "!_Y"]
    \ar[d, hookrightarrow, "m"']
    \ar[rd, phantom, "\Box"] &
    *
    \ar[d, hookrightarrow, "\true"] \\
    X
    \ar[r, red, "\exists!\chi_m"'] &
    \Omega
\end{tikzcd}
\]
\begin{overprint}
\onslide<1>
This means that $\true:*\hookrightarrow\Omega$
is an \alert{universal subobject} --
all subobjects in $\catc$ are pullbacks
of $\true$.
\onslide<2>
In $\set$, the subobject classifier is
\[
    \true:
    \{\true\}
    \longrightarrow
    \bool
    :=\bigl\{\true,\false\bigr\}.
\]
\onslide<3>
Subobject classifiers are closely related to the
\alert{comprehension axiom},
allowing definitions like
\[
    M:=\bigl\{n\in N\bigm\mid P(n)\bigr\}.
\]
\end{overprint}
\end{frame}

\begin{frame}{The topos of sets}
\footnotesize
The category $\set$ of \alert{sets} (and total functions)
is an elementary topos:
\begin{itemize}
\item
    \vspace{-2mm}
    $\set$ has finite limits:
    \begin{itemize}
        \item
            Any \alert{singleton set} $\{*\}$ is a terminal object.
        \item
            The product of sets $M$ and $N$
            is the \alert{Cartesian product} $M\times N$.
        \item
            The equalizer of two functions
            $f,g:M\rightarrow N$ is the set
            \[
                \eql{f}{g}
                :=
                \bigl\{
                    m\in M
                    \bigm\mid
                    f(m)=g(m)\in N
                \bigr\}.
            \]
    \end{itemize}
\item
    \vspace{-2mm}
    Exponentials are \alert{sets of functions}
    \[
        N^M
        :=
        \bigl\{
            f:M\rightarrow N
        \bigr\}.
    \]
\item
    \vspace{-2mm}
    Each \alert{two-element set},
    for example the set of \alert{Booleans}
    \[
        \bool:=\bigl\{\true,\false\bigr\}
    \]
    is a subobject classifier.
\end{itemize}
\end{frame}

\begin{frame}{$\hask$ is not a topos}
The category $\hask$ of Haskell types and (total) functions
is \alert{not} a topos:
\begin{itemize}
\item
    $\hask$ does \alert{not} have (all) finite limits:
    \begin{itemize}
        \item
            |()| is a terminal object in $\hask$.
        \item
            The product of types |a| and |b|
            is |(a,b)|.
        \item
            $\hask$ does \alert{not}
            have arbitrary equalizers.
    \end{itemize}
\item
    Exponentials are function types |a->b|.
\item
    $\hask$ does \alert{not} have a subobject classifier.
\end{itemize}
\end{frame}

\begin{frame}[fragile]{Natural numbers}
The category with one object $*$ and one morphism $1_*$
is a topos. In order to avoid boring cases like this,
we will always consider topoi with a \alert{natural number object}:

\pause
Let $\catc$ be a category with final object $*$.
A \alert{natural number object} in $\catc$
is a \alert{universal diagram}
$*\xrightarrow{\zero}\nat\xrightarrow{\suc}\nat$ in $\catc$:
\[
\begin{tikzcd}[row sep=huge, column sep=huge]
    *
    \ar[r, "z"]
    \ar[d, equal] &
    X
    \ar[r, "s"] &
    X \\
    *
    \ar[r, "\zero"'] &
    \nat
    \ar[u, red, "\exists!", "\rec{z}{s}"']
    \ar[r, "\suc"'] &
    \nat
    \ar[u, red, "\rec{z}{s}"']
\end{tikzcd}
\]
\end{frame}

\section{Protop}

\begin{frame}{The goal}
In order to do \dq{computational mathematics},
we want to achieve two things:
\begin{itemize}
    \pause
    \item
        Syntactically, we want to use and construct
        objects and morphism that are defined
        in \alert{every topos with natural number object},
        i.e. that only use the axioms of elementary topoi
        and natural number objects.
    \pause
    \item
        We want to \alert{interpret} the objects and morphisms
        thus constructed in a model that allows us to actually
        \alert{compute results}.
\end{itemize}
\pause
If successful, we can perform many of the constructions of classical
mathematics in a constructive, computational way.
\end{frame}

\begin{frame}[fragile]{The problem}
\scriptsize
In a topos $\catt$ with natural number object $\nat$,
consider the following situation as an example:
\[
\begin{tikzcd}[column sep=huge]
    \{42\}
    \ar[rrd, bend left, "!_{\{42\}}"]
    \ar[rd, red, "42\mapsto 41"]
    \ar[rdd, bend right, hookrightarrow] \\
    &
    \nat
    \ar[r, "!_{\nat}"]
    \ar[d, hookrightarrow, "\suc"']
    \ar[rd, phantom, "\Box"] &
    *
    \ar[d, hookrightarrow, "\true"] \\
    &
    \nat
    \ar[r, "\chi_{\suc}"'] &
    \Omega
\end{tikzcd}
\]
\begin{overprint}
\onslide<1>
If we can prove that the outer diagram commutes,
then the red morphism must exist.

\onslide<2>
If we can prove that the outer diagram commutes,
then the red morphism must exist.

Computationally, this means that our interpreter must be able to
\alert{compute the predecessor} of $42$ in our model.
\onslide<3>
\begin{block}{Note}
Equalizers are \emph{not} such a big problem - they could be implemented
by simply ignoring the extra information at runtime.
\end{block}
\end{overprint}
\end{frame}

\begin{frame}{Key idea}
In the example from the last slide,
we must first have proven \dq{somehow}
that the diagram commutes.

\pause
\dq{Somewhere} in that proof, we probably mentioned the number $41$.

\pause
The key idea is to \alert{take proofs seriously} --
make the information contained in proofs explicit
and give it computational content.
\end{frame}

\begin{frame}[fragile]{Setoids}
%if style/=newcode
%format Typeable = "\cl{Typeable}"
%format IsSetoid = "\cl{IsSetoid}"
%format Proofs = "\ty{Proofs}"
%format Proxy = "\ty{Proxy}"
%format reflexivity = "\id{reflexivity}"
%format symmetry = "\id{symmetry}"
%format transitivity = "\id{transitivity}"
%format setLhs = "\id{setLhs}"
%format setRhs = "\id{setRhs}"
%endif
\small
> class     (Typeable a, Typeable (Proofs a))
>       =>  IsSetoid a where
>
>    type Proofs a
>
>    reflexivity   :: a -> Proofs a
>    symmetry      :: Proxy a -> Proofs a -> Proofs a
>    transitivity  :: Proxy a -> Proofs a -> Proofs a
>                  -> Proofs a
>    setLhs        :: Proofs a -> a
>    setRhs        :: Proofs a -> a
\tiny
\vspace{-3mm}
\[
\begin{tikzcd}
    |setLhs p|
    \ar[loop left, Rightarrow, "|reflexivity p|"]
    \ar[r, bend left, Rightarrow, "|p|"]
    \ar[rr, bend right=50, Rightarrow, "|transitivity p q|"'] &
    |setRhs p=setLhs q|
    \ar[r, bend left, Rightarrow, "|q|"]
    \ar[l, bend left, Rightarrow, "|symmetry p|"] &
    |setRhs q|
\end{tikzcd}
\]
\end{frame}

\begin{frame}[fragile]{Functoids}
%if style/=newcode
%format Type = "\ty{Type}"
%format Functoid = "\ty{Functoid}"
%format Proxy = "\ty{Proxy}"
%format onPoints = "\id{onPoints}"
%format onProofs = "\id{onProofs}"
%endif
\footnotesize
> data Functoid :: Type -> Type -> Type where
>     Functoid  :: (IsSetoid a, IsSetoid b)
>               => (a -> b)
>               -> (Proofs a -> Proofs b)
>               -> Functoid a b
>
> onPoints :: Functoid a b -> a -> b
> onPoints (Functoid f _) = f
>
> onProofs :: Functoid a b -> Proofs a -> Proofs b
> onProofs (Functoid _ g) = g
\vspace{-5mm}
\[
\begin{tikzcd}[column sep=5cm]
    |x|
    \ar[r, "|onPoints|"]
    \ar[d, Rightarrow, "|p|"', ""{name=A}] &
    |y|
    \ar[d, Rightarrow, "|q|", ""'{name=B}] \\
    |x'|
    \ar[r, "|onPoints|"'] &
    |y'|
    \ar[from=A, to=B, red, squiggly, "|onProofs|"]
\end{tikzcd}
\]
\end{frame}

\begin{frame}{Objects}
%if style/=newcode
%format Singleton = "\cl{Singleton}"
%format IsObject = "\cl{IsObject}"
%format Domain = "\ty{Domain}"
%format proxy = "\ty{proxy}"
%endif
> class  ( Show x
>        , Typeable x
>        , IsSetoid (Domain x)
>        , Singleton x
>        ) => IsObject x where
>
>     type Domain x
\end{frame}

\begin{frame}{Morphisms}
%if style/=newcode
%format IsMorphism = "\cl{IsMorphism}"
%format Source = "\ty{Source}"
%format DSource = "\ty{DSource}"
%format PSource = "\ty{PSource}"
%format Target = "\ty{Target}"
%format DTarget = "\ty{DTarget}"
%format PTarget = "\ty{PTarget}"
%format onDomains = "\id{onDomains}"
%format proxy' = "\id{proxy\textquotesingle}"
%endif
\small
> class  ( Show f
>        , Typeable f
>        , IsObject (Source f)
>        , IsObject (Target f)
>        , Singleton f
>        ) => IsMorphism f where
>     type Source f
>     type Target f
>     onDomains :: f -> Functoid (DSource f) (DTarget f)
>
> type DSource f = Domain (Source f)
> type DTarget f = Domain (Target f)
> type PSource f = Proofs (DSource f)
> type PTarget f = Proofs (DTarget f)
\end{frame}

\begin{frame}{Proofs}
%if style/=newcode
%format IsProof = "\cl{IsProof}"
%format Lhs = "\ty{Lhs}"
%format Rhs = "\ty{Rhs}"
%format SOURCE = "\ty{SOURCE}"
%format TARGET = "\ty{TARGET}"
%format proof = "\id{proof}"
%format lhs = "\id{lhs}"
%format rhs = "\id{rhs}"
%format singleton = "\id{singleton}"
%endif
\tiny
> class  ( Show p
>        , Typeable p
>        , IsMorphism (Lhs p)
>        , IsMorphism (Rhs p)
>        , Source (Lhs p) ~ Source (Rhs p)
>        , Target (Lhs p) ~ Target (Rhs p)
>        , Singleton p
>        ) => IsProof p where
>     type Lhs p
>     type Rhs p
>     proof  :: p
>            -> Domain (SOURCE p)
>            -> Proofs (Domain (TARGET p))
>
> type SOURCE p  = Source (Lhs p)
> type TARGET p  = Target (Lhs p)
>
> lhs :: IsProof p => p -> Lhs p
> lhs _ = singleton
>
> rhs :: IsProof p => p -> Rhs p
> rhs _ = singleton
\end{frame}

\begin{frame}[fragile]{Proofs (cntd.)}
\tiny
\[
\begin{tikzcd}[column sep=40mm]
    |SOURCE p|
    \ar[r, bend left=15, "|lhs p|", ""'{name=A}]
    \ar[r, bend right=15, "|rhs p|"', ""{name=B}]
    \ar[from=A, to=B, Rightarrow, "|p|"] &
    |TARGET p| \\ \\ \\ \\
    &
    |Domain (TARGET p)| \\ \\
    |Domain (SOURCE p)|
    \ar[uur, "|onPoints $ onDomains $ lhs p|"]
    \ar[r, "|proof p|"]
    \ar[ddr, "|onPoints $ onDomains $ rhs p|"'] &
    |Proofs (Domain (TARGET p))|
    \ar[uu, "|setLhs|"']
    \ar[dd, "|setRhs|"] \\ \\
    &
    |Domain (TARGET p)|
\end{tikzcd}
\]
\end{frame}

\begin{frame}[fragile]{The Omega domain}
%if style/=newcode
%format OPoint = "\ty{OPoint}"
%format OProof = "\ty{OProof}"
%endif
\scriptsize
> data OPoint :: Type where
>     OPoint :: IsMorphism f => f -> DTarget f -> OPoint
>
> data OProof :: Type where
>     OProof  ::  (IsMorphism f, IsMorphism g)
>             =>  f -> g -> DTarget f -> DTarget g ->
>                 ((DSource f, PTarget f) -> (DSource g, PTarget g)) ->
>                 ((DSource g, PTarget g) -> (DSource f, PTarget f)) ->
>                 OProof
\normalsize
\begin{overprint}
\onslide<1>
\[
  \begin{tikzcd}
    Y
    \ar[d, "f"'] & &
    y
    \ar[d, mapsto, ""{name=A}] & &
    y'
    \ar[d, mapsto, ""'{name=B}]
    \ar[from=A, to=B, bend left, red]
    \ar[from=B, to=A, bend left, red] & &
    Y'
    \ar[d, "f'"] \\
    X
    \ar[r, no head, squiggly] &
    x &
    z
    \ar[l, Rightarrow] & &
    z'
    \ar[r, Rightarrow] &
    x' &
    X'
    \ar[l, no head, squiggly]
  \end{tikzcd}
\]
\onslide<2>
\[
  \begin{tikzcd}
    Y
    \ar[d, "f"'] & &
    y
    \ar[d, mapsto, ""{name=A}] & &
    *
    \ar[d, mapsto, ""'{name=B}]
    \ar[from=A, to=B, bend left, red]
    \ar[from=B, to=A, bend left, red] &
    \true &
    *
    \ar[d, "1_*"] \\
    X
    \ar[r, no head, squiggly] &
    x &
    z
    \ar[l, Rightarrow] & &
    *
    \ar[r, Leftrightarrow] &
    * &
    *
    \ar[l, no head, squiggly]
  \end{tikzcd}
\]
\end{overprint}
\end{frame}

\end{document}
