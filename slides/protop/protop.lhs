%include setup.fmt

\usepackage{tikz-cd}
\usepackage{MnSymbol}
\usepackage{mathtools}

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
\date{2017-10-13}

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
%endif

\begin{document}

\maketitle

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
The category $\set$ of \alert{sets} (and total functions)
is an elementary topos:
\begin{itemize}
\item
    \vspace{-1mm}
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
    \vspace{-1mm}
    Exponentials are \alert{sets of functions}
    \[
        N^M
        :=
        \bigl\{
            f:M\rightarrow N
        \bigr\}.
    \]
\item
    \vspace{-1mm}
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
\pause
If we can prove that the outer diagram commutes,
then the red morphism must exist.

\pause
Computationally, this means that our interpreter must be able to
\alert{compute the predecessor} of $42$ in our model.
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
    \ar[loop left, "|reflexivity p|"]
    \ar[r, bend left, "|p|"]
    \ar[rr, bend right=50, "|transitivity p q|"'] &
    |setRhs p=setLhs q|
    \ar[r, bend left, "|q|"]
    \ar[l, bend left, "|symmetry p|"] &
    |setRhs q|
\end{tikzcd}
\]
\end{frame}

\begin{frame}{Functoids}
%if style/=newcode
%format Type = "\ty{Type}"
%format Functoid = "\ty{Functoid}"
%format Proxy = "\ty{Proxy}"
%format onPoints = "\id{onPoints}"
%format onProofs = "\id{onProofs}"
%endif
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
\end{frame}

\begin{frame}{Objects}
%if style/=newcode
%format IsObject = "\cl{IsObject}"
%format Domain = "\ty{Domain}"
%format proxy = "\ty{proxy}"
%endif
> class ( Show x
>       , Typeable x
>       , IsSetoid (Domain x)
>       ) => IsObject x where
>
>     type Domain x
>
>     proxy :: Proxy x -> x
\end{frame}

\begin{frame}{Morphisms}
%if style/=newcode
%format IsMorphism = "\cl{IsMorphism}"
%format Source = "\ty{Source}"
%format DSource = "\ty{DSource}"
%format Target = "\ty{Target}"
%format DTarget = "\ty{DTarget}"
%format onDomains = "\id{onDomains}"
%format proxy' = "\id{proxy\textquotesingle}"
%endif
> class ( Show a
>       , Typeable a
>       , IsObject (Source a)
>       , IsObject (Target a)
>       ) => IsMorphism a where
>
>     type Source a
>     type Target a
>
>     onDomains  :: a
>                -> Functoid (DSource a) (DTarget a)
>     proxy'     :: Proxy a -> a
>
> type DSource f = Domain (Source f)
> type DTarget f = Domain (Target f)
\end{frame}

\end{document}
