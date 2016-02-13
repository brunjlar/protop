# protop - topos programming

This has been an on- and off project of mine for more than a decade. I used to
think about it day and night for a couple of days until I hit another wall, then
forgot about it for months or even years.

I have tried to program it - with more or less success - in Java, Python, C#,
Common Lisp and Haskell.

Now, finally, using all I had recently learnt about some of the more exotic
extensions to the Haskell type system, I managed to get a first prototype
working.

## Goal

The idea is to model an [elementary topos](https://en.wikipedia.org/wiki/Topos)
in Haskell, so that objects and morphisms in the topos correspond to Haskell
types and functions between those types.

A *topos* is a category with

- all finite limits, i.e.
    - a terminal object,
    - finite products,
    - equalizers,
- exponentials
- and a subobject-classifier.

Additionally, I want a *natural number object* to have at least one infinite
object. Without such an object, we would get the topos of all finite sets, which
is pretty boring. *With* a natural number object, on the other hand, we not only
get natural numbers, but all sorts of interesting object: the (constructible)
reals, differentiable functions, vector spaces... - a big chunk of all the
interesting objects being studied in mathematics.

## from Cartesian Closed Categories...

If we drop the conditions of having equalizers and a subobject-classifier,
we arrive at the notion of a
[cartesian closed category](https://en.wikipedia.org/wiki/Cartesian_closed_category).

Such categories can be modelled easily in Haskell (and indeed in any language
with first-class function types):

- The terminal object is the type `()`,
- the product of two objects `a` and `b` is the type of pairs `(a,b)`,
- and the exponential from `a` to `b` is the function type `a -> b`.

Adding *equalizers* is sligthly more difficult (as a reminder: the *equalizer*
of two morphisms `f` and `g` from `X` to `Y` is the largest subobject
of `X` on which `f` and `g` agree), but can for example be done by simply
using `X` instead of a subobject of `X` and "forgetting" the proof that `f` and
`g` agree.

## ...to Topoi

The *really* tricky part for me was to figure out how to model the
subobject-classifier *Omega*, which is characterized by the fact that there
is a one-to-one correspondence between *subobjects* of `X` and morhphisms
from `X` to `Omega`. In particular that means that if we have a monomorphism
(i.e. an injection) of `Y` into `X`, corresponding to a morphism from `X` to
`Omega`, and if we have a point `x` in `X` (a morphism from the terminal
object to `X`) of which we know that it maps to *true* in `Omega`, then we
must be able to find the unique point `y` in `Y` that maps to `x`.

We know such a `y` must exist, but in order to really model our morphisms as
functions between Haskell types, we have to be able to *compute* `y` from x.

This is obviously impossible if we ignore proofs. Only by analyzing *how* we
know that `x` maps to *true* can we hope to discover the correct `y`.

So my approach in this library is to "bake" proofs into all the types and to
keep careful track of them in order to be able to model all topos morphisms
as functions.
