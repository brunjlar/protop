-- | In this module, we model an /elementary topos/ with Haskell types
-- (see <https://en.wikipedia.org/wiki/Topos>).
-- To be more precise, we model the "smallest elementary topos with a
-- natural number object". Without such a natural number object,
-- the resulting topos would be boring, consisting merely of the finite
-- sets. By adding one infinite object, namely the natural numbers, we
-- get access to all sorts of interesting objects - rational numbers,
-- (constructible) real numbers, differentiable functions, a big chunk of
-- all those objects that are studied in mathematics.
module Protop.Core
    ( module Protop.Core.Compositions
    , module Protop.Core.Equalizers
    , module Protop.Core.Exponentials
    , module Protop.Core.Identities
    , module Protop.Core.Monos
    , module Protop.Core.Morphisms
    , module Protop.Core.Natural
    , module Protop.Core.Objects
    , module Protop.Core.Omega
    , module Protop.Core.Products
    , module Protop.Core.Proofs
    , module Protop.Core.Reflexivities
    , module Protop.Core.Setoids
    , module Protop.Core.Symmetries
    , module Protop.Core.Transitivities
    , module Protop.Core.Terminal
    ) where

import Protop.Core.Compositions
import Protop.Core.Equalizers
import Protop.Core.Exponentials
import Protop.Core.Identities
import Protop.Core.Monos
import Protop.Core.Morphisms
import Protop.Core.Natural
import Protop.Core.Objects
import Protop.Core.Omega
import Protop.Core.Products
import Protop.Core.Proofs
import Protop.Core.Reflexivities
import Protop.Core.Setoids
import Protop.Core.Symmetries
import Protop.Core.Transitivities
import Protop.Core.Terminal
