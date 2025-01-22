{-

Please do not move this file. Changes should only be made if necessary.

This file contains pointers to the code examples and main results from
the paper:



-}

-- The "--safe" flag ensures that there are no postulates or unfinished goals
{-# OPTIONS --safe #-}
module Cubical.cellular-main.paper where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

open import Cubical.cellular-main.Hurewicz.Map


fundamentalTheoremOfSyntheticMathemaics : 5 + 7 ≡ 12
fundamentalTheoremOfSyntheticMathemaics = refl
