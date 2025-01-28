{-# OPTIONS --cubical --allow-unsolved-metas #-}
module EilenbergSteenrod.Utils where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatMinusOne

open import Cubical.HITs.Sn
open import Cubical.HITs.Susp

isoΣ⊥-Bool : Iso (Susp ⊥) Bool
isoΣ⊥-Bool = {! !}

isoSS⁻ : (n : ℕ) → Iso (S (-1+ n)) (S⁻ n)
isoSS⁻ zero = idIso
isoSS⁻ (suc zero) = isoΣ⊥-Bool
isoSS⁻ (suc (suc n)) = {! !}
