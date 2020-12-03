{-# OPTIONS --without-K --sized-types --guardedness #-}

module AOC20.Colist where

open import Codata.Musical.Colist public
open import Codata.Musical.Notation
open import Codata.Musical.Stream as S

open import Codata.Stream as S′ renaming (cycle to scycle)

open import Data.List
open import Data.List.NonEmpty

open import Function

open import Level

private
  variable
    ℓ₁ : Level
    A : Set ℓ₁

cycle : List⁺ A → Colist A
cycle = toColist ∘ S.toMusical ∘ S′.cycle
