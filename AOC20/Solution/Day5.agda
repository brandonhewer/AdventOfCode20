{-# OPTIONS --without-K --safe #-}

module AOC20.Solution.Day5 where

open import AOC20.Conversions
open import AOC20.List hiding (intersperse)

open import Data.Char renaming (_≟_ to _≟ᶜ_)
open import Data.Maybe renaming (map to maybeMap; zipWith to zipWithM)
open import Data.Maybe.Properties renaming (≡-dec to ≡-maybe≡)
open import Data.Nat renaming (_≟_ to _≟ⁿ_)
open import Data.String

open import Function

open import Relation.Nullary

binCodes : Char → Maybe ℕ
binCodes 'F' = just 0
binCodes 'B' = just 1
binCodes 'L' = just 0
binCodes 'R' = just 1
binCodes  _  = nothing

toBinary : (Char → Maybe ℕ) → List Char → Maybe ℕ
toBinary f = maybeMap (toBaseℕL 2) ∘ maybeList ∘ map f

Part1 : String → String
Part1 = showℕ ∘ foldr (maybe′ _⊔_ id) 0 ∘
        map (toBinary binCodes) ∘ lines ∘ toList

Part2 : String → String
Part2 = maybe′ showℕ "nothing" ∘ (_>>= id) ∘ (_>>= head) ∘ tail ∘
        derun (≡-maybe≡ _≟ⁿ_ ∘ maybeMap suc) ∘
        difference (≡-maybe≡ _≟ⁿ_) (applyUpTo just 1023) ∘
        map (toBinary binCodes) ∘ lines ∘ toList
