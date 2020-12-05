{-# OPTIONS --without-K --safe #-}

module AOC20.Solution.Day5 where

open import AOC20.Conversions
open import AOC20.List hiding (intersperse)

open import Data.Bool
open import Data.Char renaming (_≟_ to _≟ᶜ_)
open import Data.Maybe renaming (map to maybeMap; zipWith to zipWithM)
open import Data.Maybe.Properties renaming (≡-dec to ≡-maybe≡)
open import Data.Nat renaming (_≟_ to _≟ⁿ_)
open import Data.Product renaming (map to Σ-map)
open import Data.String

open import Function

open import Level hiding (_⊔_; suc)

open import Relation.Nullary

isEqBin : Char → Char → Char → Maybe ℕ
isEqBin z o c with does (z ≟ᶜ c)
... | true  = just 0
... | false   with does (o ≟ᶜ c)
... | true  = just 1
... | false = nothing

toBinary : (Char → Maybe ℕ) → List Char → Maybe ℕ
toBinary f = (_>>= toBaseℕR 2) ∘ maybeList ∘ map f

calcSeat : {ℓ : Level} {A : Set ℓ} → (ℕ → ℕ → A) → List Char → Maybe A
calcSeat f = uncurry (zipWithM f) ∘
             Σ-map (toBinary (isEqBin 'F' 'B'))
                   (toBinary (isEqBin 'L' 'R')) ∘
             partitionⁿ 7

seatID : ℕ → ℕ → ℕ
seatID r c = 8 * r + c

Part1 : String → String
Part1 = showℕ ∘ foldr (maybe′ _⊔_ id) 0 ∘
        map (calcSeat seatID) ∘ lines ∘ toList

Part2 : String → String
Part2 = maybe′ showℕ "nothing" ∘ (_>>= id) ∘ (_>>= head) ∘ tail ∘
        derun (≡-maybe≡ _≟ⁿ_ ∘ maybeMap suc) ∘
        difference (≡-maybe≡ _≟ⁿ_) (applyUpTo just 1023) ∘
        map (calcSeat seatID) ∘ lines ∘ toList
