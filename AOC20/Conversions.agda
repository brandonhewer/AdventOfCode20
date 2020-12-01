{-# OPTIONS --without-K --safe #-}

module AOC20.Conversions where

open import AOC20.Digit
open import AOC20.List

open import Data.Bool
open import Data.Char
open import Data.Fin hiding (toℕ; fromℕ; _+_)
open import Data.Maybe hiding (map)
open import Data.Nat
open import Data.String
open import Data.Sum hiding (map)
open import Data.Product hiding (map)

open import Function

charToℕ : Char → Maybe ℕ
charToℕ c with isDigit c
... | false = nothing
... | true  = just (toℕ c ∸ toℕ '0')

toBaseℕ : ℕ → List ℕ → Maybe ℕ
toBaseℕ b ns with proj₂ (mapAccumL (λ s n → b * s , s * n) 1 ns)
... | []     = nothing
... | m ∷ ms = just (m + sum ms)

toDigitChar : (n : ℕ) → Char
toDigitChar n = fromℕ (n + (toℕ '0'))

toDecimalChars : ℕ → List Char
toDecimalChars = map toDigitChar ∘ toNatDigits 10

showℕ : ℕ → String
showℕ = fromList ∘ toDecimalChars

readℕ : String → String ⊎ ℕ
readℕ s =
  let ns = maybeList (map charToℕ (toList s))
   in maybe′ (maybe′ inj₂ (inj₁ s) ∘ toBaseℕ 10) (inj₁ s) ns
