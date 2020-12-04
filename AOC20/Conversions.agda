{-# OPTIONS --without-K --safe #-}

module AOC20.Conversions where

open import AOC20.Digit
open import AOC20.List

open import Data.Bool
open import Data.Bool.Properties using (T?)
open import Data.Char renaming (_≟_ to _≟ᶜ_)
open import Data.Fin hiding (toℕ; fromℕ; _+_)
open import Data.Maybe renaming (map to maybeMap)
open import Data.Nat
open import Data.String
open import Data.Sum hiding (map)
open import Data.Product hiding (map)

open import Function

charToℕ : Char → Maybe ℕ
charToℕ c with isDigit c
... | false = nothing
... | true  = just (toℕ c ∸ toℕ '0')

toBaseℕL : ℕ → List ℕ → Maybe ℕ
toBaseℕL b ns with proj₂ (mapAccumL (λ s n → b * s , s * n) 1 ns)
... | []     = nothing
... | m ∷ ms = just (m + sum ms)

toBaseℕR : ℕ → List ℕ → Maybe ℕ
toBaseℕR b ns with proj₂ (mapAccumR (λ s n → b * s , s * n) 1 ns)
... | []     = nothing
... | m ∷ ms = just (m + sum ms)

toDigitChar : (n : ℕ) → Char
toDigitChar n = fromℕ (n + (toℕ '0'))

toDecimalChars : ℕ → List Char
toDecimalChars = map toDigitChar ∘ toNatDigits 10

showℕ : ℕ → String
showℕ = fromList ∘ toDecimalChars

readℕ′ : List Char → Maybe ℕ
readℕ′ = (_>>= toBaseℕR 10) ∘ maybeList ∘ map charToℕ

readℕ : String → String ⊎ ℕ
readℕ s =
  let ns = maybeList (map charToℕ (toList s))
   in maybe′ (maybe′ inj₂ (inj₁ s) ∘ toBaseℕR 10) (inj₁ s) ns

lines : List Char → List (List Char)
lines = wordsBy (_≟ᶜ '\n')

nats : String → List ℕ
nats = stripMaybe ∘ map readℕ′ ∘ wordsBy (T? ∘ isSpace) ∘ toList
