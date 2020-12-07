{-# OPTIONS --without-K --safe #-}

module AOC20.Solution.Day6 where

open import AOC20.Conversions
open import AOC20.List

open import Data.Bool.Properties using (T?)
open import Data.Char renaming (_≟_ to _≟ᶜ_)
open import Data.Nat
open import Data.String hiding (concat; length)

open import Function

uniqueAlpha : List Char → ℕ
uniqueAlpha = length ∘ deduplicate _≟ᶜ_ ∘ filter (T? ∘ isAlpha)

sharedAlpha : List (List Char) → ℕ
sharedAlpha []         = 0
sharedAlpha (xs ∷ xss) = length (foldl (intersectBy _≟ᶜ_) xs xss)

Part1 : String → String
Part1 = showℕ ∘ sum ∘ map (uniqueAlpha ∘ concat) ∘
        wordsBy (T? ∘ null) ∘ lines ∘ toList

Part2 : String → String
Part2 = showℕ ∘ sum ∘ map sharedAlpha ∘
        wordsBy (T? ∘ null) ∘ lines ∘ toList
