{-# OPTIONS --without-K --sized-types --guardedness #-}

module AOC20.Solution.Day3 where

open import AOC20.Colist hiding (fromList; map)
open import AOC20.Conversions
open import AOC20.List hiding (lookup)

open import Data.Bool
open import Data.Bool.Properties using (T?)
open import Data.Char renaming (_≟_ to _≟ᶜ_)
open import Data.List.NonEmpty using (_∷_; fromList)
open import Data.Maybe renaming (map to maybeMap)
open import Data.Nat
open import Data.Nat.Properties renaming (_≟_ to _≟ⁿ_)
open import Data.Product hiding (map)
open import Data.String hiding (fromList)

open import Level

open import Function

open import Relation.Nullary

private
  variable
    ℓ₁ : Level

traverseMap : {A : Set ℓ₁} → (A → Colist Char → A × Bool) → A →
              List (List Char) → ℕ
traverseMap f z = occurs T? ∘ proj₂ ∘ mapAccumL f z ∘
                  mapMaybe (maybeMap cycle ∘ fromList)

hasTreeAt : ℕ → Colist Char → Bool
hasTreeAt n = maybe′ (does ∘ (_≟ᶜ '#')) false ∘ lookup n

removeStep : {A : Set ℓ₁} → ℕ → List A → List A
removeStep n =
  let nextℕ : ℕ → ℕ
      nextℕ i = if does (i ≟ⁿ 1) then n else pred i
   in map proj₂ ∘ filter ((_≟ⁿ 1) ∘ proj₁) ∘
      enumerateWith 1 nextℕ

traverseSlope : ℕ → ℕ → List (List Char) → ℕ
traverseSlope r d = traverseMap treeAtNext 0 ∘ removeStep d
  where
    treeAtNext : ℕ → Colist Char → ℕ × Bool
    treeAtNext n xs = r + n , hasTreeAt n xs

Part1 : String → String
Part1 = showℕ ∘ traverseSlope 3 1 ∘ lines ∘ toList

Part2 : String → String
Part2 s = 
  let cs = lines (toList s)
      ns = map (flip (uncurry traverseSlope) cs)
                 ((1 , 1) ∷ (3 , 1) ∷ (5 , 1) ∷
                  (7 , 1) ∷ (1 , 2) ∷ [])
   in showℕ (product ns)
