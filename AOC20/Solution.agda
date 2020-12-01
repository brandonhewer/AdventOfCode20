{-# OPTIONS --without-K --safe #-}

module AOC20.Solution where

open import AOC20.Conversions
open import AOC20.List hiding (mapMaybe; _++_)

open import Data.Bool.Properties using (T?)
open import Data.Char hiding (_≟_)
open import Data.Fin hiding (_+_; _≟_)
open import Data.Maybe renaming (map to mapMaybe)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.String hiding (_≟_)
open import Data.Sum renaming (map to mapSum)

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Level

private
  variable
    ℓ₁ : Level
    
  wordsBy′ : {P : Char → Set ℓ₁} → (∀ a → Dec (P a)) → String → List String
  wordsBy′ P? = map fromList ∘ wordsBy P? ∘ toList

  words : String → List String
  words = wordsBy′ (T? ∘ isSpace)

  nats : String → List ℕ
  nats = proj₂ ∘ partitionSums ∘ map readℕ ∘ words

day1-1 : String → String
day1-1 = maybe′ showℕ "Solution not found" ∘ solve ∘ nats
  where
    solve : List ℕ → Maybe ℕ
    solve ns = mapMaybe (uncurry _*_ ∘ proj₁)
                        (findWith (λ { (x , y) → x + y ≟ 2020 })
                                  (distinctPairs ns))

day1-2 : String → String
day1-2 = maybe′ showℕ "Solution not found" ∘ solve ∘ nats
  where
    solve : List ℕ → Maybe ℕ
    solve ns = mapMaybe ((λ { (x , y , z) → x * y * z }) ∘ proj₁)
                        (findWith (λ { (x , y , z) → x + y + z ≟ 2020 })
                                  (distinctTriples ns))
