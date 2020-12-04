{-# OPTIONS --without-K --safe #-}

module AOC20.Solution.Day1 where

open import AOC20.Conversions
open import AOC20.List

open import Data.Fin hiding (_+_; _≟_; _≤?_; suc)
open import Data.Maybe renaming (map to maybeMap)
open import Data.Nat
open import Data.Product
open import Data.String hiding (_≟_)

open import Function

Part1 : String → String
Part1 = maybe′ showℕ "Solution not found" ∘ solve ∘ nats
  where
    solve : List ℕ → Maybe ℕ
    solve ns = maybeMap (uncurry _*_ ∘ proj₁)
                        (findWith (λ { (x , y) → x + y ≟ 2020 })
                                  (distinctPairs ns))

Part2 : String → String
Part2 = maybe′ showℕ "Solution not found" ∘ solve ∘ nats
  where
    solve : List ℕ → Maybe ℕ
    solve ns = maybeMap ((λ { (x , y , z) → x * y * z }) ∘ proj₁)
                        (findWith (λ { (x , y , z) → x + y + z ≟ 2020 })
                                  (distinctTriples ns))
