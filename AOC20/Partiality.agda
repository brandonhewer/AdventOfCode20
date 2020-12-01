{-# OPTIONS --without-K #-}

module AOC20.Partiality where

open import AOC20.Conversions
open import AOC20.List

open import Category.Monad.Partiality hiding (map) public

open import Data.Char
open import Data.List
open import Data.Maybe hiding (map)
open import Data.Nat
open import Data.String
open import Data.Unit.Polymorphic

open import Codata.Musical.Colist hiding (map)
open import Codata.Musical.Costring
open import Codata.Musical.Notation

open import Function

open import IO hiding (_>>=_)

open import Level


private
  variable
    ℓ₁ ℓ₂ : Level
    A : Set ℓ₁
    B : Set ℓ₂

map-⊥ : (A → B) → A ⊥ → B ⊥
map-⊥ f (now x)   = now (f x)
map-⊥ f (later x) = later (♯ map-⊥ f (♭ x))

costringToList⊥ : Costring → List Char ⊥
costringToList⊥ = go []
  where
    go : List Char → Costring → List Char ⊥
    go z []       = now z
    go z (x ∷ xs) = later (♯ go (x ∷ z) (♭ xs))

IO⊥ : A ⊥ → IO A
IO⊥ (now a)   = return a
IO⊥ (later a) = ♯ return tt >> ♯ IO⊥ (♭ a)

readℕ∞ : Costring → Maybe ℕ ⊥
readℕ∞ = map-⊥ ((_>>= toBaseℕ 10) ∘ maybeList ∘ map charToℕ) ∘
         costringToList⊥
