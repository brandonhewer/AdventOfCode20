{-# OPTIONS --without-K #-}

module AOC20.IO where

open import AOC20.Conversions
open import AOC20.List
open import AOC20.Partiality

open import Codata.Musical.Costring
open import Codata.Musical.Notation

open import Data.Maybe hiding (_>>=_)
open import Data.Nat
open import Data.String

open import Function

open import IO public
open import IO.Primitive renaming (IO to PrimIO) hiding (_>>=_; return)

open import Level

postulate
  getLine : PrimIO Costring

{-# FOREIGN GHC
  toColist :: [a] -> MAlonzo.Code.Codata.Musical.Colist.AgdaColist a
  toColist []       = MAlonzo.Code.Codata.Musical.Colist.Nil
  toColist (x : xs) =
    MAlonzo.Code.Codata.Musical.Colist.Cons x (MAlonzo.RTE.Sharp (toColist xs))
#-}

{-# COMPILE GHC getLine = fmap toColist getLine #-}

private
  variable
    ℓ₁ : Level

getDecℕ : IO (Maybe ℕ)
getDecℕ = ♯ (lift getLine) >>= λ s → ♯ IO⊥ (readℕ∞ s)

mapIO : {A B : Set ℓ₁} → (A → B) → IO A → IO B
mapIO f x = ♯ x >>= λ a → ♯ (return (f a))

getLine′ : IO String
getLine′ =
  ♯ lift getLine >>= λ s →
    ♯ IO⊥ (map-⊥ (fromList ∘ reverse) (costringToList⊥ s))
