{-# OPTIONS --without-K --safe #-}

module AOC20.List where

open import Data.Bool
open import Data.Fin
open import Data.Fin.Patterns
open import Data.Fin.Properties
open import Data.List hiding ([_]) public
open import Data.Maybe hiding (map; zipWith)
open import Data.Nat
open import Data.Product hiding (map; map₂)
open import Data.Sum hiding (map; map₂)

open import Function

open import Level renaming (zero to ℓ-zero; suc to ℓ-suc)

open import Relation.Nullary

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Set ℓ₁
    B : Set ℓ₂
    C : Set ℓ₃
    D : Set ℓ₄

map₂ : (A → B → C) → List A → List B → List C
map₂ f []       _        = []
map₂ f (_ ∷ _)  []       = []
map₂ f (a ∷ as) (b ∷ bs) = f a b ∷ map₂ f as bs

enumerateWith : A → (A → A) → List B → List (A × B)
enumerateWith z s []       = []
enumerateWith z s (b ∷ bs) = (z , b) ∷ enumerateWith (s z) s bs

enumerate : List A → List (ℕ × A)
enumerate = enumerateWith zero suc

mapAccumL : (A → B → A × C) → A → List B → A × List C
mapAccumL f a [] = a , []
mapAccumL f a (b ∷ bs) =
  let (a′ , c) = f a b
      (a′′ , cs) = mapAccumL f a′ bs
   in a′′ , c ∷ cs

mapAccumR : (A → B → A × C) → A → List B → A × List C
mapAccumR f a [] = a , []
mapAccumR f a (b ∷ bs) =
  let (a′ , cs) = mapAccumR f a bs
      (a′′ , c) = f a′ b
   in a′′ , c ∷ cs

cartesianProductWith : (A → B → C) → List A → List B → List C
cartesianProductWith f []       _  = []
cartesianProductWith f (x ∷ xs) ys = map (f x) ys ++ cartesianProductWith f xs ys

cartesianProduct : List A → List B → List (A × B)
cartesianProduct = cartesianProductWith _,_

-- [0 , 1 , 2 , 3]
-- [(1 , 2) , (1 , 3) , (2 , 3)]
-- [(0 , 1 , 2) , (0 , 2 , 3) , (0 , 1 , 3) , (1 , 2 , 3)]

cartesianProduct₃ : List A → List B → List C → List (A × B × C)
cartesianProduct₃ as bs cs = cartesianProduct as (cartesianProduct bs cs)

distinctTuples : ∀ n → List A → List (Fin n → A)
distinctTuples 0 xs = []
distinctTuples 1 xs = map const xs
distinctTuples (suc (suc n)) [] = []
distinctTuples (suc (suc n)) (x ∷ xs) =
  map (∀-cons x) (distinctTuples (suc n) xs) ++
  distinctTuples (suc (suc n)) xs

distinctPairs : List A → List (A × A)
distinctPairs = map (λ f → f 0F , f 1F) ∘ distinctTuples 2

distinctTriples : List A → List (A × A × A)
distinctTriples = map (λ f → f 0F , f 1F , f 2F) ∘ distinctTuples 3

findWith : {P : A → Set ℓ₂} → (∀ a → Dec (P a)) → List A → Maybe (Σ A P)
findWith P? [] = nothing
findWith P? (a ∷ as) with P? a
... | yes p = just (a , p)
... | no ¬p = findWith P? as

maybeList : List (Maybe A) → Maybe (List A)
maybeList []            = just []
maybeList (x ∷ xs) with x | maybeList xs
... | nothing | ys      = nothing
... | just y  | nothing = nothing
... | just y  | just ys = just (y ∷ ys)

hasLeft? : List (A ⊎ B) → List A ⊎ List B
hasLeft? [] = inj₂ []
hasLeft? (x ∷ xs) with hasLeft? xs
... | inj₁ as = [ inj₁ ∘ (_∷ as) , const (inj₁ as) ] x
... | inj₂ bs = [ inj₁ ∘ (_∷ []) , inj₂ ∘ (_∷ bs) ] x

wordsBy : {P : A → Set ℓ₂} → (∀ a → Dec (P a)) → List A → List (List A)
wordsBy {A = A} P? = go []
  where
    go : List A → List A → List (List A)
    go acc []       = acc ∷ []
    go acc (c ∷ cs) with does (P? c)
    ... | true  = acc ∷ (go [] cs)
    ... | false = go (c ∷ acc) cs

