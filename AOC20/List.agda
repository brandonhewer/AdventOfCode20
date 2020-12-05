{-# OPTIONS --without-K --safe #-}

module AOC20.List where

open import Data.Bool
open import Data.Fin
open import Data.Fin.Patterns
open import Data.Fin.Properties
open import Data.List hiding ([_]) public
open import Data.List.Properties public
open import Data.List.NonEmpty hiding ([_]; wordsBy; reverse; length; foldl)
                               renaming (map to map⁺)
open import Data.Maybe renaming (map to maybeMap) hiding (zipWith)
open import Data.Nat
open import Data.Product hiding (map) renaming (map₂ to map-snd)
open import Data.Sum hiding (map; map₁; map₂)

open import Function

open import Level renaming (zero to ℓ-zero; suc to ℓ-suc)

open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Set ℓ₁
    B : Set ℓ₂
    C : Set ℓ₃
    D : Set ℓ₄

  opposite : ∀ {n} → Fin n → Fin n
  opposite {suc n} zero    = fromℕ n
  opposite {suc n} (suc i) = inject₁ (opposite i)

isEqList : DecidableEquality A → (xs : List A) →
           (i : Fin (length xs)) → ∀ a → Dec _
isEqList _≟_ xs i a = lookup xs i ≟ a

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
  let (a′ , c)   = f a b
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

cartesianProduct₃ : List A → List B → List C → List (A × B × C)
cartesianProduct₃ as bs cs = cartesianProduct as (cartesianProduct bs cs)

distinctTuples : ∀ n → List A → List (Fin n → A)
distinctTuples 0 xs = []
distinctTuples 1 xs = map const xs
distinctTuples (suc (suc n)) []       = []
distinctTuples (suc (suc n)) (x ∷ xs) =
  map (∀-cons x) (distinctTuples (suc n) xs) ++
  distinctTuples (suc (suc n)) xs

distinctPairs : List A → List (A × A)
distinctPairs = map (λ f → f 0F , f 1F) ∘ distinctTuples 2

distinctTriples : List A → List (A × A × A)
distinctTriples = map (λ f → f 0F , f 1F , f 2F) ∘ distinctTuples 3

xor : List Bool → Bool
xor []       = false
xor (b ∷ bs) = if b then not (or bs) else xor bs

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

stripMaybe : List (Maybe A) → List A
stripMaybe []             = []
stripMaybe (nothing ∷ xs) = stripMaybe xs
stripMaybe (just x  ∷ xs) = x ∷ stripMaybe xs

stripPrefix : ∀ {n} {P : Fin n → A → Set ℓ₂} →
                (∀ i a → Dec (P i a)) →
                List A → Maybe (List A)
stripPrefix {n = zero} P? xs  = just xs
stripPrefix {n = suc n} P? [] = nothing
stripPrefix {n = suc n} P? (x ∷ xs) with does (P? zero x)
... | false = nothing
... | true  = stripPrefix (P? ∘ suc) xs

stripSuffix : ∀ {n} {P : Fin n → A → Set ℓ₂} →
                (∀ i a → Dec (P i a)) →
                List A → Maybe (List A)
stripSuffix P? xs = maybeMap reverse (stripPrefix (P? ∘ opposite) (reverse xs))

hasLeft? : List (A ⊎ B) → List A ⊎ List B
hasLeft? [] = inj₂ []
hasLeft? (x ∷ xs) with hasLeft? xs
... | inj₁ as = [ inj₁ ∘ (_∷ as) , const (inj₁ as) ] x
... | inj₂ bs = [ inj₁ ∘ (_∷ []) , inj₂ ∘ (_∷ bs) ] x

wordsBy : ∀ {P : A → Set ℓ₂} → (∀ a → Dec (P a)) → List A → List (List A)
wordsBy {A = A} P? = go []
  where
    cons : List A → List (List A) → List (List A)
    cons []       ass = ass
    cons (a ∷ as) ass = reverse (a ∷ as) ∷ ass

    go : List A → List A → List (List A)
    go acc []       = cons acc []
    go acc (c ∷ cs) with does (P? c)
    ... | true  = cons acc (go [] cs)
    ... | false = go (c ∷ acc) cs

open import Data.Bool.Properties using (T?)

wordsByⁿ : ∀ {n} {P : Fin n → A → Set ℓ₂} →
             (∀ i a → Dec (P i a)) → List A → List (List A)
wordsByⁿ {A = A} {n = zero} P? = const []
wordsByⁿ {A = A} {n = suc n} P? = go P? [] []
  where
    cons : List A → List (List A) → List (List A)
    cons []       ass = ass
    cons (a ∷ as) ass = reverse (a ∷ as) ∷ ass

    go : ∀ {n} {P : Fin n → A → Set ℓ₂} →
           (∀ i a → Dec (P i a)) → List A → List A → List A → List (List A)
    go {n = n} Q? acc₁ acc₂ [] = cons acc₁ []
    go {n = zero} Q? acc₁ acc₂ (x ∷ xs) with does (P? zero x)
    ... | false = cons acc₁ (go (P? ∘ suc) (x ∷ []) [] xs)
    ... | true  = cons acc₁ (go (P? ∘ suc) [] (x ∷ []) xs)
    go {n = suc n} Q? acc₁ acc₂ (x ∷ xs) with does (Q? zero x)
    ... | false = go P? (x ∷ (acc₂ ++ acc₁)) [] xs
    ... | true  = go (Q? ∘ suc) acc₁ (x ∷ acc₂) xs

wordsⁿ : DecidableEquality A → List A → List A → List (List A)
wordsⁿ _≡ₐ_ as = wordsByⁿ λ i a → lookup as i ≡ₐ a

splitFirst : {P : A → Set ℓ₂} → (∀ a → Dec (P a)) →
             List A → List A × List A
splitFirst P? = map-snd (λ { [] → []; (_ ∷ xs) → xs }) ∘ break P?

contains : {P : A → Set ℓ₂} → (∀ a → Dec (P a)) → List A → Bool
contains P? = is-just ∘ findWith P?

containsAll : ∀ {n} {P : Fin n → A → Set ℓ₂} →
                (∀ i a → Dec (P i a)) → List A → Bool
containsAll {n = zero}  P? xs = true
containsAll {n = suc n} P? xs = contains (P? zero) xs ∧
                                containsAll (P? ∘ suc) xs

occurs : {P : A → Set ℓ₂} → (∀ a → Dec (P a)) → List A → ℕ
occurs P? [] = 0
occurs P? (x ∷ xs) with does (P? x) | occurs P? xs
... | false | n = n
... | true  | n = suc n

occursⁿ : {P : A → B → Set ℓ₁} → (∀ a b → Dec (P a b)) →
          List A → List⁺ B → ℕ
occursⁿ P? as bs = go P? as bs bs
  where
    go : {P : A → B → Set ℓ₁} → (∀ a b → Dec (P a b)) →
         List A → List⁺ B → List⁺ B → ℕ
    go P? [] bs bs′ = 0
    go P? (a ∷ as) bs (b ∷ []) with does (P? a b) | go P? as bs bs
    ... | false | n = n
    ... | true  | n = suc n
    go P? (a ∷ as) bs (b₁ ∷ b₂ ∷ bs′) with does (P? a b₁)
    ... | false = go P? as bs bs
    ... | true  = go P? as bs (b₂ ∷ bs′)

partitionⁿ : {ℓ : Level} {A : Set ℓ} → ℕ → List A → List A × List A
partitionⁿ = take -,- drop

difference : {P : A → A → Set ℓ₁} → (∀ a b → Dec (P a b)) →
             List A → List A → List A
difference {A = A} P? = foldl (flip (filter ∘ notP?))
  where
    notP? : (x y : A) → Dec _
    notP? x y = T? (not (does (P? x y)))
