{-# OPTIONS --without-K --sized-types --guardedness #-}

module AOC20.Solution where

open import AOC20.Conversions
open import AOC20.List hiding (_++_; lookup)

open import Data.Bool hiding (_≟_; _≤?_)
open import Data.Bool.Properties using (T?)
open import Data.Char renaming (_≟_ to _≟ᶜ_)
open import Data.Maybe renaming (map to maybeMap)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.String hiding (_≟_; length; fromList)
open import Data.Sum renaming (map to mapSum)

open import Function

open import Relation.Nullary

open import Level renaming (suc to ℓ-suc; zero to ℓ-zero)

private
  variable
    ℓ₁ : Level

  lines : List Char → List (List Char)
  lines = wordsBy (_≟ᶜ '\n')

  nats : String → List ℕ
  nats = stripMaybe ∘ map readℕ′ ∘ wordsBy (T? ∘ isSpace) ∘ toList

module Day1 where

  open import Data.Fin hiding (_+_; _≟_; _≤?_; suc)

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

module Day2 where

  open import Data.List.NonEmpty using (_∷_)

  parsePolicy : List Char → Maybe (ℕ × ℕ × List Char)
  parsePolicy s = do
    let (r , s′)  = splitFirst (T? ∘ isSpace) s
        (m′ , n′) = splitFirst (_≟ᶜ '-') r
    m ← readℕ′ m′
    n ← readℕ′ n′
    just (m , n , s′)

  parse : List Char → Maybe (List Char × ℕ × ℕ × List Char)
  parse s = 
    let (p , s′) = splitFirst (_≟ᶜ ':') s
     in maybeMap (dropWhile (T? ∘ isSpace) s′ ,_) (parsePolicy p)

  run : (List Char × ℕ × ℕ × List Char → Bool) → String → String
  run isValid =
    showℕ ∘ occurs T? ∘
    map (maybe′ isValid false ∘ parse) ∘ lines ∘ toList

  Part1 : String → String
  Part1 = run isValid
    where
      isValid : List Char × ℕ × ℕ × List Char → Bool
      isValid (s , l , u , [])       = false
      isValid (s , l , u , (x ∷ xs)) =
        let n = occursⁿ _≟ᶜ_ s (x ∷ xs)
         in does (l ≤? n) ∧ does (n ≤? u)

  Part2 : String → String
  Part2 = run isValid
    where
      isValid : List Char × ℕ × ℕ × List Char → Bool
      isValid (s , i , j , [])      = false
      isValid (s , i , j , (c ∷ _)) = xor (map valid (enumerateWith 1 suc s))
        where
          valid : ℕ × Char → Bool
          valid (n , x) = (does (n ≟ i) ∨ does (n ≟ j)) ∧ does (c ≟ᶜ x)

module Day3 where

  open import AOC20.Colist hiding (fromList; map)
  open import Data.List.NonEmpty using (_∷_; fromList)
  open import Data.Nat.Properties renaming (_≟_ to _≟ⁿ_)

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
        n₁ = traverseSlope 1 1 cs
        n₂ = traverseSlope 3 1 cs
        n₃ = traverseSlope 5 1 cs
        n₄ = traverseSlope 7 1 cs
        n₅ = traverseSlope 1 2 cs
     in showℕ (n₁ * n₂ * n₃ * n₄ * n₅)
