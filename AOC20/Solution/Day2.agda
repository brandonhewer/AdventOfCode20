{-# OPTIONS --without-K --safe #-}

module AOC20.Solution.Day2 where

open import AOC20.Conversions
open import AOC20.List

open import Data.Bool hiding (_≤?_; _≟_)
open import Data.Bool.Properties using (T?)
open import Data.Char renaming (_≟_ to _≟ᶜ_)
open import Data.List.NonEmpty using (_∷_)
open import Data.Maybe renaming (map to maybeMap)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.String hiding (_≟_)

open import Function

open import Relation.Nullary

parsePolicy : List Char → Maybe (ℕ × ℕ × List Char)
parsePolicy s = do
  let (r , s′)  = splitFirst (T? ∘ isSpace) s
      (m′ , n′) = splitFirst (_≟ᶜ '-') r
  m ← readℕ m′
  n ← readℕ n′
  just (m , n , s′)

parse : List Char → Maybe (List Char × ℕ × ℕ × List Char)
parse s = 
  let (p , s′) = splitFirst (_≟ᶜ ':') s
   in maybeMap (dropWhile (T? ∘ isSpace) s′ ,_) (parsePolicy p)

runV : (List Char × ℕ × ℕ × List Char → Bool) → String → String
runV isValid =
  showℕ ∘ occurs T? ∘
  map (maybe′ isValid false ∘ parse) ∘ lines ∘ toList

Part1 : String → String
Part1 = runV isValid
  where
    isValid : List Char × ℕ × ℕ × List Char → Bool
    isValid (s , l , u , [])       = false
    isValid (s , l , u , (x ∷ xs)) =
      let n = occursⁿ _≟ᶜ_ s (x ∷ xs)
       in does (l ≤? n) ∧ does (n ≤? u)

Part2 : String → String
Part2 = runV isValid
  where
    isValid : List Char × ℕ × ℕ × List Char → Bool
    isValid (s , i , j , [])      = false
    isValid (s , i , j , (c ∷ _)) = xor (map valid (enumerateWith 1 suc s))
      where
        valid : ℕ × Char → Bool
        valid (n , x) = (does (n ≟ i) ∨ does (n ≟ j)) ∧ does (c ≟ᶜ x)
