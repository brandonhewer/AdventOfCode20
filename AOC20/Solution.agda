{-# OPTIONS --without-K --safe #-}

module AOC20.Solution where

open import AOC20.Conversions
open import AOC20.List hiding (mapMaybe; _++_)

open import Data.Bool hiding (_≟_; _≤?_)
open import Data.Bool.Properties using (T?)
open import Data.Char renaming (_≟_ to _≟ᶜ_)
open import Data.Fin hiding (_+_; _≟_; _≤?_; suc)
open import Data.List.NonEmpty using (_∷_)
open import Data.Maybe renaming (map to mapMaybe)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.String hiding (_≟_; length)
open import Data.Sum renaming (map to mapSum)

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Level hiding (suc)

private
  variable
    ℓ₁ : Level

  lines : List Char → List (List Char)
  lines = wordsBy (_≟ᶜ '\n')

  nats : String → List ℕ
  nats = stripMaybe ∘ map readℕ′ ∘ wordsBy (T? ∘ isSpace) ∘ toList

module Day1 where

  Part1 : String → String
  Part1 = maybe′ showℕ "Solution not found" ∘ solve ∘ nats
    where
      solve : List ℕ → Maybe ℕ
      solve ns = mapMaybe (uncurry _*_ ∘ proj₁)
                          (findWith (λ { (x , y) → x + y ≟ 2020 })
                                    (distinctPairs ns))

  Part2 : String → String
  Part2 = maybe′ showℕ "Solution not found" ∘ solve ∘ nats
    where
      solve : List ℕ → Maybe ℕ
      solve ns = mapMaybe ((λ { (x , y , z) → x * y * z }) ∘ proj₁)
                          (findWith (λ { (x , y , z) → x + y + z ≟ 2020 })
                                    (distinctTriples ns))

module Day2 where

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
     in mapMaybe (dropWhile (T? ∘ isSpace) s′ ,_) (parsePolicy p)

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
      isValid (s , i , j , [])    = false
      isValid (s , i , j , (c ∷ _)) = xor (map valid (enumerateWith 1 suc s))
        where
          valid : ℕ × Char → Bool
          valid (n , x) = (does (n ≟ i) ∨ does (n ≟ j)) ∧ does (c ≟ᶜ x)
