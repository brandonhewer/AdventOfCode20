{-# OPTIONS --without-K --safe #-}

module AOC20.Solution.Day4 where

open import AOC20.Conversions
open import AOC20.List

open import Data.Bool hiding (_≤?_)
open import Data.Bool.Properties using (T?)
open import Data.Char renaming (_≟_ to _≟ᶜ_)
open import Data.Maybe renaming (map to maybeMap)
open import Data.Nat renaming (_≟_ to _≟ⁿ_)
open import Data.Product hiding (map)
open import Data.String hiding (length)

open import Function

open import Relation.Nullary

kwargs : Char → List Char → List (List Char × List Char)
kwargs c = map (splitFirst (_≟ᶜ c)) ∘ wordsBy (T? ∘ isSpace)

parseFields : Char → List (List Char) → List Char → Maybe (List (List Char))
parseFields d ks = mk ∘ concatMap (kwargs d) ∘ wordsBy (_≟ᶜ '\n')
  where
    mk : List (List Char × List Char) → Maybe (List (List Char))
    mk xs = maybeList (map (λ x → maybeMap (proj₂ ∘ proj₁)
                                    (findWith (≡-dec _≟ᶜ_ x ∘ proj₁) xs)) ks)

parseEntries : List (List Char) → String → List (Maybe (List (List Char)))
parseEntries ks = map (parseFields ':' ks) ∘
                  wordsByⁿ (isEqList _≟ᶜ_ ('\n' ∷ '\n' ∷ [])) ∘ toList

isValidPassport : List (List Char) → Bool
isValidPassport (
   by ∷
   iy ∷
   ey ∷
   ht ∷
   hc ∷
   ec ∷
   id ∷
   _
   ) = isValidBY by ∧ isValidIY iy ∧ isValidEY ey ∧
       isValidHT ht ∧ isValidHC hc ∧ isValidEC ec ∧
       isValidID id
  where
    isNumberBtwn : ℕ → ℕ → ℕ → List Char → Bool
    isNumberBtwn len l u xs with readℕ′ xs
    ... | nothing = false
    ... | just n  = does (length xs ≟ⁿ len) ∧ does (l ≤? n) ∧
                    does (n ≤? u)

    isValidBY : List Char → Bool
    isValidBY = isNumberBtwn 4 1920 2002

    isValidIY : List Char → Bool
    isValidIY = isNumberBtwn 4 2010 2020

    isValidEY : List Char → Bool
    isValidEY = isNumberBtwn 4 2020 2030

    isValidHT : List Char → Bool
    isValidHT xs with stripSuffix (isEqList _≟ᶜ_ ('c' ∷ 'm' ∷ [])) xs
    ... | just cm  = isNumberBtwn 3 150 193 cm
    ... | nothing with stripSuffix (isEqList _≟ᶜ_ ('i' ∷ 'n' ∷ [])) xs
    ... | nothing  = false
    ... | just inc = isNumberBtwn 2 59 76 inc

    isValidHC : List Char → Bool
    isValidHC []         = false
    isValidHC ('#' ∷ xs) = does (length xs ≟ⁿ 6) ∧ all (λ b → isAlpha b ∨ isDigit b) xs
    isValidHC (_   ∷  _) = false

    isValidEC : List Char → Bool
    isValidEC ('a' ∷ 'm' ∷ 'b' ∷ []) = true
    isValidEC ('b' ∷ 'l' ∷ 'u' ∷ []) = true
    isValidEC ('b' ∷ 'r' ∷ 'n' ∷ []) = true
    isValidEC ('g' ∷ 'r' ∷ 'y' ∷ []) = true
    isValidEC ('g' ∷ 'r' ∷ 'n' ∷ []) = true
    isValidEC ('h' ∷ 'z' ∷ 'l' ∷ []) = true
    isValidEC ('o' ∷ 't' ∷ 'h' ∷ []) = true
    isValidEC _                      = false

    isValidID : List Char → Bool
    isValidID xs = does (length xs ≟ⁿ 9) ∧ all isDigit xs

isValidPassport _ = false

expectedKeys′ : List String
expectedKeys′ =
  "byr" ∷
  "iyr" ∷
  "eyr" ∷
  "hgt" ∷
  "hcl" ∷
  "ecl" ∷
  "pid" ∷
  []

expectedKeys : List (List Char)
expectedKeys = map toList expectedKeys′

Part1 : String → String
Part1 = showℕ ∘ occurs (T? ∘ is-just) ∘ parseEntries expectedKeys

Part2 : String → String
Part2 = showℕ ∘ occurs (T? ∘ maybe′ id false ∘ maybeMap isValidPassport) ∘
        parseEntries expectedKeys
