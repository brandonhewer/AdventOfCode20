{-# OPTIONS --no-import-sorts #-}

module AOC20 where

open import AOC20.Conversions
open import AOC20.IO
open import AOC20.Solution

open import Codata.Musical.Costring
open import Codata.Musical.Notation

open import Data.Fin
open import Data.Maybe hiding (_>>=_)
open import Data.Nat

open import Data.String

open import Function

getSolution : ℕ → ℕ → String → String
getSolution 1 1 = Part₁₁
getSolution 1 2 = Part₁₂
getSolution 2 1 = Part₂₁
getSolution 2 2 = Part₂₂
getSolution 3 1 = Part₃₁
getSolution 3 2 = Part₃₂
getSolution _ _ = const "Solution doesn't exist"

getSolution′ : Maybe ℕ → Maybe ℕ → String → String
getSolution′ nothing        _  = const "Invalid problem given"
getSolution′ (just _) nothing  = const "Invalid part given"
getSolution′ (just m) (just n) = getSolution m n

main = run $
  ♯ getProblem >>= λ pb →
  ♯ (♯ getPart >>= λ pt →
  ♯ (♯ getInput >>= λ i →
  ♯ (♯ putStrLn "Solution:" >> ♯ putStrLn (getSolution′ pb pt i))))
  where
    getProblem : IO (Maybe ℕ)
    getProblem =
      ♯ (putStrLn "Problem #:") >> ♯ getDecℕ

    getPart : IO (Maybe ℕ)
    getPart =
      ♯ (putStrLn "Part:") >> ♯ getDecℕ

    getInput : IO String
    getInput = ♯ (putStrLn "Input File:") >>
               ♯ (♯ getLine′ >>= λ f → ♯ readFiniteFile f)
