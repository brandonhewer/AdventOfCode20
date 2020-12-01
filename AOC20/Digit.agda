------------------------------------------------------------------------
-- The Agda standard library
--
-- REFLECTION.PATTERN CONTAINS AN APPARENT TYPE ERROR =>
-- ALL NECESSARY FUNCTIONS FOR DIGITS MOVED TO THIS FILE
--
-- Core lemmas for division and modulus operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module AOC20.Digit where

open import Agda.Builtin.Nat using (div-helper; mod-helper)

open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Nat.Solver
open import Data.Fin.Base as Fin using (Fin; zero; suc; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Char using (Char)
open import Data.List.Base
open import Data.Product
open import Data.Vec.Base as Vec using (Vec; _∷_; [])
open import Data.Nat.Divisibility.Core
open import Data.Nat.Induction
open import Relation.Nullary using (does)
open import Relation.Nullary.Decidable
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality as P
open import Function

open ≤-Reasoning

-- Natural division

_/_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
m / (suc n) = div-helper 0 n m n

-- Natural remainder/modulus

_%_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
m % (suc n) = mod-helper 0 n m n

div-mod-lemma : ∀ accᵐ accᵈ d n →
    accᵐ + accᵈ * suc (accᵐ + n) + d ≡
    mod-helper accᵐ (accᵐ + n) d n + div-helper accᵈ (accᵐ + n) d n * suc (accᵐ + n)
div-mod-lemma accᵐ accᵈ zero    n    = +-identityʳ _
div-mod-lemma accᵐ accᵈ (suc d) zero rewrite +-identityʳ accᵐ = begin-equality
  accᵐ + accᵈ * suc accᵐ + suc d          ≡⟨ +-suc _ d ⟩
  suc accᵈ * suc accᵐ + d                 ≡⟨ div-mod-lemma zero (suc accᵈ) d accᵐ ⟩
  mod-helper 0          accᵐ d accᵐ +
  div-helper (suc accᵈ) accᵐ d accᵐ * suc accᵐ  ≡⟨⟩
  mod-helper accᵐ accᵐ (suc d) 0 +
  div-helper accᵈ accᵐ (suc d) 0 * suc accᵐ     ∎
div-mod-lemma accᵐ accᵈ (suc d) (suc n) rewrite +-suc accᵐ n = begin-equality
  accᵐ + accᵈ * m + suc d             ≡⟨ +-suc _ d ⟩
  suc (accᵐ + accᵈ * m + d)           ≡⟨ div-mod-lemma (suc accᵐ) accᵈ d n ⟩
  mod-helper _ _ d n + div-helper accᵈ _ d n * m  ∎
  where
  m = 2 + accᵐ + n

m≡m%n+[m/n]*n : ∀ m n → m ≡ m % suc n + (m / suc n) * suc n
m≡m%n+[m/n]*n m n = div-mod-lemma 0 0 m n

m/n*n≤m : ∀ m n {≢0} → (m / n) {≢0} * n ≤ m
m/n*n≤m m n@(suc n-1) = begin
  (m / n) * n          ≤⟨ m≤m+n ((m / n) * n) (m % n) ⟩
  (m / n) * n + m % n  ≡⟨ +-comm _ (m % n) ⟩
  m % n + (m / n) * n  ≡⟨ sym (m≡m%n+[m/n]*n m n-1) ⟩
  m                    ∎

m/n<m : ∀ m n {≢0} → m ≥ 1 → n ≥ 2 → (m / n) {≢0} < m
m/n<m m n@(suc n-1) m≥1 n≥2 = *-cancelʳ-< {n} (m / n) m (begin-strict
  (m / n) * n ≤⟨ m/n*n≤m m n ⟩
  m           <⟨ m<m*n m≥1 n≥2 ⟩
  m * n       ∎)

a[modₕ]n<n : ∀ acc d n → mod-helper acc (acc + n) d n ≤ acc + n
a[modₕ]n<n z zero    n       = m≤m+n z n
a[modₕ]n<n z (suc d) zero    = a[modₕ]n<n zero d (z + 0)
a[modₕ]n<n z (suc d) (suc n) rewrite +-suc z n = a[modₕ]n<n (suc z) d n

m%n<n : ∀ m n → m % suc n < suc n
m%n<n m n = s≤s (a[modₕ]n<n 0 m n)

------------------------------------------------------------------------
--  A specification of integer division.

record DivMod (dividend divisor : ℕ) : Set where
  constructor result
  field
    quotient  : ℕ
    remainder : Fin divisor
    property  : dividend ≡ toℕ remainder + quotient * divisor

infixl 7 _div_ _mod_ _divMod_

_div_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
_div_ = _/_

_mod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → Fin divisor
m mod (suc n) = fromℕ< (m%n<n m n)

_divMod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
           DivMod dividend divisor
m divMod n@(suc n-1) = result (m / n) (m mod n) (begin-equality
  m                                     ≡⟨ m≡m%n+[m/n]*n m n-1 ⟩
  m % n                      + [m/n]*n  ≡⟨ cong (_+ [m/n]*n) (sym (toℕ-fromℕ< (m%n<n m n-1))) ⟩
  toℕ (fromℕ< (m%n<n m n-1)) + [m/n]*n  ∎)
  where [m/n]*n = m / n * n

------------------------------------------------------------------------
-- Digits

-- Digit b is the type of digits in base b.

Digit : ℕ → Set
Digit b = Fin b

-- Some specific digit kinds.

Decimal = Digit 10
Bit     = Digit 2

-- Some named digits.

0b : Bit
0b = zero

1b : Bit
1b = suc zero

------------------------------------------------------------------------
-- Converting between `ℕ` and `expansions of ℕ`

toNatDigits : (base : ℕ) {base≤16 : True (1 ≤? base)} → ℕ → List ℕ
toNatDigits base@(suc zero)    n = replicate n 1
toNatDigits base@(suc (suc b)) n = aux (<-wellFounded n) []
  where
  aux : {n : ℕ} → Acc _<_ n → List ℕ → List ℕ
  aux {zero}        _        xs =  (0 ∷ xs)
  aux {n@(suc n-1)} (acc wf) xs with does (0 <? n / base)
  ... | false =  (n % base) ∷ xs
  ... | true  =  aux (wf (n / base) q<n) ((n % base) ∷ xs)
    where
    q<n : n / base < n
    q<n = m/n<m n base (s≤s z≤n) (s≤s (s≤s z≤n))

------------------------------------------------------------------------
-- Converting between `ℕ` and expansions of `Digit base`

Expansion : ℕ → Set
Expansion base = List (Digit base)

-- fromDigits takes a digit expansion of a natural number, starting
-- with the _least_ significant digit, and returns the corresponding
-- natural number.

fromDigits : ∀ {base} → Expansion base → ℕ
fromDigits        []       = 0
fromDigits {base} (d ∷ ds) = toℕ d + fromDigits ds * base

-- toDigits b n yields the digits of n, in base b, starting with the
-- _least_ significant digit.
--
-- Note that the list of digits is always non-empty.

toDigits : (base : ℕ) {base≥2 : True (2 ≤? base)} (n : ℕ) →
           ∃ λ (ds : Expansion base) → fromDigits ds ≡ n
toDigits (suc (suc k)) n = <′-rec Pred helper n
  where
  base = suc (suc k)
  Pred = λ n → ∃ λ ds → fromDigits ds ≡ n

  cons : ∀ {m} (r : Digit base) → Pred m → Pred (toℕ r + m * base)
  cons r (ds , eq) = (r ∷ ds , cong (λ i → toℕ r + i * base) eq)

  open ≤-Reasoning
  open +-*-Solver

  lem : ∀ x k r → 2 + x ≤′ r + (1 + x) * (2 + k)
  lem x k r = ≤⇒≤′ $ begin
    2 + x
      ≤⟨ m≤m+n _ _ ⟩
    2 + x + (x + (1 + x) * k + r)
      ≡⟨ solve 3 (λ x r k → con 2 :+ x :+ (x :+ (con 1 :+ x) :* k :+ r)
                              :=
                            r :+ (con 1 :+ x) :* (con 2 :+ k))
                 refl x r k ⟩
    r + (1 + x) * (2 + k)
      ∎

  helper : ∀ n → <′-Rec Pred n → Pred n
  helper n                       rec with n divMod base
  helper .(toℕ r + 0     * base) rec | result zero    r refl = (r ∷ [] , refl)
  helper .(toℕ r + suc x * base) rec | result (suc x) r refl =
    cons r (rec (suc x) (lem (pred (suc x)) k (toℕ r)))

------------------------------------------------------------------------
-- Showing digits

-- The characters used to show the first 16 digits.

digitChars : Vec Char 16
digitChars =
  '0' ∷ '1' ∷ '2' ∷ '3' ∷ '4' ∷ '5' ∷ '6' ∷ '7' ∷ '8' ∷ '9' ∷
  'a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ 'e' ∷ 'f' ∷ []

-- showDigit shows digits in base ≤ 16.

showDigit : ∀ {base} {base≤16 : True (base ≤? 16)} → Digit base → Char
showDigit {base≤16 = base≤16} d =
  Vec.lookup digitChars (Fin.inject≤ d (toWitness base≤16))
