
module Array.Repr where

open import Array.Base

open import Data.Nat
open import Data.Vec as V
open import Data.Fin using (Fin; zero; suc; raise)
open import Relation.Binary.PropositionalEquality
open import Function


-- This is a function that inductively generates a Vec-based type
-- for the given arguments of Ar.
repr-t : ∀ {a} → (X : Set a) → (n : ℕ) → (s : Vec ℕ n) → Set a
repr-t X zero s = X
repr-t X (suc n) (x ∷ s) = Vec (repr-t X n s) x

a→rt : ∀ {a}{X : Set a}{n s} → Ar X n s → repr-t X n s
a→rt {n = zero}  {s = []} (imap f) = f []
a→rt {n = suc n} {x ∷ s} (imap f) = tabulate λ i → a→rt (imap (λ iv → f (i ∷ iv)))

rt→a : ∀ {a}{X : Set a}{n s} → repr-t X n s → Ar X n s
rt→a {n = zero} {s} x = imap (λ _ → x)
rt→a {n = suc n} {s ∷ _} x = imap λ where
                                (i ∷ iv) → case rt→a (lookup x i) of λ where
                                              (imap f) → f iv


-- This is an inductive type for tensors
data Tensor {a} (X : Set a) : (n : ℕ) → (s : Vec ℕ n) → Set a where
  zz : (x : X) → Tensor X 0 []
  ss : ∀ {n m}{s : Vec ℕ n} → (v : Vec (Tensor X n s) m) → Tensor X (1 + n) (m ∷ s)

-- Ugh, well...  This is big because we have to formulate point-wise equality.
data EqTen {a} (X : Set a) : (n : ℕ) → ∀ {s s₁} → Tensor X n s → Tensor X n s₁ → Set a where
  zeq : ∀ {x} → EqTen X 0 (zz x) (zz x)
  s[] : ∀ {n}{s s₁ : Vec ℕ n}
        → (∀ i → lookup s i ≡ lookup s₁ i)
        → EqTen X (1 + n) (ss {s = s} []) (ss {s = s₁} [])
  s∷ : ∀ {n}{s s₁ : Vec ℕ n}{m}
        → (∀ i → lookup s i ≡ lookup s₁ i)
        → ∀ {x y xs ys}
        → EqTen X n {s = s} {s₁ = s₁} x y
        → EqTen X (1 + n) (ss {m = m} xs) (ss {m = m} ys)
        → EqTen X (1 + n) (ss (x ∷ xs)) (ss (y ∷ ys))

a→tensor : ∀ {a}{X : Set a}{n s} → Ar X n s → Tensor X n s
a→tensor {n = zero} {s = []} (imap f) = zz (f [])
a→tensor {n = suc n}{s = s ∷ _} (imap f) = ss $ tabulate λ i → a→tensor (imap (λ iv → f (i ∷ iv)))

tensor→a : ∀ {a}{X : Set a}{n s} → Tensor X n s → Ar X n s --(lookup s)
tensor→a {s = []} (zz x) = imap (λ _ → x)
tensor→a {s = a ∷ s} (ss v) = imap λ where
                                 (i ∷ iv) → case tensor→a (lookup v i) of λ where
                                               (imap f) → f iv


t→rt : ∀ {a}{X : Set a}{n s} → Tensor X n s → repr-t X n s
t→rt {s = []} (zz x) = x
t→rt {s = x₁ ∷ s} (ss v) = V.map t→rt v

rt→t : ∀ {a}{X : Set a}{n s} → repr-t X n s → Tensor X n s
rt→t {s = []}     x = zz x
rt→t {s = _ ∷ _} x = ss (V.map rt→t x)


module test-repr where
    a : Ar ℕ 2 (3 ∷ 3 ∷ [])
    a = cst 42

    at = (a→tensor a)
    aₜ = tensor→a at

    rt = a→rt a
    a₁ = rt→a {n = 2} {s = 3 ∷ 3 ∷ []} rt

    test₁ : t→rt at ≡ rt
    test₁ = refl

    -- This one is quite tricky to show
    --test₂ : ∀ iv → sel a₁ iv ≡ sel aₜ iv
    --test₂ iv = {!!}

