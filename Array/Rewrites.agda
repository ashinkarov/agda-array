--{-# OPTIONS --rewriting  #-}
module Array.Rewrites where

open import Array.Base
open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality

open import Function

--{-# BUILTIN REWRITE _≡_ #-}

thm : ∀ {a}{X : Set a}{s : Vec X 1} →  head s ∷ [] ≡ s
thm {s = x ∷ []} = refl

expand-s→a∘a→s : ∀ {el}{ar : Ar ℕ 1 (el ∷ [])} → ∀ (iv : Ix 1 (el ∷ []))
               → lookup (a→s ar) (ix-lookup iv zero) ≡ unimap ar iv
expand-s→a∘a→s {ar = imap f} (x ∷ []) rewrite (lookup∘tabulate (f ∘ (_∷ [])) x) = refl

imap∘unimap : ∀ {a}{X : Set a}{d s} → (ar : Ar X d s) → imap (λ iv → unimap ar iv) ≡ ar
imap∘unimap (imap ar) = refl


--{-# REWRITE expand-s→a∘a→s     #-}
--{-# REWRITE imap∘unimap        #-}
--{-# REWRITE tabulate∘lookup    #-}
--{-# REWRITE lookup∘tabulate    #-}


n+0≡n : ∀ n → n + 0 ≡ n
n+0≡n zero = refl
n+0≡n (suc n) = cong suc (n+0≡n n)

--{-# REWRITE n+0≡n     #-}


test = λ x → x + 0

