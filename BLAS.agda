{-# OPTIONS --rewriting  #-}
open import Array 
open import Array.APL using (reduce-1d)

open import Data.Nat
open import Data.Vec
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality
open import Function


sum-1d : ∀ {n} → Ar ℕ 1 (n ∷ []) → ℕ
sum-1d v = reduce-1d v _+_ 0

zipw : ∀ {a}{X : Set a}{d s} → (X → X → X) → Ar X d s → Ar X d s → Ar X d s
zipw _⊕_ (imap a) (imap b) = imap λ iv → a iv ⊕ b iv

hd : ∀ {n s : ℕ}{ss : Vec ℕ n} → Ix (suc n) (s ∷ ss) → Fin s
hd ix = ix-lookup ix zero



vec-mat-mul : ∀ {n m} → Ar ℕ 2 (m ∷ n ∷ []) → Ar ℕ 1 (n ∷ []) → Ar ℕ 1 (m ∷ [])
vec-mat-mul (imap a) b = imap λ iv → sum-1d (zipw _*_ (imap λ jv → a (iv ix++ jv)) b)

twice : ∀ {n} → (M : Ar ℕ 2 (n ∷ n ∷ [])) → (V : Ar ℕ 1 (n ∷ [])) → Ar ℕ 1 (n ∷ [])
twice m v = vec-mat-mul m (vec-mat-mul m v)



iterate-1 : ∀ {a}{X : Set a}{n} → (Fin n → X) → (X → X → X) → X → X
iterate-1 {n = zero}  f _⊕_ neut = neut
iterate-1 {n = suc n} f _⊕_ neut = f zero ⊕ iterate-1 (f ∘ suc) _⊕_ neut

red-iter : ∀ {a}{X : Set a}{n} → (f : Ix 1 (n ∷ []) → X) → (op : X → X → X) → (neut : X)
         → reduce-1d (imap f) op neut ≡ iterate-1 (λ i → f (i ∷ [])) op neut
red-iter {n = zero}  f op neut = refl
red-iter {n = suc n} f op neut = cong (λ x → op _ x) (red-iter (λ iv → f (suc (hd iv) ∷ [])) op neut)



{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE red-iter    #-}


thm : ∀ {n} → (m : Ar ℕ 2 (n ∷ n ∷ [])) → (v : Ar _ _ (n ∷ [])) → ∀ iv → unimap (twice m v) iv ≡ {!!}
thm (imap m) (imap v) (i ∷ []) = {!!}


-- A * v = { i → Σ Aᵢ×v }
-- A * A * v = { i → Σ Aᵢ×v }
