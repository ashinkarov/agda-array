
module Array.Properties where

open import Array.Base
open import Data.Fin using (Fin; zero; suc; raise; fromℕ≤; fromℕ)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality
open import Function using (_$_; _∘_; case_of_)

open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Binary using (Decidable; Rel)


open import Data.Maybe
open import Data.Sum



sel-ext : ∀ {a}{X : Set a}{d s} → (f : Ix d s → X)
        → (iv jv : Ix d s)
        → iv =ix jv
        → f iv ≡ f jv
sel-ext {d = zero}  f [] [] pf = refl
sel-ext {d = suc d} f (i ∷ iv) (j ∷ jv) pf rewrite (pf zero) = sel-ext (f ∘ (j ∷_)) iv jv (pf ∘ suc)


s→a∘a→s : ∀ {n} → (a : Ar ℕ 1 (n ∷ [])) → s→a (a→s a) =a a
s→a∘a→s (imap x) (i ∷ []) = lookup∘tabulate _ i


a→s∘s→a : ∀ {n} → (v : Vec ℕ n) → a→s (s→a v) =s v
a→s∘s→a v i = lookup∘tabulate _ i


refl-=a : ∀ {a}{X : Set a}{d s}{x : Ar X d s}
        → x =a x
refl-=a {x = imap x} iv = refl

sym-=a : ∀ {a}{X : Set a}{d s}{l r : Ar X d s}
       → l =a r → r =a l
sym-=a {l = imap f} {imap g} l=r = sym ∘ l=r


trans-=a : ∀ {a}{X : Set a}{d s}{x y z : Ar X d s}
         → x =a y → y =a z → x =a z
trans-=a {x = imap x} {imap y} {imap z} x=y y=z iv
  = trans (x=y iv) (y=z iv)

_<v?_ : ∀ {n} → Decidable (_<s_ {n = n})
[] <v? [] = yes λ ()
(x ∷ xs) <v? (y ∷ ys) = case (x <? y) , (xs <v? ys) of λ where
                         (yes pf-xy , yes pf-xsys) → yes λ where
                                                         zero    → pf-xy
                                                         (suc i) → pf-xsys i
                         (no pf-xy , _) → no (not-head pf-xy)
                         (_ , no pf-xsys) → no (not-tail pf-xsys) 
  where        
    p1 : ∀ {n}{x y}{xs ys : Vec ℕ n} → (x ∷ xs) <s (y ∷ ys) → x < y
    p1 pf = pf zero

    p2 : ∀ {n}{x y}{xs ys : Vec ℕ n} → (x ∷ xs) <s (y ∷ ys) → xs <s ys
    p2 pf = pf ∘ (raise 1)

    not-head : ∀ {n}{x y}{xs ys : Vec ℕ n} → ¬ (x < y) → ¬ ((x ∷ xs) <s (y ∷ ys)) 
    not-head pf-xy pf-xxs-yys = contradiction (p1 pf-xxs-yys) pf-xy

    not-tail : ∀ {n}{x y}{xs ys : Vec ℕ n} → ¬ (xs <s ys) → ¬ ((x ∷ xs) <s (y ∷ ys))
    not-tail pf-xsys pf-xxs-yys = contradiction (p2 pf-xxs-yys) pf-xsys 


-- Index curry makes it possible to fix the first position of
-- the index vector and select a sub-array.
ix-curry : ∀ {a}{X : Set a}{d s ss} → (f : Ix (suc d) (s ∷ ss) → X) → (Fin s) → (Ix d ss → X)
ix-curry f x xs = f (x ∷ xs)


ARel : ∀ {a}{A : Set a} → (P : Rel A a) -- → Decidable P
     → ∀ {d s} → Ar A d s → Ar A d s → Set a
ARel p (imap x) (imap y) = ∀ iv → p (x iv) (y iv)

--test = ARel _≥_ 

-- If a < b, then sub-arays a[i] < b[i], where a[i] and b[i]
-- is non-scalar selection where the head of index-vector is
-- fixed to i.
all-subarrays : ∀ {d s ss}{a}{X : Set a}{_~_ : Rel X a}
              → let _~a_ = ARel _~_ in
                (a b : Ix (suc d) (suc s ∷ ss) → X)
              → imap a ~a imap b
              → ∀ i → (imap (ix-curry a i) ~a imap (ix-curry b i))
all-subarrays a b pf i iv = pf (i ∷ iv)

-- If all a[i] < b[i], then a < b.
from-subarrays : ∀ {d s ss}{a}{X : Set a}{_~_ : Rel X a}
               → let _~a_ = ARel _~_ in
                 (a b : Ix (suc d) (suc s ∷ ss) → X)
               → (∀ i → (imap (ix-curry a i) ~a imap (ix-curry b i)))
               → imap a ~a imap b
from-subarrays a b pf (x ∷ iv) = pf x iv

-- If there exists i such that ¬ a[i] < b[i], then ¬ a < b.
not-subarrays : ∀ {d s ss}{a}{X : Set a}{_~_ : Rel X a}
              → let _~a_ = ARel _~_ in
                (a b : Ix (suc d) (suc s ∷ ss) → X)
              → (i : Fin (suc s))
              → ¬ imap (ix-curry a i) ~a imap (ix-curry b i)
              → ¬ imap a ~a imap b
not-subarrays a b i ¬p pp = contradiction pp λ z → ¬p (λ iv → z (i ∷ iv))


module not-needed where
  unmaybe : ∀ {a}{X : Set a}{n}
          → (x : Vec (Maybe X) n)
          → (∀ i → lookup x i ≢ nothing)
          → Vec X n
  unmaybe {n = zero} x pf = []
  unmaybe {n = suc n} (just x ∷ xs) pf = x ∷ unmaybe xs (pf ∘ suc)
  unmaybe {n = suc n} (nothing ∷ x₁) pf = contradiction refl $ pf zero


  check-all-nothing : ∀ {a}{X : Set a}{n}
                    → (x : Vec (Maybe X) n)
                    → Maybe ((i : Fin n) → lookup x i ≢ nothing)
  check-all-nothing {n = zero} x = nothing
  check-all-nothing {n = suc n} (just x  ∷ xs) with check-all-nothing xs
  check-all-nothing {n = suc n} (just x ∷ xs) | just f = just λ { zero → λ () ; (suc k) → f k }
  check-all-nothing {n = suc n} (just x ∷ xs) | nothing = nothing
  check-all-nothing {n = suc n}  _  = nothing



check-all-subarrays : ∀ {d s ss}{a}{X : Set a}{_~_ : Rel X a}
                    → let _~a_ = ARel _~_ in
                      (a b : Ix (suc d) (suc s ∷ ss) → X)
                    → (∀ i → Dec (imap (ix-curry a i) ~a imap (ix-curry b i)))
                    → (Σ (Fin (suc s)) λ i → ¬ (imap (ix-curry a i) ~a imap (ix-curry b i)))
                    ⊎ (∀ i → (imap (ix-curry a i) ~a imap (ix-curry b i)))
check-all-subarrays {s = zero}  a b pf with (pf zero)
check-all-subarrays {_} {zero}  a b pf | yes p = inj₂ λ { zero → p }
check-all-subarrays {_} {zero}  a b pf | no ¬p = inj₁ (zero , ¬p)
check-all-subarrays {s = suc s} {_~_ = _~_} a b pf with check-all-subarrays {_~_ = _~_}
                                                                (λ { (i ∷ iv) → a (suc i ∷ iv)})
                                                                (λ { (i ∷ iv) → b (suc i ∷ iv)})
                                                                (pf ∘ suc)
                                         -- If we have a subarray that is not <
                                         -- simply propagate it further, updating the index
check-all-subarrays {_} {suc s} a b pf | inj₁ (i , a≁b) = inj₁ (suc i , a≁b)
check-all-subarrays {_} {suc s} a b pf | inj₂ y with (pf zero)
check-all-subarrays {_} {suc s} a b pf | inj₂ y | yes p = inj₂ λ { zero → p ; (suc k) → y k }
check-all-subarrays {_} {suc s} a b pf | inj₂ y | no ¬p = inj₁ (zero , ¬p)

{-
-- For arrays a and b, if f : ∀ i → Dec (a[i] < b[i]),
-- check whether:
--   1. There exists i, for which ¬ a[i] < b[i]
--   2. Otherwise construct a function of type ∀ i → a[i] < b[i]
check-all-subarrays : ∀ {d s ss}
                    → (a b : Ix (suc d) (suc s ∷ ss) → ℕ)
                    → (∀ i → Dec (imap (ix-curry a i) <a imap (ix-curry b i)))
                    → (Σ (Fin (suc s)) λ i → ¬ (imap (ix-curry a i) <a imap (ix-curry b i)))
                    ⊎ (∀ i → (imap (ix-curry a i) <a imap (ix-curry b i)))
check-all-subarrays {s = zero}  a b pf with (pf zero)
check-all-subarrays {_} {zero}  a b pf | yes p = inj₂ λ { zero → p }
check-all-subarrays {_} {zero}  a b pf | no ¬p = inj₁ (zero , ¬p)
check-all-subarrays {s = suc s} a b pf with check-all-subarrays (λ { (i ∷ iv) → a (suc i ∷ iv)})
                                                                (λ { (i ∷ iv) → b (suc i ∷ iv)})
                                                                (pf ∘ suc)
                                         -- If we have a subarray that is not <
                                         -- simply propagate it further, updating the index
check-all-subarrays {_} {suc s} a b pf | inj₁ (i , a≮b) = inj₁ (suc i , a≮b)
check-all-subarrays {_} {suc s} a b pf | inj₂ y with (pf zero)
check-all-subarrays {_} {suc s} a b pf | inj₂ y | yes p = inj₂ λ { zero → p ; (suc k) → y k }
check-all-subarrays {_} {suc s} a b pf | inj₂ y | no ¬p = inj₁ (zero , ¬p)
-}


mk-dec-arel : ∀ {a}{X : Set a} → (p : Rel X a) → Decidable p → ∀ {d s} → Decidable (ARel p {d = d} {s = s})
mk-dec-arel _~_ _~?_ {zero} {[]} (imap x) (imap x₁) with x [] ~? x₁ []
mk-dec-arel _~_ _~?_ {zero} {[]} (imap x) (imap x₁) | yes p = yes λ { [] → p }
mk-dec-arel _~_ _~?_ {zero} {[]} (imap x) (imap x₁) | no ¬p =  no λ p → contradiction (p []) ¬p
mk-dec-arel _~_ _~?_ {suc d} {zero  ∷ ss} (imap x) (imap x₁) = yes λ iv → magic-fin $ ix-lookup iv zero
mk-dec-arel _~_ _~?_ {suc d} {suc s ∷ ss} (imap x) (imap x₁) = case-analysis
  where
    case-analysis : _ -- Dec ((i : Ix (suc d) (suc s ∷ ss)) → suc (x i) ≤ x₁ i)
    case-analysis = let _~a?_ = mk-dec-arel _~_ _~?_
                    in case check-all-subarrays {_~_ = _~_}
                          x x₁ (λ i → imap (ix-curry x i)
                                      ~a? imap (ix-curry x₁ i)) of λ where
                       -- In this case we have an index and a proof that
                       -- subarray at this index is not <
                       (inj₁ (i , x≁x₁)) → no $ not-subarrays {_~_ = _~_} x x₁ i x≁x₁
                       -- In this case we have a function that for every index
                       -- returns a proof that sub-arrays are <
                       (inj₂ f) → yes (from-subarrays {_~_ = _~_} x x₁ f)

_<a?_ = mk-dec-arel _<_ _<?_
_≥a?_ = mk-dec-arel _≥_ _≥?_

{-
_<a?_ : ∀ {d s} → Decidable (_<a_ {d = d} {s = s})
_<a?_ {zero} {[]} (imap x) (imap x₁) with x [] <? x₁ []
_<a?_ {zero} {[]} (imap x) (imap x₁) | yes p = yes λ { [] → p }
_<a?_ {zero} {[]} (imap x) (imap x₁) | no ¬p = no λ p → contradiction (p []) ¬p
_<a?_ {suc d} {0 ∷ ss} (imap x) (imap x₁) = yes λ iv → magic-fin $ ix-lookup iv zero
_<a?_ {suc d} {(suc s) ∷ ss} (imap x) (imap x₁) = case-analysis
  where
    case-analysis : _ -- Dec ((i : Ix (suc d) (suc s ∷ ss)) → suc (x i) ≤ x₁ i)
    case-analysis =  case check-all-subarrays {_~_ = _<_}
                          x x₁ (λ i → imap (ix-curry x i)
                                      <a? imap (ix-curry x₁ i)) of λ where
                       -- In this case we have an index and a proof that
                       -- subarray at this index is not <
                       (inj₁ (i , x≮x₁)) → no $ not-subarrays {_~_ = _<_} x x₁ i x≮x₁
                       -- In this case we have a function that for every index
                       -- returns a proof that sub-arrays are <
                       (inj₂ f) → yes (from-subarrays {_~_ = _<_} x x₁ f)


_≥a?_ : ∀ {d s} → Decidable (_≥a_ {d = d} {s = s})
_≥a?_ {zero} {[]} (imap x) (imap x₁) with x [] ≥? x₁ []
_≥a?_ {zero} {[]} (imap x) (imap x₁) | yes p = yes λ { [] → p }
_≥a?_ {zero} {[]} (imap x) (imap x₁) | no ¬p = no λ p → contradiction (p []) ¬p
_≥a?_ {suc d} {s} (imap x) (imap x₁) = {!!}
-}

private
  thm : ∀ { i s } → i < s → s ∸ i ∸ 1 + suc i ≡ s
  thm {i} {s} pf = begin
                      s ∸ i ∸ 1 + suc i ≡⟨ cong (_+ (suc i)) (∸-+-assoc s i 1) ⟩
                      s ∸ (i + 1) + suc i ≡⟨ cong (_+ (suc i)) (cong (s ∸_) (+-comm i 1))  ⟩
                      s ∸ suc i + suc i ≡⟨ m∸n+n≡m pf ⟩
                      s
                   ∎
                 where open ≡-Reasoning 


-- XXX can we do this simpler?
≮a⇒∃ : ∀ {d s}{a b : Ar _ d s} → ¬ a <a b → Σ (Ix d s) λ iv → ¬ (unimap a iv < unimap b iv)
≮a⇒∃ {zero} {[]} {imap f} {imap g} ¬a<b with f [] <? g []
≮a⇒∃ {zero} {[]} {imap f} {imap g} ¬a<b | yes p = contradiction (λ { [] → p}) ¬a<b
≮a⇒∃ {zero} {[]} {imap f} {imap g} ¬a<b | no ¬p = [] , ¬p
≮a⇒∃ {suc d} {zero ∷ ss} {imap f} {imap g} ¬a<b = contradiction (λ iv → magic-fin $ ix-lookup iv zero) ¬a<b
≮a⇒∃ {suc d} {suc s ∷ ss} {imap f} {imap g} ¬a<b = case-analysis
  where
    case-analysis : _
    case-analysis =  case check-all-subarrays {_~_ = _<_}
                          f g (λ i → imap (ix-curry f i)
                                      <a? imap (ix-curry g i)) of λ where
                          (inj₁ (i , f≮g)) → let
                                               iv , pf = ≮a⇒∃ f≮g
                                             in (i ∷ iv) , λ pp → contradiction pp pf
                          (inj₂ pf) → contradiction (from-subarrays {_~_ = _<_} f g pf) ¬a<b



module try-irrelevant where
  -- XXX this shouldn't be here, this is for now to avoid
  -- dependencies in the modules.
  -- Inverse of the above
  a→ix : ∀ {d} --{s : Fin d → ℕ}
       → (ax sh : Ar ℕ 1 (d ∷ []))
       -- XXX we can make this inequality irrelevant
       -- and recompute it when it is needed, as <a
       -- is decideable.
       → .(ax <a sh)
       → Ix d (a→s sh)
  a→ix {d} (imap axf) (imap shf) ax<sh = ix-tabulate from-pf
    where
      pf : _
      pf = recompute (imap axf <a? imap shf) ax<sh

      from-pf : _
      from-pf i rewrite (lookup∘tabulate (shf ∘ (_∷ [])) i)
        = let
            ix : Ix 1 (d ∷ [])
            ix = i ∷ []
            r = raise (shf ix ∸ axf ix ∸ 1) $ fromℕ (axf ix)

           in subst Fin (thm (pf ix)) r --fromℕ≤ (ax<sh (i ∷ []))


a→ix : ∀ {d} --{s : Fin d → ℕ}
     → (ax sh : Ar ℕ 1 (d ∷ []))
     → (ax <a sh)
     → Ix d (a→s sh)
a→ix {d} (imap axf) (imap shf) ax<sh = ix-tabulate from-pf
  where
    from-pf : _
    from-pf i rewrite (lookup∘tabulate (shf ∘ (_∷ [])) i)
      = fromℕ≤ (ax<sh (i ∷ []))

