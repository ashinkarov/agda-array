
module Array.Base where

open import Data.Nat
open import Data.Nat.DivMod             using (_div_ ; _mod_)
open import Data.Nat.Properties
open import Data.Vec
open import Data.Vec.Properties         using (lookup∘tabulate)
open import Data.Fin.Base               hiding (_<_; _+_)
open import Data.Fin.Properties         hiding (_≟_)
open import Function                    using (_$_; _∘_; case_of_)
open import Data.Product                using (Σ; _,_)
open import Relation.Binary.PropositionalEquality
                                        using (_≡_; _≢_; refl; subst; sym)
open import Relation.Nullary            using (Dec; yes; no)
open import Relation.Nullary.Decidable  using (fromWitnessFalse)
open import Relation.Nullary.Negation   using (contradiction)
open import Data.Sum                    using (inj₁; inj₂)

infixr 5 _∷_
data Ix : (d : ℕ) → (s : Vec ℕ d) → Set where
  []   : Ix 0 []
  _∷_  : ∀ {d s x} → Fin x → (ix : Ix d s) → Ix (suc d) (x ∷ s)


ix-lookup : ∀ {d s} → Ix d s → (i : Fin d) → Fin (lookup s i)
ix-lookup [] ()
ix-lookup (x ∷ ix) zero = x
ix-lookup (x ∷ ix) (suc i) = ix-lookup ix i

ix-tabulate : ∀ {d s} → ((i : Fin d) → Fin (lookup s i)) → Ix d s
ix-tabulate {s = []} f = []
ix-tabulate {s = x ∷ s} f = f zero ∷ ix-tabulate (f ∘ suc)

ix→v : ∀ {d s} → Ix d s → Vec ℕ d
ix→v [] = []
ix→v (x ∷ xs) = toℕ x ∷ ix→v xs



data Ar {a} (X : Set a) (d : ℕ) (s : Vec ℕ d) : Set a where
  imap : (Ix d s → X) → Ar X d s


unimap : ∀ {a}{X : Set a}{d s} → Ar X d s → Ix d s → X
unimap (imap x) = x


cst : ∀ {a}{X : Set a}{d s} → X → Ar X d s
cst x = imap λ _ → x

-- Promoting shapes into 1-dimensional array of integers
-- and back.
s→a : ∀ {n} → Vec ℕ n → Ar ℕ 1 (n ∷ [])
s→a s = imap (λ iv → lookup s $ ix-lookup iv zero )

a→s : ∀ {s} → Ar ℕ 1 (s ∷ []) → Vec ℕ s
a→s (imap x) = tabulate λ i → x (i ∷ [])

-- Here we define < on shape-like objects and demonstrate that
-- this relation is decideable.
_<s_ : ∀ {n} → Vec ℕ n → Vec ℕ n → Set
a <s b = ∀ i → lookup a i < lookup b i

-- XXX This might be just equality
_=s_ : ∀ {n} → Vec ℕ n → Vec ℕ n → Set
a =s b = ∀ i → lookup a i ≡ lookup b i

_<a_ : ∀ {d s} → Ar ℕ d s → Ar ℕ d s → Set
imap f <a imap g = ∀ iv → f iv < g iv

_≥a_ : ∀ {d s} → Ar ℕ d s → Ar ℕ d s → Set
imap f ≥a imap g = ∀ iv → f iv ≥ g iv

_=a_ : ∀ {a}{X : Set a}{d s} → Ar X d s → Ar X d s → Set a
imap f =a imap g = ∀ iv → f iv ≡ g iv

_=ix_ : ∀ {d s} → Ix d s → Ix d s → Set
iv =ix jv = ∀ i → ix-lookup iv i ≡ ix-lookup jv i


subst-ix : ∀ {n}{s s₁ : Vec ℕ n} → s =s s₁ → Ix n s → Ix n s₁
subst-ix {zero} {[]} {[]} pf []  = []
subst-ix {suc n} {x ∷ xs} {y ∷ ys} pf (i ∷ iv) rewrite (pf zero) = i ∷ subst-ix (pf ∘ suc) iv

subst-ar : ∀ {a}{X : Set a}{n}{s s₁ : Vec ℕ n} → s =s s₁ → Ar X n s → Ar X n s₁
subst-ar pf (imap f) = imap λ iv → f $ subst-ix (sym ∘ pf) iv

subst-ar-d : ∀ {a}{X : Set a}{n m}{s : Vec ℕ n}{s₁ : Vec ℕ m}
           → (n=m : n ≡ m)
           → s =s (subst (Vec ℕ) (sym n=m) s₁)
           → Ar X n s → Ar X m s₁
subst-ar-d refl pf a = subst-ar pf a



-- If we have an index, produce a pair containing an array representation
-- and the proof that the index is smaller than the shape.
ix→a : ∀ {d}{s : Vec ℕ d}
     → (ix : Ix d s)
     → Σ (Ar ℕ 1 (d ∷ [])) λ ax → ax <a (s→a s) 
ix→a ix = imap (λ iv → toℕ $ ix-lookup ix (ix-lookup iv zero)) ,
          λ iv → toℕ<n (ix-lookup ix (ix-lookup iv zero))
          


{-
try : ∀ a b → .(a < b) → Fin b
try a b pf = let
               x = raise (b ∸ a) (fromℕ a)
             in {!Array.Properties._<a?_!} 
-}

-- XXX we can do this via imap/lookup if we want to, so that it
-- extracts to more efficient code.
infixl 10 _ix++_ 
_ix++_ : ∀ {n m s s₁}
       → (iv : Ix n s)
       → (jv : Ix m s₁)
       → Ix (n + m) (s ++ s₁)
_ix++_ {s = []}     {s₁} iv jv = jv
_ix++_ {s = s ∷ ss} {s₁} (i ∷ iv) jv = i ∷ iv ix++ jv


nest : ∀ {a}{X : Set a}{n m s s₁}
     →  Ar X (n + m) (s ++ s₁)
     →  Ar (Ar X m s₁) n s
nest (imap f) = imap (λ iv → imap (λ jv → f (iv ix++ jv)))


-- Take and drop for indices
take-ix-l : ∀ {n m} → (s : Vec ℕ n) (s₁ : Vec ℕ m)
          → Ix (n + m) (s ++ s₁) 
          → Ix n s
take-ix-l []       s₁ ix = []
take-ix-l (s ∷ ss) s₁ (x ∷ ix) = x ∷ take-ix-l ss s₁ ix

take-ix-r : ∀ {n m} → (s : Vec ℕ n) (s₁ : Vec ℕ m)
          → Ix (n + m) (s ++ s₁) 
          → Ix m s₁
take-ix-r [] s₁ ix = ix
take-ix-r (x ∷ s) s₁ (x₁ ∷ ix) = take-ix-r s s₁ ix


-- Flatten the first nesting of the Ar
flatten : ∀ {a}{X : Set a}{n m}{s : Vec ℕ n}{s₁ : Vec ℕ m}
        → Ar (Ar X m s₁) n s
        → Ar X (n + m) (s ++ s₁)
flatten (imap f) = imap λ iv → case f (take-ix-l _ _ iv) of λ where
                              (imap g) → g (take-ix-r _ _ iv)

prod : ∀ {n} → (Vec ℕ n) → ℕ
prod s = foldr _ _*_ 1 s

magic-fin : ∀ {a}{X : Set a} → Fin 0 → X
magic-fin ()

a*b≢0⇒a≢0 : ∀ {a b} → a * b ≢ 0 → a ≢ 0
a*b≢0⇒a≢0 {zero}    {b} 0≢0 0≡0 = 0≢0 0≡0
a*b≢0⇒a≢0 {(suc a)} {b} _       = λ ()

a*b≢0⇒b≢0 : ∀ {a b} → a * b ≢ 0 → b ≢ 0
a*b≢0⇒b≢0 {a} {b} rewrite (*-comm a b) = a*b≢0⇒a≢0


-- XXX currently this is not efficient way to convert between indices and
-- offsets, as we are doing it form left to right.  Computing in reverse
-- makes more sense.  Something for later.

off→idx : ∀ {n} → (sh : Vec ℕ n)
        → Ix 1 (prod sh ∷ [])
        → Ix n sh
off→idx [] iv = []
off→idx (s ∷ sh) iv with prod (s ∷ sh) ≟ 0
off→idx (s ∷ sh) iv | yes p rewrite p = magic-fin $ ix-lookup iv zero
off→idx (s ∷ sh) (off ∷ []) | no ¬p = let
                                         o = toℕ off
                                         tl = prod sh
                                         tl≢0 = fromWitnessFalse (a*b≢0⇒b≢0 {a = s} ¬p)
                                         s≢0 = fromWitnessFalse (a*b≢0⇒a≢0 {a = s} ¬p)
                                         x = (o div tl) {≢0 = tl≢0}
                                     in (x mod s) {≢0 = s≢0} ∷ off→idx sh ((x mod tl) {≢0 = tl≢0} ∷ [])

 
-- [x , y] < [a , b] ⇒ rowmaj [x , y] < a*b ⇒ x*b+y < a*b  
rm-thm : ∀ {a b} → (x : Fin a) → (b ≢ 0) → (y : Fin b) → ((toℕ y) + (toℕ x) * b  < (a * b)) 
rm-thm {a} {ℕ.zero}  x pf y = contradiction (refl {x = 0}) pf
rm-thm {ℕ.zero} {ℕ.suc b₁} () pf y 
rm-thm {ℕ.suc a₁} {ℕ.suc b₁} x pf y = +-mono-≤ (toℕ<n y) $   *-monoˡ-≤ (ℕ.suc b₁) (≤-pred $ toℕ<n x)  

Πs≡0⇒Fin0 : ∀ {n} → (s : Vec ℕ n)
          → (Ix n s) → (prod s ≡ 0)
          → Fin 0
Πs≡0⇒Fin0 (x ∷ s) (i ∷ iv) Πxs≡0 with  m*n≡0⇒m≡0∨n≡0 x Πxs≡0
Πs≡0⇒Fin0 (x ∷ s) (i ∷ iv) Πxs≡0 | inj₁ x≡0 rewrite x≡0 = i
Πs≡0⇒Fin0 (x ∷ s) (i ∷ iv) Πxs≡0 | inj₂ Πs≡0 = Πs≡0⇒Fin0 s iv Πs≡0


idx→off : ∀ {n} → (s : Vec ℕ n)
        → (iv : Ix n s)
        → Ix 1 (prod s ∷ []) 
idx→off [] iv = zero ∷ iv
idx→off (s ∷ sh) (i ∷ iv) with prod (s ∷ sh) ≟ 0
idx→off (s ∷ sh) (i ∷ iv) | yes p rewrite p = magic-fin $ Πs≡0⇒Fin0 (s ∷ sh) (i ∷ iv) p
idx→off (s ∷ sh) (i ∷ iv) | no ¬p = fromℕ≤ (rm-thm i (a*b≢0⇒b≢0 {a = s} ¬p) (ix-lookup (idx→off sh iv) zero)) ∷ []


mkempty : ∀ {a}{X : Set a}{n} → (s : Vec ℕ n) → (prod s ≡ 0) → Ar X n s
mkempty {X = X} {n = n} s Πs≡0 = imap empty
  where
    empty : _
    empty iv = magic-fin $ Πs≡0⇒Fin0 s iv Πs≡0
