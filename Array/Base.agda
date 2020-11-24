
module Array.Base where

open import Data.Nat
open import Data.Nat.DivMod             --using (_div_ ; _mod_; _/_; m/n*n≤m)
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Data.Vec
open import Data.Vec.Properties         using (lookup∘tabulate)
open import Data.Fin.Base               hiding (_<_; _+_)
open import Data.Fin.Properties         hiding (_≟_; <-cmp; ≤-trans; <-trans)
open import Function                    using (_$_; _∘_; case_of_)
open import Data.Product                using (Σ; _,_)
open import Relation.Binary.PropositionalEquality   --using (_≡_; _≢_; refl; subst; sym; cong; cong₂)
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Nullary            --using (Dec; yes; no)
open import Relation.Nullary.Decidable  --using (fromWitnessFalse; False)
open import Relation.Nullary.Negation   --using (contradiction)
open import Data.Sum                    using (inj₁; inj₂)
open import Data.Empty

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

--data Ar {a} (X : Set a) (d : ℕ) (s : Vec ℕ d) : Set a where
--  imap : (Ix d s → X) → Ar X d s
--
-- We used this type before `withReconstructed` was introduced, so that
-- we could obtain the shape of arrays at each imap.  Now we have switched
-- to the record that gives us η-equality.
--
--data Ar {a} (X : Set a) (d : ℕ) : (Vec ℕ d) → Set a where
--  imap : ∀ {s} → (Ix d s → X) → Ar X d s

record Ar {a} (X : Set a) (d : ℕ) (s : Vec ℕ d) : Set a where
  constructor imap
  field sel : Ix d s → X
open Ar public


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




-- A basic fact about division that is not yet in the stdlib.
/-mono-x : ∀ {a b c} → a < b * c → (c≢0 : False (c ≟ 0))
         → (a / c) {≢0 = c≢0} < b
/-mono-x {a}{b}{c} a<b*c c≢0 with <-cmp ((a / c) {≢0 = c≢0}) b
/-mono-x {a} {b} {c} a<b*c c≢0 | tri< l< _ _ = l<
/-mono-x {a} {b} {c} a<b*c c≢0 | tri≈ _ l≡ _ = let
     a<a/c*c = subst (a <_) (cong₂ _*_ (sym l≡) refl) a<b*c
     a/c*c≤a = m/n*n≤m a c {≢0 = c≢0}
     a<a = ≤-trans a<a/c*c a/c*c≤a
   in contradiction a<a (n≮n a)
/-mono-x {a} {b} {suc c} a<b*c c≢0 | tri> _ _ l> = let
     b*c<a/c*c = *-monoˡ-< c l>
     a/c*c≤a = m/n*n≤m a (suc c) {≢0 = c≢0}
     b*c≤a = ≤-trans b*c<a/c*c a/c*c≤a
     a<a = <-trans a<b*c b*c≤a
   in contradiction a<a (n≮n a)


/-mono-f : ∀ {a b c} → a < b * c → (b≢0 : False (b ≟ 0))
         → (a / b) {≢0 = b≢0} < c
/-mono-f {b = b}{c} a<b*c ≢0 rewrite *-comm b c = /-mono-x a<b*c ≢0


divmod-thm : ∀ {a b m n}
           → (n≢0 : n ≢ 0)
           → a ≡ (m % n) {≢0 = fromWitnessFalse n≢0}
           → b ≡ (m / n) {≢0 = fromWitnessFalse n≢0} * n
             → m ≡ a + b
divmod-thm {n = zero} n≢0 _ _ = contradiction refl n≢0
divmod-thm {m = m}{n = suc n} n≢0 refl refl = m≡m%n+[m/n]*n m n



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
                                     in {- off / tl -} (fromℕ< (/-mono-x (toℕ<n off) tl≢0))
                                        {- rec call -} ∷ (off→idx sh ((o mod tl) {tl≢0} ∷ []))

module test-oi where
  open import Data.Fin using (#_)
  test-oi₁ : off→idx (10 ∷ 5 ∷ []) (# 40 ∷ []) ≡ (# 8) ∷ (# 0) ∷ []
  test-oi₁ = refl


-- [x , y] < [a , b] ⇒ rowmaj [x , y] < a*b ⇒ x*b+y < a*b
rm-thm : ∀ {a b} → (x : Fin a) → (b ≢ 0) → (y : Fin b) → ((toℕ y) + (toℕ x) * b  < (a * b))
rm-thm {a} {ℕ.zero}  x pf y = contradiction (refl {x = 0}) pf
rm-thm {ℕ.zero} {ℕ.suc b₁} () pf y
rm-thm {ℕ.suc a₁} {ℕ.suc b₁} x pf y = +-mono-≤ (toℕ<n y) $ *-monoˡ-≤ (ℕ.suc b₁) (≤-pred $ toℕ<n x)


v-rm-thm : ∀ {a b x y b≢0} → (toℕ $ fromℕ< (rm-thm {a = a} {b = b} x b≢0 y)) ≡ (toℕ y) + (toℕ x) * b
v-rm-thm {suc a} {suc b} {x} {y} {≢0} = toℕ-fromℕ< (rm-thm x ≢0 y)


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
idx→off (s ∷ sh) (i ∷ iv) | no ¬p = fromℕ< (rm-thm i (a*b≢0⇒b≢0 {a = s} ¬p) (ix-lookup (idx→off sh iv) zero)) ∷ []

module test-io where
  open import Data.Fin using (#_)
  test-io₁ : idx→off (10 ∷ 5 ∷ []) (# 8 ∷ # 0 ∷ []) ≡ # 40 ∷ [] 
  test-io₁ = refl

mkempty : ∀ {a}{X : Set a}{n} → (s : Vec ℕ n) → (prod s ≡ 0) → Ar X n s
mkempty {X = X} {n = n} s Πs≡0 = imap empty
  where
    empty : _
    empty iv = magic-fin $ Πs≡0⇒Fin0 s iv Πs≡0


-- Fin fact:
Fin1≡0 : (x : Fin 1) → x ≡ zero
Fin1≡0 zero = refl


-- XXX This should be moved to Properties
io-oi : ∀ {n}{x : Vec _ n}{i : Fin (prod x)}
      → idx→off x (off→idx x (i ∷ [])) ≡ i ∷ []
io-oi {zero} {[]}{i} = cong (_∷ []) (sym (Fin1≡0 i))
io-oi {suc n} {x ∷ x₁}{i} with prod (x ∷ x₁) ≟ 0
... | yes p = ⊥-elim $ ¬Fin0 (subst Fin p i)
... | no ¬p with prod (x ∷ x₁) ≟ 0
io-oi {suc n} {x ∷ x₁} {i} | no ¬p | yes q = contradiction q ¬p
io-oi {suc n} {x ∷ x₁} {i} | no ¬p | no ¬q
  = cong (_∷ []) (toℕ-injective (trans (v-rm-thm {a = x} {b = prod x₁})
                                       (sym (divmod-thm
                                                 {a = toℕ (ix-lookup (idx→off x₁ (off→idx x₁ _)) zero)}
                                                 (a*b≢0⇒b≢0 {a = x} ¬p)
                                                 (trans (cong (λ x → toℕ (ix-lookup x zero))
                                                              (io-oi {x = x₁}))
                                                        mod⇒%)
                                                 (mono⇒/* {b = x} {c = prod x₁})))))
  where
    mono⇒/* : ∀ {b c}{i : Fin (b * c)}{≢0 : False (c ≟ 0)}
            → toℕ {n = b} (fromℕ< (/-mono-x (toℕ<n i) (≢0))) * c ≡ (toℕ i / c) {≢0} * c
    mono⇒/* {b} {c} {i} {≢0} = cong (_* c) (toℕ-fromℕ< (/-mono-x (toℕ<n i) ≢0))

    mod⇒% :  ∀ {n}{i : Fin n}{a}{≢0 : False (a ≟ 0)} → toℕ ((toℕ i mod a){≢0}) ≡ (toℕ i % a) {≢0}
    mod⇒% {n} {i} {suc a} = trans (toℕ-fromℕ< (m%n<n (toℕ i) a)) refl



m≡m+x⇒0≡x : ∀ {m x} → m ≡ m + x → 0 ≡ x
m≡m+x⇒0≡x {m}{x} m≡m+x = +-cancelˡ-≡ m (trans (+-identityʳ m) m≡m+x)

a*b≡0⇒b≢0⇒a≡0 : ∀ {a b} → a * b ≡ 0 → b ≢ 0 → a ≡ 0
a*b≡0⇒b≢0⇒a≡0 {a}{b} a*b≡0 b≢0 with (m*n≡0⇒m≡0∨n≡0 a a*b≡0)
a*b≡0⇒b≢0⇒a≡0 {a} {b} a*b≡0 b≢0 | inj₁ x = x
a*b≡0⇒b≢0⇒a≡0 {a} {b} a*b≡0 b≢0 | inj₂ y = contradiction y b≢0


-- m≤n⇒m%n≡m
m<n⇒m/n≡0 : ∀ {m n} → (m<n : m < n) → ∀ {≢0} → (m / n) {≢0} ≡ 0
m<n⇒m/n≡0 {m} {n@(suc n-1)} m<n = let
                      m%n≡m = m≤n⇒m%n≡m (≤-pred m<n)
                      m≡m%n+m/n*n = (m≡m%n+[m/n]*n m n-1)
                      m≡m+m/n*n = trans m≡m%n+m/n*n (cong₂ _+_ m%n≡m refl)
                      m/n*n≡0 = sym (m≡m+x⇒0≡x m≡m+m/n*n)
                      m/n≡0 = a*b≡0⇒b≢0⇒a≡0 {a = m / n} {b = n} m/n*n≡0 (m<n⇒n≢0 m<n) 
                    in m/n≡0 

b≡0+c≡a⇒b+c≡a : ∀ {a b c} → b ≡ 0 → c ≡ a → b + c ≡ a
b≡0+c≡a⇒b+c≡a refl refl = refl

a<c⇒c|b⇒[a+b]%c≡a : ∀ {a b c} → a < c → (c ∣ b) → ∀ {≢0} → ((a + b) % c) {≢0} ≡ a
a<c⇒c|b⇒[a+b]%c≡a {a} {b} {c@(suc c-1)} a<c c|b = trans (%-remove-+ʳ a c|b) (m≤n⇒m%n≡m (≤-pred a<c))

a<c⇒c|b⇒[a+b]mod[c]≡a : ∀ {b c} → (a : Fin c) → (c ∣ b) → ∀ {≢0} → ((toℕ a + b) mod c) {≢0} ≡ a
a<c⇒c|b⇒[a+b]mod[c]≡a {b} {suc c-1} a c|b {≢0} = toℕ-injective (trans (toℕ-fromℕ< _) (a<c⇒c|b⇒[a+b]%c≡a (toℕ<n a) c|b))



ixl-cong : ∀ {s}{i : Ix 1 (s ∷ [])} → (ix-lookup i zero) ∷ [] ≡ i
ixl-cong {i = i ∷ []} = refl

--rm-thm : ∀ {a b} → (x : Fin a) → (b ≢ 0) → (y : Fin b) → ((toℕ y) + (toℕ x) * b  < (a * b))
--v-rm-thm : ∀ {a b x y b≢0} → (toℕ $ fromℕ< (rm-thm {a = a} {b = b} x b≢0 y)) ≡ (toℕ y) + (toℕ x) * b
oi-io : ∀ {n}{x : Vec _ n}{iv : Ix n x}
      → off→idx x (idx→off x iv) ≡ iv
oi-io {x = []} {[]} = refl
oi-io {x = x ∷ xs} {i ∷ iv} with prod (x ∷ xs) ≟ 0
... | yes p = ⊥-elim $ ¬Fin0 $ Πs≡0⇒Fin0 (x ∷ xs) (i ∷ iv) p
... | no ¬p = cong₂ _∷_
                   -- Πiv + i * Πxs
                   (toℕ-injective (trans (toℕ-fromℕ< _)
                                         (trans (cong (_/ prod xs) (toℕ-fromℕ< _))
                                                (hlpr {n = prod xs}
                                                      {a = toℕ (ix-lookup (idx→off xs iv) zero)}
                                                      refl (toℕ<n _)))))
                   (trans (cong (off→idx xs)
                                (trans (cong (λ x → x mod (prod xs) ∷ []) (toℕ-fromℕ< _))
                                       (trans (cong (_∷ []) (a<c⇒c|b⇒[a+b]mod[c]≡a _ (n∣m*n (toℕ i) {n = (prod xs)})))
                                              ixl-cong)))
                          oi-io)
   where
     hlpr : ∀ {m n a x}{≢0} → a + m * n ≡ x → a < n → (x / n) {≢0} ≡ m
     hlpr {m} {n} {a} {x} {≢0} refl a<n = trans (+-distrib-/-∣ʳ {m = a} (m * n) {d = n} {≢0} (n∣m*n m))
                                                (b≡0+c≡a⇒b+c≡a (m<n⇒m/n≡0 a<n) (m*n/n≡m m n))


-- rewrite (v-rm-thm {a = x} {b = prod xs} {x = i} {y = (ix-lookup (idx→off xs iv) zero)} {b≢0 = (a*b≢0⇒b≢0 {a = x} ¬p)})
