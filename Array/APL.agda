{-# OPTIONS --rewriting  #-}
module Array.APL where

open import Array.Base
open import Array.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin; zero; suc; raise; toℕ; fromℕ≤) --hiding (_+_; _<_)
open import Data.Fin.Properties using (toℕ<n) --hiding (_≟_)
open import Data.Vec
open import Data.Vec.Properties
open import Data.Product
open import Agda.Builtin.Float
open import Function
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Nullary

-- Now we start to introduce APL operators trying
-- to maintain syntactic rules and semantics.
-- We won't be able to mimic explicit concatenations
-- like 2 3 4 is a vector [2, 3, 4], as we would have
-- to overload the " " somehow.

-- This relation describes promotion of the scalar element in
-- dyadic operations.
data dy-args : ∀ n m k → (Vec ℕ n) → (Vec ℕ m) → (Vec ℕ k) → Set where
 instance
    n-n : ∀ {n}{s}    → dy-args n n n s s s
    n-0 : ∀ {n}{s}{s₁} → dy-args n 0 n s s₁ s
    0-n : ∀ {n}{s}{s₁} → dy-args 0 n n s s₁ s₁


dyadic-type : ∀ a → Set a → Set a
dyadic-type a X = ∀ {n m k}{s s₁ s₂}{{c : dy-args n m k s s₁ s₂}}
                  → Ar X n s → Ar X m s₁ → Ar X k s₂

dyadic-type-c : ∀ a → Set a → Set a
dyadic-type-c a X = ∀ {n m k}{s s₁ s₂}
                    → Ar X n s → dy-args n m k s s₁ s₂ → Ar X m s₁ → Ar X k s₂

lift-binary-op : ∀ {a}{X : Set a} → ∀ (op : X → X → X) → dyadic-type a X
lift-binary-op op ⦃ c = n-n ⦄ (imap f) (imap g) = imap λ iv → op (f iv) (g iv)
lift-binary-op op {s₁ = []} ⦃ c = n-0 ⦄ (imap f) (imap g) = imap λ iv → op (f iv) (g []) 
lift-binary-op op {s = [] } ⦃ c = 0-n ⦄ (imap f) (imap g) = imap λ iv → op (f []) (g iv) 


lift-unary-op : ∀ {a}{X : Set a} → ∀ (op : X → X)
              → ∀ {n s} → Ar X n s → Ar X n s
lift-unary-op f (imap g) = imap (λ iv → f (g iv))

-- Nat operations
infixr 20 _+ₙ_ 
infixr 20 _×ₙ_ 
_+ₙ_ = lift-binary-op _+_
_×ₙ_ = lift-binary-op _*_

_-safe-_ : (a : ℕ) → (b : ℕ) .{≥ : a ≥ b} → ℕ
a -safe- b = a ∸ b

-- FIXME As _-ₙ_ requires a proof, we won't consider yet
-- full dyadic types for _-ₙ_, as it would require us
-- to define dyadic types for ≥a.
_-ₙ_ : ∀ {n}{s}
     → (a : Ar ℕ n s) → (b : Ar ℕ n s)
     → .{≥ : a ≥a b}
     → Ar ℕ n s
(imap f -ₙ imap g) {≥} = imap λ iv → (f iv -safe- g iv) {≥ = ≥ iv}


infixr 20 _+⟨_⟩ₙ_
infixr 20 _×⟨_⟩ₙ_
_+⟨_⟩ₙ_ : dyadic-type-c _ _
a +⟨ c ⟩ₙ b = _+ₙ_ {{c = c}} a b

_×⟨_⟩ₙ_ : dyadic-type-c _ _
a ×⟨ c ⟩ₙ b = _×ₙ_ {{c = c}} a b

-- Float operations
infixr 20 _+ᵣ_
_+ᵣ_ = lift-binary-op primFloatPlus
infixr 20 _-ᵣ_
_-ᵣ_ = lift-binary-op primFloatMinus
infixr 20 _×ᵣ_
_×ᵣ_ = lift-binary-op primFloatTimes

-- XXX we can request the proof that the right argument is not zero.
-- However, the current primFloatDiv has the type Float → Float → Float, so...
infixr 20 _÷ᵣ_
_÷ᵣ_ = lift-binary-op primFloatDiv

infixr 20 _×⟨_⟩ᵣ_
_×⟨_⟩ᵣ_ : dyadic-type-c _ _
a ×⟨ c ⟩ᵣ b = _×ᵣ_ {{c = c}} a b

infixr 20 _+⟨_⟩ᵣ_
_+⟨_⟩ᵣ_ : dyadic-type-c _ _
a +⟨ c ⟩ᵣ b = _+ᵣ_ {{c = c}} a b

infixr 20 _-⟨_⟩ᵣ_
_-⟨_⟩ᵣ_ : dyadic-type-c _ _
a -⟨ c ⟩ᵣ b = _-ᵣ_ {{c = c}} a b
infixr 20 _÷⟨_⟩ᵣ_
_÷⟨_⟩ᵣ_ : dyadic-type-c _ _
a ÷⟨ c ⟩ᵣ b = _÷ᵣ_ {{c = c}} a b


infixr 20 *ᵣ_
*ᵣ_ = lift-unary-op primExp


module xx where
  a : Ar ℕ 2 (3 ∷ 3 ∷ [])
  a = cst 1

  s : Ar ℕ 0 []
  s = cst 2

  test₁ = a +ₙ a
  test₂ = a +ₙ s
  --test = (s +ₙ s) 
  test₃ = s +⟨ n-n ⟩ₙ s

  test₄ : ∀ {n s s₁} → Ar ℕ n s → Ar ℕ 0 s₁ → Ar ℕ n s
  test₄ = _+ₙ_


infixr 20 ρ_
ρ_ : ∀ {ℓ}{X : Set ℓ}{d s} → Ar X d s → Ar ℕ 1 (d ∷ [])
ρ_ {s = s} _  = s→a s


infixr 20 ,_
,_ : ∀ {a}{X : Set a}{n s} → Ar X n s → Ar X 1 (prod s ∷ [])
,_ {s = s} (imap p) = imap λ iv → p (off→idx s iv)


reduce-1d : ∀ {a}{X : Set a}{n} → Ar X 1 (n ∷ []) → (X → X → X) → X → X
reduce-1d {n = zero}  (imap p) op neut = neut
reduce-1d {n = suc n} (imap p) op neut = reduce-1d (imap λ iv → p ((raise 1 $ ix-lookup iv zero) ∷ []))
                                                   op (op neut (p $ zero ∷ []))


Scal : ∀ {a} → Set a → Set a
Scal X = Ar X 0 []

scal : ∀ {a}{X : Set a} → X → Scal X
scal = cst

unscal : ∀ {a}{X : Set a} → Scal X → X
unscal (imap f) = f []

module true-reduction where
  
  thm : ∀ {a}{X : Set a}{n m} → (s : Vec X (n + m)) → s ≡ take n s ++ drop n s
  thm {n = n} s  with splitAt n s
  thm {n = n} .(xs ++ ys) | xs , ys , refl = refl

  thm2 : ∀ {a}{X : Set a} → (v : Vec X 1) → v ≡ head v ∷ []
  thm2 (x ∷ []) = refl

  -- This is a variant with take
  _/⟨_⟩_ : ∀ {a}{X : Set a}{n}{s : Vec ℕ (n + 1)}
        → (X → X → X) → X
        → Ar X (n + 1) s
        → Ar X n (take n s) 
  _/⟨_⟩_ {n = n} {s} f neut a = let
                x = nest {s = take n s} {s₁ = drop n s} $ subst (λ x → Ar _ _ x) (thm {n = n} s) a
                in imap λ iv → reduce-1d (subst (λ x → Ar _ _ x) (thm2 (drop n s)) $ unimap x iv) f neut

  _/₁⟨_⟩_ : ∀ {a}{X : Set a}{n}{s : Vec ℕ n}{m}
        → (X → X → X) → X
        → Ar X (n + 1) (s ++ (m ∷ []))
        → Ar X n s 
  _/₁⟨_⟩_ {n = n} {s} f neut a = let
         x = nest {s = s} a
         in imap λ iv → reduce-1d (unimap x iv) f neut


  module test-reduce where
    a : Ar ℕ 2 (4 ∷ 4 ∷ [])
    a = cst 1

    b : Ar ℕ 1 (5 ∷ [])
    b = cst 2

    test₁ = _/⟨_⟩_ {n = 0} _+_ 0 (, a)
    test₂ = _/⟨_⟩_ {n = 0} _+_ 0 b


-- FIXME!  This reduction does not implement semantics of APL,
--         as it assumes that we always reduce to scalars!
--         Instead, in APL / reduce on the last axis only,
--         i.e. ⍴ +/3 4 5 ⍴ ⍳1 = 3 4

-- This is mimicing APL's f/ syntax, but with extra neutral
-- element.  We can later introduce the variant where certain
-- operations come with pre-defined neutral elements.
_/⟨_⟩_ : ∀ {a}{X : Set a}{n s}
      → (Scal X → Scal X → Scal X) → Scal X → Ar X n s → Scal X
f /⟨ neut ⟩ a = let
                    op x y = unscal $ f (scal x) (scal y)
                    a-1d = , a
                    neut = unscal neut
                in 
                    scal $ reduce-1d a-1d op neut


-- XXX I somehow don't understand how to make X to be an arbitrary Set a...
data reduce-neut : {X : Set} → (Scal X → Scal X → Scal X) → Scal X → Set where
  instance
    plus-nat : reduce-neut  _+⟨ n-n ⟩ₙ_ (cst 0)
    mult-nat : reduce-neut _×⟨ n-n ⟩ₙ_ (cst 1)
    plus-flo : reduce-neut  (_+ᵣ_ {{c = n-n}}) (cst 0.0)
    mult-flo : reduce-neut  (_×ᵣ_ {{c = n-n}}) (cst 1.0)
    
infixr 20 _/_
_/_ : ∀ {X : Set}{n s neut}
      → (op : Scal X → Scal X → Scal X) → {{c : reduce-neut op neut}}
      → Ar X n s → Scal X
_/_ {neut = neut} f a = f /⟨ neut ⟩ a 


module test-reduce where
  a = s→a $ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []

  test₁ : reduce-1d a _+_ 0 ≡ 10
  test₁ = refl

  test₂ : _+⟨ n-n ⟩ₙ_ /⟨ scal 0 ⟩ a ≡ scal 10
  test₂ = refl

  test₃ : _+ₙ_ / a ≡ scal 10
  test₃ = refl

  -- This is somewhat semi-useful dot-product expressed
  -- pretty close to what you'd write in APL.
  dotp : ∀ {n s} → Ar ℕ n s → Ar ℕ n s → Scal ℕ
  dotp a b = _+ₙ_ / a ×ₙ b

  test₄ : dotp a a ≡ scal (1 + 4 + 9 + 16)
  test₄ = refl


-- Ravel -- the size of the leading axis.
infixr 20 ≢_
≢_ : ∀ {a}{X : Set a}{n s} → Ar X n s → Scal ℕ
≢_ {n = zero}      a = scal 1
≢_ {n = suc n} {s} a = scal $ head s


data iota-type : (d : ℕ) → (n : ℕ) → (Vec ℕ d) → Set where
  instance
    iota-scal : iota-type 0 1 []
    iota-vec  : ∀ {n} → iota-type 1 n (n ∷ [])


iota-res-t : ∀ {d n s} → iota-type d n s → (sh : Ar ℕ d s) → Set

iota-res-t {n = n} iota-scal sh = Ar (Σ ℕ λ x → x < unscal sh)
                                     1 (unscal sh ∷ [])

iota-res-t {n = n} iota-vec  sh = Ar (Σ (Ar ℕ 1 (n ∷ []))
                                      λ v → v <a sh)
                                     n (a→s sh)



{-# BUILTIN REWRITE _≡_ #-}

thm : ∀ {a}{X : Set a}{s : Vec X 1} →  head s ∷ [] ≡ s
thm {s = x ∷ []} = refl

expand-s→a∘a→s : ∀ {el}{ar : Ar ℕ 1 (el ∷ [])} → ∀ (iv : Ix 1 (el ∷ []))
               → lookup (a→s ar) (ix-lookup iv zero) ≡ unimap ar iv
expand-s→a∘a→s {ar = imap f} (x ∷ []) rewrite (lookup∘tabulate (f ∘ (_∷ [])) x) = refl
--unimap (s→a (a→s ar)) iv ≡ unimap ar (subst (λ x → Ix 1 x) thm iv)
--expand-s→a∘a→s {s} {imap f} iv = {!!}


--open import Axiom.Extensionality.Propositional
--postulate
--  ext : ∀ {a b} → Extensionality a b

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


--xthm : ∀ {a}{X : Set a}{s}{sh : Ix 1 (s ∷ []) → X} → tabulate (λ i → sh (i ∷ [])) ≡ sh

--xthm : ∀ {a b c} → 

a<b⇒b≡c⇒a<c : ∀ {a b c} → a < b → b ≡ c → a < c
a<b⇒b≡c⇒a<c a<b refl = a<b

infixr 20 ι_ 
ι_ : ∀ {d n s}{{c : iota-type d n s}}
   → (sh : Ar ℕ d s)
   → iota-res-t c sh
ι_ ⦃ c = iota-scal ⦄ s = (imap λ iv → (toℕ $ ix-lookup iv zero) , toℕ<n (ix-lookup iv zero))
ι_ {n = n} {s = s ∷ []} ⦃ c = iota-vec ⦄ (imap sh) = imap cast-ix→a
  where
    cast-ix→a : _
    cast-ix→a iv = let
                     ix , pf = ix→a iv
                   in ix , λ jv → a<b⇒b≡c⇒a<c (pf jv) (s→a∘a→s (imap sh) jv)

-- Zilde and comma
⍬ : ∀ {a}{X : Set a} → Ar X 1 (0 ∷ [])
⍬ = imap λ iv → magic-fin $ ix-lookup iv zero



-- FIXME _,_ is missing


infixr 20 _¨_
_¨_ : ∀ {a}{X Y : Set a}{n s}
    → (X → Y)
    → Ar X n s
    → Ar Y n s
f ¨ imap p = imap λ iv → f $ p iv



-- Take and Drop

ax+sh<s : ∀ {n}
        → (ax sh s : Ar ℕ 1 (n ∷ []))
        → (s≥sh : s ≥a sh)
        → (ax <a (s -ₙ sh) {≥ = s≥sh})
        → (ax +ₙ sh) <a s
ax+sh<s (imap ax) (imap sh) (imap s) s≥sh ax<s-sh iv =
    let
      ax+sh<s-sh+sh = +-monoˡ-< (sh iv) (ax<s-sh iv)
      s-sh+sh≡s     = m∸n+n≡m (s≥sh iv)
    in a<b⇒b≡c⇒a<c ax+sh<s-sh+sh s-sh+sh≡s


_↑_ : ∀ {a}{X : Set a}{n s}
    → (sh : Ar ℕ 1 (n ∷ []))
    → (a : Ar X n s)
    → {pf : s→a s ≥a sh}
    → Ar X n $ a→s sh
_↑_ {s = s} sh       (imap f) {pf}   with (prod $ a→s sh) ≟ 0
_↑_ {s = s} sh       (imap f) {pf} | yes Πsh≡0 = mkempty _ Πsh≡0
_↑_ {s = s} (imap q) (imap f) {pf} | no  Πsh≢0 = imap mtake
  where
    mtake : _
    mtake iv = let
                  ai , ai< = ix→a iv
                  ix<q jv = a<b⇒b≡c⇒a<c (ai< jv) (s→a∘a→s (imap q) jv)
                  ix = a→ix ai (s→a s) λ jv → ≤-trans (ix<q jv) (pf jv)
               in f (subst-ix (a→s∘s→a s) ix)


_↓_ : ∀ {a}{X : Set a}{n s}
    → (sh : Ar ℕ 1 (n ∷ []))
    → (a : Ar X n s)
    → {pf : (s→a s) ≥a sh}
    → Ar X n $ a→s $ (s→a s -ₙ sh) {≥ = pf}
_↓_ {s = s} sh (imap x) {pf} with
                             let p = prod $ a→s $ (s→a s -ₙ sh) {≥ = pf}
                             in  p ≟ 0
_↓_ {s = s} sh       (imap f) {pf} | yes Π≡0 = mkempty _ Π≡0
_↓_ {s = s} (imap q) (imap f) {pf} | no  Π≢0 = imap mkdrop
  where
    mkdrop : _ 
    mkdrop iv = let 
                  ai , ai< = ix→a iv
                  ax = ai +ₙ (imap q)
                  thmx = ax+sh<s
                           ai (imap q) (s→a s) pf
                           λ jv → a<b⇒b≡c⇒a<c (ai< jv)
                                  (s→a∘a→s ((s→a s -ₙ (imap q)) {≥ = pf}) jv)
                  ix = a→ix ax (s→a s) thmx
                in f (subst-ix (a→s∘s→a s) ix) 


mapₐ₂ : ∀ {a}{X Y Z : Set a}{n s} → (X → Y → Z)
       → Ar X n s → Ar Y n s → Ar Z n s
mapₐ₂ f (imap p) (imap p₁) = imap λ iv → f (p iv) (p₁ iv)


a≤b⇒b≡c⇒a≤c : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
a≤b⇒b≡c⇒a≤c a≤b refl = a≤b

a≤b⇒a≡c⇒b≡d⇒c≤d : ∀ {a b c d} → a ≤ b → a ≡ c → b ≡ d → c ≤ d
a≤b⇒a≡c⇒b≡d⇒c≤d a≤b refl refl = a≤b


thm1 : ∀ {n}{ix s s₁ : Ar ℕ 1 (n ∷ [])}
      → ix <a s → s₁ ≥a s → s₁ ≥a ix
thm1 {ix = imap x} {imap x₁} {imap x₂} ix<s ix≤s₁ iv = ≤-trans (<⇒≤ $ ix<s iv) (ix≤s₁ iv)

moo : ∀ {a b} → b < a →  a ∸ suc b + 1 ≡ a ∸ b
moo {a} {b} pf = begin
                     a ∸ suc (b) + 1  ≡⟨ sym $ +-∸-comm 1 pf ⟩
                     a + 1 ∸ suc b    ≡⟨ cong₂ _∸_ (+-comm a 1) (refl {x = suc b}) ⟩
                     a ∸ b
                   ∎
                   where open ≡-Reasoning


thm2 : ∀ {n}{ix s s₁ : Ar ℕ 1 (n ∷ [])}
       → (ix<s : ix <a s)
       → (s₁≥s : s₁ ≥a s)
       → (s₁ -ₙ ix) {≥ = thm1 {s₁ = s₁} ix<s s₁≥s {-thm1 ix<s s₁≥s-}} ≥a ((s₁ -ₙ s) {≥ = s₁≥s} +ₙ (scal 1))
thm2 {ix = imap ix} {imap s} {imap s₁} ix<s s₁≥s iv =
       let
         s₁-[1+ix]≥s₁-s = ∸-monoʳ-≤ (s₁ iv) (ix<s iv)
         xxx = +-monoˡ-≤ 1 s₁-[1+ix]≥s₁-s
       in a≤b⇒b≡c⇒a≤c xxx (moo {a = s₁ iv} {b = ix iv} (≤-trans (ix<s iv) (s₁≥s iv))) 

{-dugh : ∀ {n}{iv : Ix 1 (n ∷ [])}{s₁ : Vec ℕ n}{ix : Ar ℕ 1 (n ∷ [])}{≥1 ≥2}
     → unimap ((imap (λ iv₁ → lookup s₁ (iiv₁ zero)) -ₙ ix) {≥ = ≥1}) iv ≡
       (a→s $ (s→a s₁ -ₙ ix) {≥ = ≥2}) (iv zero)
dugh {iv = iv} {s₁ = s₁} {ix = imap x} = cong (s₁ (iv zero) ∸_) ? --(cong x (ext λ i → cong iv (Fin1≡0 i)))
-}


A≥B⇒A≡C⇒C≥B : ∀ {d s}{A B C : Ar ℕ d s}
             → A ≥a B → A =a C → C ≥a B
A≥B⇒A≡C⇒C≥B {A = imap x} {imap x₁} {imap x₂} A≥B A≡C iv rewrite (sym $ A≡C iv) = A≥B iv




toto : ∀ {n} {s s₁ : Vec ℕ n}
         {ix : Ar ℕ 1 (n ∷ [])}
         {≥1} →
       ((imap (λ iv → lookup s₁ (ix-lookup iv zero)) -ₙ ix) {≥ = ≥1}) =a
       imap
       (λ z →
          lookup (a→s ((imap (λ iv → lookup s₁ (ix-lookup iv zero)) -ₙ ix) {≥ = ≥1}))
          (ix-lookup z zero))
toto {s = s} {s₁ = s₁} {ix = (imap ix)} {≥1} iv = sym $ s→a∘a→s ((s→a s₁ -ₙ imap ix) {≥ = ≥1}) iv


boo : ∀ {n} s → Vec ℕ n -- Ar ℕ 1 (n ∷ [])
boo s = a→s (s→a s)

goo : ∀ {n} → Ar ℕ 1 (n ∷ []) → Ar ℕ 1 (n ∷ [])
goo a = s→a (a→s a) -- (imap a) = s→a (a→s (imap a))

testxx = goo {n = 5} (cst 3)


conv : ∀ {n s s₁}
       → Ar ℕ n s
       → Ar ℕ n s₁
       → {s₁≥s : s→a s₁ ≥a s→a s}
       → let sr = a→s $ (s→a s₁ -ₙ s→a s) {≥ = s₁≥s} +ₙ scal 1
         in Ar ℕ n sr
conv {n = n} {s = s} {s₁ = s₁} w a {s₁≥s} = let
               sr = (s→a s₁ -ₙ s→a s) {≥ = s₁≥s} +ₙ scal 1
               idxs = ι ρ w
               --rots : _ -- (v : Ar ℕ 1 (λ _ → n)) → v <a imap (λ iv → s (iv zero)) → _
               rots ix ix<s =
                         let
                           --ix , ix<s = ix,ix<s
                           ix↓a = (ix ↓ a) {pf = thm1 ix<s s₁≥s} --thm1 {s₁ = s→a s₁} ix<s s₁≥s} -- thm1 {s₁ = s→a s₁} ix<s s₁≥s }
                           ttt = thm2 {s₁ = s→a s₁} ix<s s₁≥s
                         in
                           (sr ↑ ix↓a) {pf = A≥B⇒A≡C⇒C≥B
                                                 ttt
                                                 (toto {s = s} {s₁ = s₁} {≥1 = thm1 {s₁ = s→a s₁} ix<s s₁≥s}) } 
               --rots-unw : _ --Σ (Ar ℕ 1 (λ _ → n)) (λ v → v <a imap (λ iv → s (iv zero))) → _
               rots-unw ix,ix<s = (let
                                     ix , ix<s = ix,ix<s
                                    in rots ix ix<s)
               r = rots-unw ¨ idxs
               mul = mapₐ₂ (λ weight arr → arr ×⟨ n-n ⟩ₙ (cst weight)) w (subst-ar (a→s∘s→a s) r)
               res = reduce-1d (, mul) _+ₙ_ (cst 0)
              in res 

cex₁ = conv (s→a $ 1 ∷ []) (s→a $ 2 ∷ 3 ∷ []) {s₁≥s = λ { (zero ∷ []) → s≤s z≤n} }
