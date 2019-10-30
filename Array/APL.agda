module Array.APL where

open import Array.Base
open import Array.Properties
open import Data.Nat
open import Data.Nat.DivMod hiding (_/_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; zero; suc; raise; toℕ; fromℕ≤)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Vec
open import Data.Vec.Properties
open import Data.Product
open import Agda.Builtin.Float
open import Function
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
--open import Relation.Binary

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
infixr 20 _-ₙ_
_-ₙ_ : ∀ {n}{s}
     → (a : Ar ℕ n s) → (b : Ar ℕ n s)
     → .{≥ : a ≥a b}
     → Ar ℕ n s
(imap f -ₙ imap g) {≥} = imap λ iv → (f iv -safe- g iv) {≥ = ≥ iv}


--≢-sym : ∀ {X : Set}{a b : X} → a ≢ b → b ≢ a
--≢-sym pf = pf ∘ sym


infixr 20 _÷ₙ_
_÷ₙ_ : ∀ {n}{s}
     → (a : Ar ℕ n s) → (b : Ar ℕ n s)
     → {≥0 : cst 0 <a b}
     → Ar ℕ n s
_÷ₙ_ (imap f) (imap g) {≥0} = imap λ iv → (f iv div g iv) {≢0 = fromWitnessFalse (≢-sym $ <⇒≢ $ ≥0 iv) }

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
  test₃ = s +ₙ a 
  --test = (s +ₙ s) 
  test₄ = s +⟨ n-n ⟩ₙ s

  test₅ : ∀ {n s s₁} → Ar ℕ n s → Ar ℕ 0 s₁ → Ar ℕ n s
  test₅ = _+ₙ_


infixr 20 ρ_
ρ_ : ∀ {ℓ}{X : Set ℓ}{d s} → Ar X d s → Ar ℕ 1 (d ∷ [])
ρ_ {s = s} _  = s→a s

infixr 20 ,_
,_ : ∀ {a}{X : Set a}{n s} → Ar X n s → Ar X 1 (prod s ∷ [])
,_ {s = s} (imap p) = imap λ iv → p (off→idx s iv)


-- Reshape
infixr 20 _ρ_
_ρ_ : ∀ {a}{X : Set a}{n}{sa}
    → (s : Ar ℕ 1 (n ∷ []))
    → (a  : Ar X n sa)
    -- if the `sh` is non-empty, `s` must be non-empty as well.
    → {s≢0⇒ρa≢0 : prod (a→s s) ≢ 0 → prod sa ≢ 0}
    → Ar X n (a→s s)
_ρ_ {sa = sa} s a {s≢0⇒ρa≢0} with  prod sa ≟ 0 | prod (a→s s) ≟ 0 
_ρ_ {sa = sa} s a {s≢0⇒ρa≢0}     | _           | yes s≡0  = mkempty (a→s s) s≡0
_ρ_ {sa = sa} s a {s≢0⇒ρa≢0}     | yes ρa≡0    | no  s≢0  = contradiction ρa≡0 (s≢0⇒ρa≢0 s≢0)
_ρ_ {sa = sa} s a {s≢0⇒ρa≢0}     | no  ρa≢0    | _        = imap from-flat
  where    
    from-flat : _
    from-flat iv = let
                     off  = idx→off (a→s s) iv --{!!} -- (ix-lookup iv zero)
                     flat = unimap $ , a
                     ix   = (toℕ (ix-lookup off zero) mod prod sa)
                            {≢0 = fromWitnessFalse ρa≢0}
                   in 
                     flat (ix ∷ [])



reduce-1d : ∀ {a}{X : Set a}{n} → Ar X 1 (n ∷ []) → (X → X → X) → X → X
reduce-1d {n = zero}  (imap p) op neut = neut
reduce-1d {n = suc n} (imap p) op neut = op (p $ zero ∷ [])
                                            (reduce-1d (imap (λ iv → p (suc (ix-lookup iv zero) ∷ []))) op neut)

{-
  This goes right to left if we want to
  reduce-1d (imap λ iv → p ((raise 1 $ ix-lookup iv zero) ∷ []))
            op (op neut (p $ zero ∷ []))
-}


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


-- The size of the leading axis.
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



-- XXX We are going to use _·_ instead of _,_ as the
-- latter is a constructor of dependent sum.  Renaming
-- all the occurrences to something else would take
-- a bit of work which we should do later.
infixr 30 _·_
_·_ : ∀ {a}{X : Set a}{n} → X → Ar X 1 (n ∷ []) → Ar X 1 (suc n ∷ [])
x · (imap p) = imap λ iv → case ix-lookup iv zero of λ where
                             zero     → x
                             (suc j) → p (j ∷ [])

-- Note that two dots in an upper register combined with
-- the underscore form the _̈  symbol.  When the symbol is
-- used on its own, it looks like ̈ which is the correct
-- "spelling".
infixr 20 _̈_
_̈_ : ∀ {a}{X Y : Set a}{n s}
    → (X → Y)
    → Ar X n s
    → Ar Y n s
f ̈ imap p = imap λ iv → f $ p iv



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


_̈⟨_⟩_ : ∀ {a}{X Y Z : Set a}{n s} 
     → Ar X n s
     → (X → Y → Z)
     → Ar Y n s → Ar Z n s
(imap p) ̈⟨ f ⟩ (imap p₁) = imap λ iv → f (p iv) (p₁ iv)


