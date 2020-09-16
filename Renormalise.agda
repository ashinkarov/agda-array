{-# OPTIONS --rewriting  #-}
open import Reflection hiding (return; _>>=_) renaming (_≟_ to _≟r_)

open import Data.List hiding (_++_)
open import Data.Vec as V using (Vec; updateAt)
open import Data.Unit
open import Data.Nat as N
open import Data.Nat.Properties
open import Data.Fin using (Fin; #_; suc; zero)
open import Data.Maybe hiding (_>>=_; map)
open import Function
open import Data.Bool
open import Data.Product hiding (map)
open import Data.String renaming (_++_ to _++s_; concat to sconc; length to slen)
open import Data.Char renaming (_≈?_ to _c≈?_; show to showChar)

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Data.Nat.Show renaming (show to showNat)

open import Level renaming (zero to lzero; suc to lsuc)

open import Category.Monad using (RawMonad)

open RawMonad {{...}} public

instance
  monadMB : ∀ {f} → RawMonad {f} Maybe
  monadMB = record { return = just ; _>>=_ = Data.Maybe._>>=_ }

  monadTC : ∀ {f} → RawMonad {f} TC
  monadTC = record { return = Reflection.return ; _>>=_ = Reflection._>>=_ }

data Err {a} (A : Set a) : Set a where
  error : String → Err A
  ok : A → Err A

instance
  monadErr : ∀ {f} → RawMonad {f} Err
  monadErr = record {
    return = ok ;
    _>>=_ = λ { (error s) f → error s ; (ok a) f → f a }
    }

record RawMonoid {a}(A : Set a) : Set a where
  field
    _++_ : A → A → A
    ε : A
  ++/_ : List A → A
  ++/ [] = ε
  ++/ (x ∷ a) = x ++ ++/ a

  infixr 5 _++_

open RawMonoid {{...}} public

instance
  monoidLst : ∀ {a}{A : Set a} → RawMonoid (List A)
  monoidLst {A = A} = record {
    _++_ = Data.List._++_;
    ε = []
    }

  monoidErrLst : ∀{a}{A : Set a} → RawMonoid (Err $ List A)
  monoidErrLst = record {
    _++_ =  λ where
      (error s) _ → error s
      _ (error s) → error s
      (ok s₁) (ok s₂) → ok (s₁ ++ s₂)
    ;
    ε = ok []
    }


defToTerm : Name → Definition → List (Arg Term) → Term
defToTerm _ (function cs) as = pat-lam cs as
defToTerm _ (constructor′ d) as = con d as
defToTerm _ _ _ = unknown

derefImmediate : Term → TC Term
derefImmediate (def f args) = getDefinition f >>= λ f' → return (defToTerm f f' args)
derefImmediate x = return x

derefT : Term → TC Term
derefT (def f args) = getType f
derefT (con f args) = getType f
derefT x = return x


Ctx = List $ Arg Type

drop-ctx' : Ctx → ℕ → Ctx
drop-ctx' l zero = l
drop-ctx' [] (suc n) = []
drop-ctx' (x ∷ l) (suc n) = drop-ctx' l n

take-ctx' : Ctx → ℕ → Ctx
take-ctx' [] zero = []
take-ctx' [] (suc p) = [] --error "take-ctx: ctx too short for the prefix"
take-ctx' (x ∷ l) zero = []
take-ctx' (x ∷ l) (suc p) = x ∷ take-ctx' l p

-- FIXME we probably want to error out on these two functions.
pi-to-ctx : Term → Ctx
pi-to-ctx (Π[ s ∶ a ] x) = (a ∷ pi-to-ctx x)
pi-to-ctx _ = []

ctx-to-pi : List (Arg Type) → Type
ctx-to-pi [] = def (quote ⊤) []
ctx-to-pi (a ∷ t) = Π[ "_" ∶  a ] ctx-to-pi t

ty-con-args : Arg Type → List $ Arg Type
ty-con-args (arg _ (con c args)) = args
ty-con-args (arg _ (def c args)) = args
ty-con-args _ = []


con-to-ctx : Term → Term × Ctx
con-to-ctx (Π[ s ∶ a ] x) = let t , args = con-to-ctx x in t , a ∷ args
con-to-ctx x = x , []


record Eq : Set where
  constructor _↦_
  field
    left  : Term
    right : Term

Eqs = List Eq

eqs-shift-vars : Eqs → ℕ → Eqs

mbeqs-eqs : Maybe Eqs → Eqs
mbeqs-eqs (just x) = x
mbeqs-eqs nothing = []

-- stupid name, this generates equalities for two terms being somewhat similar.
unify-eq : Term → Term → Eqs
unify-eq-map : List $ Arg Term → List $ Arg Term → Maybe Eqs

unify-eq (var x [])             y = [ var x [] ↦ y ]
unify-eq (var x args@(_ ∷ _))   t₂ = {!!}

unify-eq (con c args) (con c′ args′) with c ≟-Name c′
... | yes p = mbeqs-eqs $ unify-eq-map args args′
... | no ¬p = []
unify-eq (def f args) (def f′ args′) with f ≟-Name f′
              -- Generally speaking this is a lie of course, as
              -- not all the definitons are injective.  However,
              -- we mainly use these for types such as Vec, Nat, etc
              -- and for these cases it is fine.  How do I check whether
              -- the definition is a data type or not?
... | yes p = mbeqs-eqs $ unify-eq-map args args′
... | no ¬p = []
unify-eq (lam v t) t₂ = {!!}
unify-eq (pat-lam cs args) t₂ = {!!}
unify-eq (pi a b) t₂ = {!!}
unify-eq (sort s) t₂ = {!!}
unify-eq (lit l) y = [ lit l ↦ y ]
unify-eq (meta x x₁) t₂ = {!!}
unify-eq unknown t₂ = {!!}
unify-eq x              (var y []) = [ x ↦ var y [] ]
unify-eq x              (var y args@(_ ∷ _)) =  {!!} --[ x ↦ var y [] ]
unify-eq a b = []

test-unify₁ = unify-eq (var 0 []) (con (quote ℕ.suc) [ vArg $ con (quote ℕ.zero) [] ] )
test-unify₂ = unify-eq (con (quote ℕ.suc) [ vArg $ con (quote ℕ.zero) [] ] )   (var 0 [])

unify-eq-map [] [] = just []
unify-eq-map [] (y ∷ _) = nothing
unify-eq-map (x ∷ _) [] = nothing
unify-eq-map (arg _ x ∷ xs) (arg _ y ∷ ys) = do
  eqs ← unify-eq-map xs ys
  return $ unify-eq x y ++ eqs


eq-find-l : Eqs → Term → Term
eq-find-l [] t = t
eq-find-l (l ↦ r ∷ eqs) t with l ≟r t
... | yes l≡t = r
... | no  l≢t = eq-find-l eqs t


decvar : Term → (min off : ℕ) → Err Term
decvar-map : List $ Arg Term → (min off : ℕ) → Err $ List $ Arg Term

decvar (var x args) m o with x ≥? m
decvar (var x args) m o | yes x≥m with x ≥? o
decvar (var x args) m o | yes x≥m | yes x≥o = do
  args ← decvar-map args m o
  return $ var (x ∸ o) args
decvar (var x args) m o | yes x≥m | no x≱o = error "decvar: variable index is less than decrement"
decvar (var x args) m o | no x≱m = do
  args ← decvar-map args m o
  return $ var x args
decvar (con c args) m o = do
  args ← decvar-map args m o
  return $ con c args
decvar (def f args) m o = do
  args ← decvar-map args m o
  return $ def f args
decvar (lam v t) m o = {!!}
decvar (pat-lam cs args) m o = {!!}
decvar (Π[ s ∶ arg i a ] x) m o = do
  a ← decvar a m o
  x ← decvar x (1 + m) o
  return $ Π[ s ∶ arg i a ] x
decvar (sort (set t)) m o = do
  t ← decvar t m o
  return $ sort $ set t
decvar (sort (lit n)) m o =
  return $ sort $ lit n
decvar (sort unknown) m o =
  return $ sort $ unknown
decvar (lit l) m o = return $ lit l
decvar (meta x args) m o = do
  args ← decvar-map args m o
  return $ meta x args
decvar unknown m o = return unknown

decvar-map [] m o = ok []
decvar-map (arg i x ∷ l) m o = do
   x ← decvar x m o
   l ← decvar-map l m o
   return $ (arg i x) ∷ l

-- Note that we throw away the equality in case it didn't decvar'd correctly.
decvar-eqs : Eqs → (min off : ℕ) → Eqs
decvar-eqs [] m o = []
decvar-eqs (x ↦ y ∷ eqs) m o with (decvar x m o) | (decvar y m o)
decvar-eqs (x ↦ y ∷ eqs) m o | ok x′ | ok y′ = x′ ↦ y′ ∷ decvar-eqs eqs m o
decvar-eqs (x ↦ y ∷ eqs) m o | _     | _       = decvar-eqs eqs m o


check-var-pred : Term → (p : ℕ → Bool) → (min : ℕ) → Bool
check-var-pred-map : List $ Arg Term → (p : ℕ → Bool) (min : ℕ) → Bool
check-var-pred (var x args) p m with x ≥? m
check-var-pred (var x args) p m | yes x≥m with p x
check-var-pred (var x args) p m | yes x≥m | true = true
check-var-pred (var x args) p m | yes x≥m | false = check-var-pred-map args p m
check-var-pred (var x args) p m | no  x≱m = check-var-pred-map args p m
check-var-pred (con c args) p m = check-var-pred-map args p m
check-var-pred (def f args) p m = check-var-pred-map args p m
check-var-pred (lam v t) p m = {!!}
check-var-pred (pat-lam cs args) p m = {!!}
check-var-pred (Π[ s ∶ (arg i a) ] x) p m with check-var-pred a p m
... | true  = true
... | false = check-var-pred x p (1 + m)
check-var-pred (sort (set t)) p m = check-var-pred t p m
check-var-pred (sort (lit n)) p m = false
check-var-pred (sort unknown) p m = false
check-var-pred (lit l) p m = false
check-var-pred (meta x args) p m = check-var-pred-map args p m
check-var-pred unknown p m = false

check-var-pred-map [] p m = false
check-var-pred-map (arg _ x ∷ l) p m with check-var-pred x p m
... | true = true
... | false = check-var-pred-map l p m

-- eliminate equalities where we reverence variables that are greaterh than n
eqs-elim-vars-ge-l : Eqs → (n : ℕ) → Eqs
eqs-elim-vars-ge-l [] n = []
eqs-elim-vars-ge-l (l ↦ r ∷ eqs) n with check-var-pred l (isYes ∘ (_≥? n)) 0
... | true = eqs-elim-vars-ge-l eqs n
... | false = (l ↦ r) ∷ eqs-elim-vars-ge-l eqs n



subst-eq-var : Eqs → Type → (min : ℕ) → Type
subst-eq-var-map : Eqs → List $ Arg Type → (min : ℕ) → List $ Arg Type


-- Iterate over a reversed telescopic context and try to subsitute variables
-- from eqs, if we have some.
subst-eq-vars : Eqs → List $ Arg Type → List $ Arg Type

subst-eq-vars eqs [] = []
subst-eq-vars eqs ((arg i ty) ∷ tys) = let
  eqs = decvar-eqs eqs 0 1
  in (arg i $ subst-eq-var eqs ty 0) ∷ subst-eq-vars eqs tys


subst-eq-var eqs t@(var x []) m with x ≥? m
... | yes p = eq-find-l eqs t
... | no ¬p = t
subst-eq-var eqs (var x (x₁ ∷ args)) m = {!!}
subst-eq-var eqs (con c args) m =
      con c $ subst-eq-var-map eqs args m
subst-eq-var eqs (def f args) m =
      def f $ subst-eq-var-map eqs args m
subst-eq-var eqs (lam v t) m = {!!}
subst-eq-var eqs (pat-lam cs args) m = {!!}
subst-eq-var eqs (Π[ s ∶ (arg i a) ] x) m =
  Π[ s ∶ (arg i $ subst-eq-var eqs a m) ]
   -- We need to increase all the variables in
   -- eqs berfore entering x.
   subst-eq-var (eqs-shift-vars eqs 1) x (1 + m)
subst-eq-var eqs (sort s) m = {!!}
subst-eq-var eqs (lit l) m = lit l
subst-eq-var eqs (meta x x₁) m = {!!}
subst-eq-var eqs unknown m = unknown

subst-eq-var-map eqs [] m = []
subst-eq-var-map eqs (arg i x ∷ l) m =
  arg i (subst-eq-var eqs x m) ∷ subst-eq-var-map eqs l m

-- shift all the variables by n
shift-vars : Type → (min off : ℕ) → Type
shift-vars-map : List $ Arg Type → ℕ → ℕ → List $ Arg Type

shift-vars (var x args) m o with x ≥? m
... | yes p = var (o + x) (shift-vars-map args m o)
... | no ¬p = var x (shift-vars-map args m o)
shift-vars (con c args) m o = con c $ shift-vars-map args m o
shift-vars (def f args) m o = def f $ shift-vars-map args m o
shift-vars (lam v (abs s x)) m o = lam v $ abs s $ shift-vars x (1 + m) o

shift-vars (pat-lam cs args) m o = {!!}
shift-vars (Π[ s ∶ arg i a ] x) m o = Π[ s ∶ arg i (shift-vars a m o) ] shift-vars x (1 + m) o
shift-vars (sort (set t)) m o = sort $ set $ shift-vars t m o
shift-vars (sort (lit n)) m o = sort $ lit n
shift-vars (sort unknown) m o = sort unknown
shift-vars (lit l) m o = lit l
shift-vars (meta x args) m o = meta x $ shift-vars-map args m o
shift-vars unknown m o = unknown

shift-vars-map [] m o = []
shift-vars-map (arg i x ∷ l) m o = arg i (shift-vars x m o) ∷ shift-vars-map l m o


eqs-shift-vars [] n = []
eqs-shift-vars (l ↦ r ∷ eqs) n = let
  l′ = shift-vars l 0 n
  r′ = shift-vars r 0 n
  in l′ ↦ r′ ∷ eqs-shift-vars eqs n


trans-eqs : Eqs → Eq → Eqs
trans-eqs [] (l ↦ r) = []
trans-eqs ((l′ ↦ r′) ∷ eqs) eq@(l ↦ r) with l′ ≟r l
... | yes l′≡l = unify-eq r′ r ++ trans-eqs eqs eq
... | no _ with  l′ ≟r r
... | yes l′≡r = unify-eq r′ l ++ trans-eqs eqs eq
... | no _ with  r′ ≟r l
... | yes r′≡l = unify-eq l′ r ++ trans-eqs eqs eq
... | no _ with  r′ ≟r r
... | yes r′≡r = unify-eq l′ l ++ trans-eqs eqs eq
... | no _ = trans-eqs eqs eq

merge-eqs : (l r : Eqs) → (acc : Eqs) → Eqs
merge-eqs l [] acc = l ++ acc
merge-eqs l (x ∷ r) acc = merge-eqs l r (x ∷ acc ++ trans-eqs l x)


TyPat = Arg Type × Arg Pattern

merge-tys-pats : List $ Arg Type → List $ Arg Pattern → Err $ List TyPat
merge-tys-pats [] [] = ok []
merge-tys-pats [] (x ∷ ps) = error "merge-tys-pats: more patterns than types"
merge-tys-pats (x ∷ tys) [] = error "merge-tys-pats: more types than patterns"
merge-tys-pats (ty ∷ tys) (p ∷ ps) = ok [ ty , p ] ++ merge-tys-pats tys ps

shift-ty-vars-map : List TyPat → (min off : ℕ) → List TyPat
shift-ty-vars-map [] m o = []
shift-ty-vars-map ((arg i ty , p) ∷ l) m o = (arg i (shift-vars ty m o) , p) ∷ shift-ty-vars-map l m o

subst-typats : List TyPat → (min var : ℕ) → Type → List TyPat
subst-typats [] m v x = []
subst-typats ((arg tv ty , p) ∷ l) m v x = let
  ty′ = subst-eq-var [ (var v []) ↦ x ] ty m
  in (arg tv ty′ , p) ∷ subst-typats l (1 + m) (1 + v) (shift-vars x 0 1)

gen-n-vars : (count v : ℕ) → List $ Arg Term
gen-n-vars 0 _ = []
gen-n-vars (suc n) v = vArg (var v []) ∷ gen-n-vars n (1 + v)


{-# TERMINATING #-}
pats-ctx-open-cons : List TyPat → Eqs →  TC $ Eqs × (Err $ List TyPat)
pats-ctx-open-cons [] eqs = return $ eqs , ok []
pats-ctx-open-cons ((arg tv ty , arg pv (con c ps)) ∷ l) eqs = do
   con-type ← getType c
   let con-ret , con-ctx = con-to-ctx con-type
   -- bump indices in x by the length of ps
   let #ps = length ps
   let ty = shift-vars ty 0 #ps
   let con-eqs = unify-eq con-ret ty
   --let con-eqs = mbeqs-eqs $ unify-eq-map con-type-args ty-args
   let ctx = subst-eq-vars con-eqs (take-ctx' (reverse con-ctx) #ps)
   case #ps N.≟ 0 of λ where
     (no #ps≢0) → do
        -- Throw away substitutions that point further than the number
        -- of arguments to the constructor
        let con-eqs′ = eqs-elim-vars-ge-l con-eqs #ps
        let eqs′ = eqs-shift-vars eqs #ps
        let ctxl = merge-tys-pats (reverse ctx) ps
        -- substitute constructor into the rest of the context
        let l′ = subst-typats l 0 0 (con c $ gen-n-vars #ps 0)
        -- We eliminated 0 variable, so bump all the variables greater than 0
        let l′ = shift-ty-vars-map l′ 1 (#ps ∸ 1)
        eqs″ , ctxr ← pats-ctx-open-cons l′ (merge-eqs eqs′ con-eqs′ [])
        return $ eqs″ , ctxl ++ ctxr
     (yes  ps≡0) → do
        let con-eqs′ = eqs-elim-vars-ge-l con-eqs 0
        -- shift con-eqs′ by 1 to account for the newly inserted Dot.
        let con-eqs′ = eqs-shift-vars con-eqs′ 1
        -- Add equality of the newly inserted Dot and shift eqs by 1
        --let eqs′ = (var 0 [] ≜ con c []) ∷ eqs-shift-vars eqs 1
        let eqs′ = eqs-shift-vars eqs 1
        -- substitute constructor into the rest of the context
        let l′ = subst-typats l 0 0 (con c [])
        eqs″ , ctxr ← pats-ctx-open-cons l′ (merge-eqs eqs′ con-eqs′ [])
        return $ eqs″ , ok [ arg tv ty , arg pv dot ] ++ ctxr
pats-ctx-open-cons ((ty , arg i dot) ∷ l) eqs = do
  -- leave the dot and psas the equations further
  let eqs′ = eqs-shift-vars eqs 1
  eqs″ , ctx ← pats-ctx-open-cons l eqs′
  return $ eqs″ , ok [ ty , arg i dot ] ++ ctx
pats-ctx-open-cons ((ty , arg i (var s)) ∷ l) eqs = do
  -- pass the equations further and leave the variable as is
  let eqs′ = eqs-shift-vars eqs 1
  eqs″ , ctx ← pats-ctx-open-cons l eqs′
  return $ eqs″ , ok [ ty , arg i (var s) ] ++ ctx
pats-ctx-open-cons ((ty , arg i (lit x)) ∷ l) eqs = do
  -- we don't get any new equations from the literal so
  -- pass the equations further and insert the dot
  let eqs′ = eqs-shift-vars eqs 1
  let l′ = subst-typats l 0 0 (lit x)
  eqs″ , ctx ← pats-ctx-open-cons l′ eqs′
  return $ eqs″ , ok [ ty , arg i dot ] ++ ctx
pats-ctx-open-cons ((ty , arg i (proj f)) ∷ l) eqs =
  return $ eqs , error "pats-ctx-open-cons: projection found, fixme"
pats-ctx-open-cons ((ty , arg i absurd) ∷ l) eqs =
  return $ eqs , error "pats-ctx-open-cons: absurd pattern found, fixme"


-- Check whether the varibale (var 0) can be found in the tyspats
-- telescopic context.
check-ref : List TyPat → (v : ℕ) → Bool
check-ref [] v = false
check-ref ((arg _ ty , _) ∷ l) v with check-var-pred ty (isYes ∘ (N._≟ v)) 0
... | true  = true
... | false = check-ref l (1 + v)

-- XXX we are going to ignore the errors from the decvar, as we assume that
-- (var 0) is not referenced in the telescopic pattern.
dec-typats : List TyPat → (min : ℕ) → List TyPat
dec-typats [] m = []
dec-typats ((arg ti ty , p) ∷ l) m with decvar ty m 1
... | ok ty′  = (arg ti ty′ , p) ∷ dec-typats l (1 + m)
... | error _ = (arg ti ty , p) ∷ dec-typats l (1 + m)

-- Try to eliminate dots if there is no references in the rhs to this variable
{-# TERMINATING #-}  -- XXX this can be resolved, this function IS terminating
try-elim-dots : List TyPat → List TyPat
try-elim-dots [] = []
try-elim-dots ((ty , arg i dot) ∷ tyspats) with check-ref tyspats 0
... | true = (ty , arg i dot) ∷ try-elim-dots tyspats
... | false = try-elim-dots (dec-typats tyspats 1)
try-elim-dots ((ty , p) ∷ tyspats) = (ty , p) ∷ try-elim-dots tyspats


-- Look at the ctx list in *reverse* and get the list of variables that
-- correspond to dot patterns
get-dots : List TyPat → ℕ → List ℕ
get-dots [] o = []
get-dots ((_ , arg _ dot) ∷ l) o = o ∷ get-dots l (1 + o)
get-dots (_ ∷ l) o = get-dots l (1 + o)

-- Check if a given term contains any variable from the list
check-refs : Term → List ℕ → Bool
check-refs t [] = false
check-refs t (v ∷ vs) with check-var-pred t (isYes ∘ (N._≟ v)) 0
... | true = true
... | false = check-refs t vs


-- Eliminate the rhs of each eq in case it references dot patterns.
eqs-elim-nondots : Eqs → List ℕ → Eqs
eqs-elim-nondots [] _ = []
eqs-elim-nondots (eq@(_ ↦ r) ∷ eqs) vs with check-refs r vs
... | true = eqs-elim-nondots eqs vs
... | false = eq ∷ eqs-elim-nondots eqs vs


-- Substitute the variables from eqs into the *reversed* telescopic
-- context.
subst-eq-typats : Eqs → List TyPat → List TyPat
subst-eq-typats eqs [] = []
subst-eq-typats []  l  = l
subst-eq-typats eqs ((arg ti ty , p) ∷ typats) = let
  eqs = decvar-eqs eqs 0 1
  in (arg ti (subst-eq-var eqs ty 0) , p) ∷ subst-eq-typats eqs typats



check-no-dots : List TyPat → Bool
check-no-dots [] = true
check-no-dots ((_ , arg _ dot) ∷ l) = false
check-no-dots (_ ∷ l) = check-no-dots l

check-all-vars : List TyPat → Bool
check-all-vars [] = true
check-all-vars ((_ , arg _ (var _)) ∷ l) = check-all-vars l
check-all-vars (_ ∷ l) = false

check-conlit : List TyPat → Bool
check-conlit [] = false
check-conlit ((_ , arg _ (con _ _)) ∷ l) = true
check-conlit ((_ , arg _ (lit _)) ∷ l) = true
check-conlit (_ ∷ l) = check-conlit l

{-# TERMINATING #-}
compute-ctx : List TyPat → TC $ Err $ List TyPat
compute-ctx typats with check-no-dots typats ∧ check-all-vars typats
... | true = return $ ok typats
... | false with check-conlit typats
... | true = do
      eqs , typats ← pats-ctx-open-cons typats []
      case typats of λ where
        (error s) → return $ error s
        (ok t) → let
          sub = eqs-elim-nondots (eqs ++ map (λ { (l ↦ r) → r ↦ l}) eqs) (get-dots (reverse t) 0)
          t = subst-eq-typats sub (reverse t)
          t = try-elim-dots (reverse t)
          in compute-ctx t
... | false = return $ error "compute-ctx: can't eliminate dots in the context"


-- try normalising every clause of the pat-lam, given
-- the context passed as an argument.  Propagate error that
-- can be produced by pats-ctx.
pat-lam-norm : Term → Ctx → TC $ Err Term
pat-lam-norm (pat-lam cs args) ctx = do
  cs ← hlpr ctx cs
  case cs of λ where
    (ok cs) → return $ ok (pat-lam cs args)
    (error s) → return $ error s
  --return $ ok (pat-lam cs args)
  where
    hlpr : Ctx → List Clause → TC $ Err (List Clause)
    hlpr ctx [] = return $ ok []
    hlpr ctx (clause ps t ∷ l) = do
      case merge-tys-pats ctx ps of λ where
        (error s) → return $ error s
        (ok typats) → do
           typats ← compute-ctx typats
           case typats of λ where
             (ok typats) → do
               let ctx′ = map proj₁ typats
               t ← inContext (reverse ctx′) (normalise t)
               l ← hlpr ctx l
               return $ ok [ clause ps t ] ++ l
             (error s) →
               --return $ clause ps t ∷ l
               -- Make sure that we properly error out
               -- Uncomment above line, in case you want to skip the error.
               return $ error s
    hlpr ctx (a ∷ l) = do
      l' ← hlpr ctx l
      return (ok [ a ] ++ l')
      --return (a ∷ l')
pat-lam-norm x ctx = return $ error "pat-lam-norm: Shouldn't happen" --return $ ok x



macro
  reflect : Term → Term → TC ⊤
  reflect f a = -- not sure I need this
                --withNormalisation true
                normalise f >>=
                (derefImmediate)
                >>= quoteTC >>= unify a

  reflect-ty : Name → Type → TC ⊤
  reflect-ty f a = getType f >>= quoteTC >>= normalise >>= unify a

  tstctx : Name → Type → TC ⊤
  tstctx f a = do
    t ← getType f
    q ← quoteTC (con-to-ctx t)
    unify a q

  rtest : Term → Term → TC ⊤
  rtest f a = do
     t ← derefT f
     v ← derefImmediate f
     v ← pat-lam-norm v (pi-to-ctx t)
     q ← quoteTC v
     --q ← quoteTC (con-to-ctx t)
     unify a q

  norm-test : Term → Term → TC ⊤
  norm-test tm a = do
    t ← derefT tm
    v ← derefImmediate tm
    --let vec-and'-pat-[] = (hArg dot ∷ vArg (con (quote nil) []) ∷ vArg (var "_") ∷ [])
    {-
    let add-2v-pat = (hArg (var "_") ∷
                      vArg (con (quote imap) (hArg dot ∷ vArg (var "a") ∷ [])) ∷
                      vArg (con (quote imap) (hArg dot ∷ vArg (var "b") ∷ [])) ∷ [])
    -}
    {-
    let vec-sum-pat = (hArg dot ∷
                       vArg
                       (con (quote V._∷_)
                        (hArg (var "_") ∷ vArg (var "x") ∷ vArg (var "a") ∷ []))
                       ∷
                       vArg
                       (con (quote V._∷_)
                        (hArg dot ∷ vArg (var "y") ∷ vArg (var "b") ∷ []))
                       ∷ [])
    -}
    let vec-sum-pat-[] = (hArg dot ∷ vArg (con (quote V.[]) []) ∷ vArg (var "_") ∷ [])


    {-
    let ty-args = args-to-ctx vec-args 0
    t ← getType (quote V._∷_)
    let t = subst-args 2 (reverse $ take-ctx' ty-args 2) 0 t
    -}
    let ctx = pi-to-ctx t
    case merge-tys-pats ctx vec-sum-pat-[] of λ where
      (error s) → unify a (lit (string s))
      (ok typats) → do
         eqs , t ← pats-ctx-open-cons typats []
         --let t = ok typats
         case t of λ where
           (error s) → unify a (lit (string s))
           (ok t) → do
              -- let sub = eqs-elim-nondots (eqs ++ map (λ { (l ≜ r) → r ≜ l}) eqs) (get-dots (reverse t) 0)
              -- let t = subst-eq-typats sub (reverse t)
              -- let t = try-elim-dots (reverse t)
              q ← quoteTC t
              unify a q


    --t ← inferType v -- (vArg n ∷ [ vArg lz ]))
    --let v = plug-new-args v (vArg n ∷ [ vArg lz ])
    --t ← inContext (reverse $ hArg lz ∷ [ hArg n ]) (normalise v)
    --t ← reduce t
    --t ← getType t
    --t ← inContext [] (normalise t)
    --q ← quoteTC (pi-to-ctx t)



  infert : Type → Term → TC ⊤
  infert t a = inferType t >>= quoteTC >>= unify a

-- {-
open import Data.Vec
vec-and : ∀ {n} → Vec Bool n → Vec Bool n → Vec Bool n
vec-and (x ∷ a) (y ∷ b) = x ∧ y ∷ vec-and a b
vec-and [] _ = []

-- explicit length
vec-and-nd : ∀ {n} → Vec Bool n → Vec Bool n → Vec Bool n
vec-and-nd {0}     []      _ = []
vec-and-nd {suc n} (_∷_ {n = n} x a) (_∷_ {n = n} y b) = x ∧ y ∷ vec-and-nd a b


data Vec' {l : Level} (A : Set l) : ℕ → Set l where
  nil  : Vec' A 0
  cons : A → {n : ℕ} → Vec' A n → Vec' A (1 + n)

vec-and' : ∀ {n} → Vec' Bool n → Vec' Bool n → Vec' Bool n
vec-and' nil _ = nil
vec-and' (cons x a) (cons y b) = cons (x ∧ y) (vec-and' a b)

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE +-identityʳ #-}

a = 1 + 0


xx : ℕ → Bool → ℕ → ℕ
xx x true y = let a = x * x in a + y
xx x false y = x + 2 + 0

postulate
  rev-rev : ∀ {a}{X : Set a}{n}{xs : Vec X n} →
            let rev = V.foldl (Vec X) (λ rev x → x ∷ rev) [] in
            rev (rev xs) ≡ xs

{-# REWRITE rev-rev #-}

test-reverse : ∀ {a}{X : Set a}{n} → X → Vec X n → Vec X (suc n)
test-reverse x xs =  x ∷ V.reverse (V.reverse xs)

test-rev-pat : ∀ {a}{X : Set a}{n} → X → Vec X n → Vec X (suc n)
test-rev-pat x [] = x ∷ []
test-rev-pat x xs = x ∷ V.reverse (V.reverse xs)


open import Array
add-2v : ∀ {n} → let X = Ar ℕ 1 (n ∷ []) in X → X → X
add-2v (imap a) (imap b) = imap λ iv → a iv + b iv

postulate
  asum : ∀ {n} → Ar ℕ 1 (n ∷ []) → ℕ


mm : ∀ {m n k} → let Mat a b = Ar ℕ 2 (a ∷ b ∷ []) in
                 Mat m n → Mat n k → Mat m k
mm (imap a) (imap b) = imap λ iv → let i = ix-lookup iv (# 0)
                                       j = ix-lookup iv (# 1)
                                   in asum (imap λ kv → let k = ix-lookup kv (# 0)
                                                        in a (i ∷ k ∷ []) * b (k ∷ j ∷ []))


data P (x : ℕ) : Set where
  c : P x

data TT : ℕ → Set where
  tc : ∀ {n} → P (suc n) → TT (suc n)


foo : ∀ {n} → TT (suc n) → ℕ
foo (tc x) = 5
  
xxx = 3 N.< 5
