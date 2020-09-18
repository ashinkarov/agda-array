{-# OPTIONS --rewriting  #-}
open import Reflection hiding (return; _>>=_) renaming (_≟_ to _≟r_)
open import Reflection.Term
--open import Reflection.Definition

open import Data.List hiding (_++_)
open import Data.Maybe hiding (_>>=_; map)
open import Data.Unit
open import Data.Nat as N
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.String renaming (_++_ to _++s_; concat to sconc; length to slen)
open import Data.Char renaming (_≈?_ to _c≈?_; show to showChar)



open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Data.Nat.Show renaming (show to showNat)
open import Function

open import Category.Monad using (RawMonad)


Ctx = List $ Arg Type
TyPat = Arg Type × Arg Pattern

data Err {a} (A : Set a) : Set a where
  error : String → Err A
  ok : A → Err A

open RawMonad {{...}} public
instance
  monadMB : ∀ {f} → RawMonad {f} Maybe
  monadMB = record { return = just ; _>>=_ = Data.Maybe._>>=_ }

  monadTC : ∀ {f} → RawMonad {f} TC
  monadTC = record { return = Reflection.return ; _>>=_ = Reflection._>>=_ }

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
defToTerm _ (data-cons d) as = con d as
defToTerm _ _ _ = unknown

derefImmediate : Term → TC Term
derefImmediate (def f args) = getDefinition f >>= λ f' → return (defToTerm f f' args)
derefImmediate x = return x

derefT : Term → TC Term
derefT (def f args) = getType f
derefT (con f args) = getType f
derefT x = return x



merge-tys-pats : List $ Arg Type → List $ Arg Pattern → Err $ List TyPat
merge-tys-pats [] [] = ok []
merge-tys-pats [] (x ∷ ps) = error "merge-tys-pats: more patterns than types"
merge-tys-pats (x ∷ tys) [] = error "merge-tys-pats: more types than patterns"
merge-tys-pats (ty ∷ tys) (p ∷ ps) = ok [ ty , p ] ++ merge-tys-pats tys ps



pat-lam-norm : Term → TC $ Err Term
pat-lam-norm (pat-lam cs args) = do
  cs ← hlpr cs
  case cs of λ where
    (ok cs) → return $ ok (pat-lam cs args)
    (error s) → return $ error s
  where
    hlpr : List Clause → TC $ Err (List Clause)
    hlpr [] = return $ ok []
    hlpr (clause tel ps t ∷ l) = do
      let ctx = map proj₂ tel
      t ← inContext (reverse ctx) (normalise t)
      l ← hlpr l
      return $ ok [ clause tel ps t ] ++ l
    hlpr (absurd-clause tel ps ∷ l) = do
      l ← hlpr l
      return $ ok [ absurd-clause tel ps ] ++ l
pat-lam-norm t = return $ error "pat-lam-norm: Shouldn't happen"


macro
  rtest : Term → Term → TC ⊤
  rtest f a = do
     t ← derefT f
     v ← derefImmediate f
     v ← pat-lam-norm v --(pi-to-ctx t)
     q ← quoteTC v
     --q ← quoteTC (con-to-ctx t)
     unify a q

open import Data.Vec as V
open import Data.Bool
vec-and : ∀ {n} → Vec Bool n → Vec Bool n → Vec Bool n
vec-and (x ∷ a) (y ∷ b) = x ∧ y ∷ vec-and a b
vec-and [] _ = []

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE +-identityʳ #-}


xx : ℕ → Bool → ℕ → ℕ
xx x true y = let a = x * x in a + y
xx x false y = x + 2 + 3 + 0

postulate
  rev-rev : ∀ {a}{X : Set a}{n}{xs : Vec X n} →
            let rev = V.foldl (Vec X) (λ rev x → x ∷ rev) [] in
            rev (rev xs) ≡ xs

{-# REWRITE rev-rev #-}

xreverse : ∀ {a}{X : Set a}{n} → X → Vec X n → Vec X (suc n)
xreverse x xs =  x ∷ V.reverse (V.reverse xs)



