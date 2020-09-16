{-# OPTIONS --rewriting  #-}
open import Array 
open import Array.APL using (reduce-1d)

open import Data.Nat as N
open import Data.Nat.Properties
open import Data.Vec as V hiding (_>>=_; _++_)
open import Data.Fin using (Fin; zero; suc; raise; inject+; #_)
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Function

open import Relation.Nullary
open import Relation.Nullary.Decidable





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


sum-2d : ∀ {m n} → Ar ℕ 2 (m ∷ n ∷ []) → ℕ
sum-2d (imap a) = sum-1d (imap λ i → sum-1d (imap λ j → a $ i ix++ j))

_+'_ : ∀ {m n} → Fin (1 + m) → Fin (1 + n) → Fin (1 + m + n)
_+'_ {m} {n} zero j = subst Fin (+-suc m n) (raise m j)
_+'_ {suc m} {n} (suc i) j = suc (i +' j)

_+''_ : ∀ {m n} → Fin m → Fin n → Fin (m + n ∸ 1)
_+''_ {suc m} {suc n} zero j = raise m j
_+''_ {suc (suc m)} {suc n} (suc i) j = suc (i +'' j)

_ix+2_ : ∀ {m n k p} → Ix 2 (m ∷ n ∷ []) → Ix 2 (k ∷ p ∷ []) → Ix 2 (m + k ∸ 1 ∷ n + p ∸ 1 ∷ [])
(x₁ ∷ x₂ ∷ []) ix+2 (y₁ ∷ y₂ ∷ []) = x₁ +'' y₁ ∷ (x₂ +'' y₂) ∷ []

conv-2 : ∀ {m n k p} → Ar ℕ 2 (m + k ∷ n + p ∷ []) → Ar ℕ 2 (k ∷ p ∷ []) → Ar ℕ 2 (1 + m ∷ 1 + n ∷ [])
conv-2 {k = k} {p} (imap a) (imap w) = imap (λ iv → sum-2d {m = k} {n = p} (imap λ ov → w ov * a (iv ix+2 ov)))



iterate-1 : ∀ {a}{X : Set a}{n} → (Fin n → X) → (X → X → X) → X → X
iterate-1 {n = zero}  f _⊕_ neut = neut
iterate-1 {n = suc n} f _⊕_ neut = f zero ⊕ iterate-1 (f ∘ suc) _⊕_ neut

red-iter : ∀ {a}{X : Set a}{n} → (f : Ix 1 (n ∷ []) → X) → (op : X → X → X) → (neut : X)
         → reduce-1d (imap f) op neut ≡ iterate-1 (λ i → f (i ∷ [])) op neut
red-iter {n = zero}  f op neut = refl
red-iter {n = suc n} f op neut = cong (λ x → op _ x) (red-iter (λ iv → f (suc (hd iv) ∷ [])) op neut)



{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE red-iter    #-}


thm : ∀ {n} → (m : Ar ℕ 2 (n ∷ n ∷ []))
    → (v : Ar _ _ (n ∷ []))
    → ∀ iv → unimap (twice m v) iv ≡ {!!}
thm (imap m) (imap v) (i ∷ []) = {!!}

{-
-- Reflection business
open import Reflection
open import Data.List hiding (_++_)
open import Data.Bool
open import Data.Maybe hiding (_>>=_)
open import Data.Unit

defToTerm : Name → Definition → List (Arg Term) → Term
defToTerm _ (function cs) as = pat-lam cs as
defToTerm _ (constructor′ d) as = con d as
defToTerm _ _ _ = unknown

derefImmediate : Term → TC Term
derefImmediate (def f args) = getDefinition f >>= λ f' → return (defToTerm f f' args)
derefImmediate x = return x

--reflectTerm : TC Term
--reflectTerm = (getType (quote f)) >>= λ ty → quoteTC f >>= derefImmediate >>= λ x → checkType x ty

macro
  reflect : Term → Term → TC ⊤
  reflect f a = derefImmediate f -- (quoteTerm f)
                >>= quoteTC >>= unify a

  reflect-ty : Name → Type → TC ⊤
  reflect-ty f a = getType f >>= quoteTC >>= unify a

r : Term
r = reflect twice

open import Data.String
open import Data.Nat.Show as Ns
open import Data.List as L using (List)


data Prog : Set where
  ok : String → Prog
  error : String → Prog

record State : Set where
  inductive
  constructor st
  field
   vars : List String
   defs : List $ String × String
   cons : List (String × ((List $ Arg Term) → Prog))




var-lkup : State → ℕ → Prog
var-lkup s n = hlpr (State.vars s) n
  where hlpr : _ → _ → _
        hlpr [] n = error $ "Variable not found"
        hlpr (x ∷ l) zero = ok x
        hlpr (x ∷ l) (suc n) = hlpr l n

def-lkup : State → String → Prog
def-lkup ss s = hlpr (State.defs ss) s
  where hlpr : _ → _ → _
        hlpr [] s = error $ "Definition `" ++ s ++ "' not found"
        hlpr ((k , v) ∷ dfs) s with k ≈? s
        ... | yes p = ok v
        ... | no ¬p = hlpr dfs s

cons-cont : State → String → List (Arg Term) → Prog
cons-cont ss s args = {!!} {-hlpr (State.cons ss) s args
  where hlpr : _ → _ → _ → _
        hlpr [] s _ = error $ "Constructor `" ++ s ++ "' not found"
        hlpr ((k , f) ∷ cs) s args with k ≈? s
        ... | yes p = f args
        ... | no ¬p = hlpr cs s args
-}
infixl 5 _#_
_#_ : Prog → Prog → Prog
ok x # ok y = ok $ x ++ y
error x # _ = error x
_ # error y = error y


l→s : List String → String
l→s [] = ""
l→s (x ∷ l) = x ++ " " ++ l→s l

comp-arglist-mask : State → List (Arg Term) → List Bool → Prog

comp-arglist : State → List (Arg Term) → Prog
comp-clauses : State → List Clause → Prog

_at_ : ∀ {a}{X : Set a} → List X → ℕ → Maybe X
[] at idx = nothing
(x ∷ a) at zero = just x
(x ∷ a) at suc idx = a at idx

unmaybe : ∀ {a}{X : Set a} → List (Maybe X) → Maybe (List X)
unmaybe [] = just []
unmaybe (nothing ∷ xs) = nothing
unmaybe (just x ∷ xs) with unmaybe xs
unmaybe (just x ∷ xs) | nothing = nothing
unmaybe (just x ∷ xs) | just xs' = just $ x ∷ xs'


filter-idx : ∀ {a}{X : Set a} → List X → List ℕ → Maybe (List X)
filter-idx xs idxs = unmaybe $ L.map (xs at_) idxs

_!!_ : ∀ {a}{X : Set a} → (xs : List X) → Fin (L.length xs) → X
[] !! ()
(x ∷ xs) !! zero = x
(x ∷ xs) !! suc i = xs !! i

mk-mask : (n : ℕ) → List (Fin n) → List Bool
mk-mask n xs = V.toList $ go (V.replicate {n = n} false) xs
  where go : _ → _ → _
        go e [] = e
        go e (x ∷ xs) = go (updateAt x (λ _ → true) e) xs

compile : State → Term → Prog
compile s (var x args) = ok "V(" # var-lkup s x # ok " " # comp-arglist s args # ok ")"
compile s (con c args) with (showName c)
compile s (con c args) | "Data.Vec.Base.Vec.[]" = ok "nil"
compile s (con c args) | "Array.Base.Ix.[]" = ok "nil"
compile s (con c args) | "Data.Vec.Base.Vec._∷_" =
   ok "(cons " # comp-arglist-mask s args (mk-mask 5 $ # 3 ∷ # 4 ∷ []) # ok ")"
compile s (con c args) | "Array.Base.Ix._∷_" =
   ok "(cons " # comp-arglist-mask s args (mk-mask 5 $ # 3 ∷ # 4 ∷ []) # ok ")"
compile s (con c args) | _ = ok ("C(" ++ showName c ++ " ") # comp-arglist s args # ok ")"

compile s (def f args) with def-lkup s $ showName f
... | error _ = ok "D(" # ok (showName f) # ok " " # comp-arglist s args
... | d       = ok "D(" # d # ok " "
                        # comp-arglist s args # ok ")"

compile s (lam v (abs w x)) = ok ("(\\ " ++ w ++ " -> ") # compile (record s {vars = (w ∷ State.vars s)}) x # ok ")"
compile s (pat-lam cs []) = ok "PAT-LAM (cl = " # comp-clauses s cs # ok ")" --(args = " # comp-arglist s args # ok ")"
compile s (pat-lam cs _) = error "PAT-LAM: I don't know what args to pat-lam are"
compile s (pi a b) = ok "PI TYPE"
compile s (sort _) = ok "SORT"
compile s (lit x) = ok $ showLiteral x
compile s (meta x x₁) = ok "META"
compile s unknown = ok "_" -- "UNKNOWN"


comp-arglist s [] = ok ""
comp-arglist s (arg i x ∷ l) = compile s x # ok " " # comp-arglist s l

comp-arglist-mask s [] [] = ok ""
comp-arglist-mask s [] (x ∷ mask) = error "Incorrect argument mask"
comp-arglist-mask s (x ∷ args) [] = error "Incorrect argument mask"
comp-arglist-mask s (x ∷ args) (false ∷ mask) = comp-arglist-mask s args mask
comp-arglist-mask s (arg i x ∷ args) (true ∷ mask) = compile s x # ok "  " # comp-arglist-mask s args mask

comp-pats : List (Arg Pattern) → List String
comp-pats [] = []
comp-pats (vArg (var x) ∷ l) = x ∷ comp-pats l
comp-pats (vArg _ ∷ l) = "_" ∷ comp-pats l
comp-pats (_ ∷ l) = "_" ∷ comp-pats l

comp-clauses s [] = ok ""
comp-clauses s (clause ps t ∷ cs) = let
   vars = comp-pats ps
   in ok ("pats = " ++ l→s vars) # compile (record s {vars = (L.reverse vars L.++ State.vars s)}) t
comp-clauses s (absurd-clause ps ∷ cs) = error "absurd clause found"






test : ∀ {n} (m : Ix 2 (n ∷ n ∷ []) → ℕ) (v : Ix 1 (n ∷ []) → ℕ)
         (i : Fin n) → ℕ
test m v i = iterate-1
       (λ i₁ →
          m (i ∷ i₁ ∷ []) *
          iterate-1 (λ i₂ → m (i₁ ∷ i₂ ∷ []) * v (i₂ ∷ [])) _+_ 0)
       _+_ 0


bltin-defs : List $ String × String
bltin-defs = ("Agda.Builtin.Nat.Nat" , "nat")
           ∷ ("Agda.Builtin.Nat._+_" , "plus")
           ∷ ("Agda.Builtin.Nat._*_" , "mult")
           ∷ ("Agda.Primitive.lzero" , "tt")
           ∷ ("BLAS.iterate-1" , "for-loop-acc")
           ∷ []

bltin-cons : List (String × (List (Arg Term) → Prog))
bltin-cons = ("Data.Vec.Base.Vec.[]" , λ _ → ok "nil")
           ∷ ("Array.Base.Ix.[]" , λ _ → ok "nil")
           ∷ ("Array.Base.Ix._∷_" , λ args → {!!})
           ∷ []

ct = compile (st [] bltin-defs []) (reflect test)

foo : ∀ {n : ℕ} (a b : ℕ) → ℕ
foo x = _+ x

cr = compile (st [] bltin-defs []) (reflect foo)

cconv = compile (st [] bltin-defs []) (reflect conv-2)

-}

--t : Term
--t = reflect-ty (thm)

-- PAT-LAM (cl = pats = _ m v i D(BLAS.iterate-1 D(Agda.Primitive.lzero ) D(Agda.Builtin.Nat.Nat ) V(i )
--         (\\ i₁ -> D(Agda.Builtin.Nat._*_
--                        V(v C(Array.Base.Ix._∷_ 1 C(Data.Vec.Base.Vec._∷_ UNKNOWN UNKNOWN 0 V(i ) C(Data.Vec.Base.Vec.[] UNKNOWN UNKNOWN ) )
--                                                  V(i )
--                                                  V(_ )
--                                                  C(Array.Base.Ix._∷_ 0 C(Data.Vec.Base.Vec.[] UNKNOWN UNKNOWN ) V(i ) V(i₁ ) C(Array.Base.Ix.[] ) ) ) )
--                        D(BLAS.iterate-1 D(Agda.Primitive.lzero ) D(Agda.Builtin.Nat.Nat ) V(i )
--                         (\\ i₂ -> D(Agda.Builtin.Nat._*_
--                                     V(v C(Array.Base.Ix._∷_ 1 C(Data.Vec.Base.Vec._∷_ UNKNOWN UNKNOWN 0 V(i ) C(Data.Vec.Base.Vec.[] UNKNOWN UNKNOWN ) )
--                                                               V(i )
--                                                               V(i₁ )
--                                                               C(Array.Base.Ix._∷_ 0 C(Data.Vec.Base.Vec.[] UNKNOWN UNKNOWN )
--                                                                                     V(i ) V(i₂ ) C(Array.Base.Ix.[] ) ) ) )
--                                     V(m C(Array.Base.Ix._∷_ 0 C(Data.Vec.Base.Vec.[] UNKNOWN UNKNOWN ) V(i ) V(i₂ ) C(Array.Base.Ix.[] ) ) ) ))
--                         D(Agda.Builtin.Nat._+_ ) 0 ) ))
--         D(Agda.Builtin.Nat._+_ ) 0 )) (args = )


--compld _ m v i = D(for-loop-acc D(tt ) D(nat ) V(_ )
--                               (\\ i₁ -> D(mult V(m (cons V(i )  (cons V(i₁ )  nil  )  ) )
--                                                D(for-loop-acc D(tt ) D(nat ) V(_ )
--                                                              (\\ i₂ -> D(mult V(m (cons V(i₁ )  (cons V(i₂ )  nil  )  ) )
--                                                                               V(v (cons V(i₂ )  nil  ) ) ))
--                                                                               D(plus ) 0 ) ))
--                               D(plus ) 0 )


-- A * v = { i → Σ Aᵢ×v }
-- A * A * v = { i → Σ Aᵢ×v }
