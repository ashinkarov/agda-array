open import Reflection hiding (return; _>>=_)

open import Data.List renaming (_++_ to _++l_)
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
open import Data.Char renaming (_≈?_ to _c≈?_)

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
    _++_ = _++l_;
    ε = []
    }

  monoidStr : RawMonoid String
  monoidStr = record {
    _++_ = _++s_;
    ε = ""
    }

  monoidErrStr : RawMonoid (Err String)
  monoidErrStr = record {
    _++_ =  λ where
      (error s) _ → error s
      _ (error s) → error s
      (ok s₁) (ok s₂) → ok (s₁ ++ s₂)
    ;
    ε = ok ""
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

defName : Term → Maybe Name
defName (def f args) = just f
defName _ = nothing

Ctx = List $ Arg Type

pi-to-ctx : Term → Ctx

-- we have a Ctx for the entire function, now we want to build
-- a context for the given variables in the clause.  To do so
-- we merge function's ctx with patterns of the given clause
-- and we grab the types that correspond to the variables within
-- the patterns.
--pats-ctx : Ctx → (List $ Arg Pattern) → TC $ Maybe Ctx

macro
  reflect : Term → Term → TC ⊤
  reflect f a = (derefImmediate f)
                >>= quoteTC >>= unify a

  reflect-ty : Name → Type → TC ⊤
  reflect-ty f a = getType f >>= quoteTC >>= normalise >>= unify a

  rtest : Term → Term → TC ⊤
  rtest f a = do
     t ← derefT f
     v ← derefImmediate f
     --v ← pat-lam-no--rm v (pi-to-ctx t)
     --q ← quoteTC v
     q ← quoteTC (pi-to-ctx t)
     unify a q

  rmkstring : Term → Term → TC ⊤
  rmkstring f a = unify (lit (string "Test")) a

  infert : Type → Term → TC ⊤
  infert t a = inferType t >>= quoteTC >>= unify a

-- FIXME we probably want to error out on these two functions.
pi-to-ctx (Π[ s ∶ a ] x) = (a ∷ pi-to-ctx x)
pi-to-ctx _ = []


Prog = Err $ List String
infixl 5 _#p_
_#p_ = _++_

okl : String → Prog
okl s = ok ([ s ])

-- reduce a list of Progs with a delimiter
_/#p_ : List Prog → (delim : String) → Prog
[] /#p d = ok []
(x ∷ []) /#p d = x
(x ∷ xs@(_ ∷ _)) /#p d = x #p okl d #p xs /#p d


-- Normalise the name of functions that we obtain from showName,
-- i.e. remove dots, replace weird symbols by ascii.
nnorm : String → Prog
nnorm s = okl
        $ replace '.' '_'
        $ replace '-' '_'
        $ s
  where
    repchar : (t f x : Char) → Char
    repchar f t x with x c≈? f
    ... | yes _ = t
    ... | no  _ = x

    replace : (from to : Char) → String → String
    replace f t s = fromList $ map (repchar f t) $ toList s


data NumClauses : Set where
  Many One : NumClauses

record State : Set where
  constructor st
  field
    --arg-ctx     : Ctx
    --ret-typ     : String
    var-names   : List String
    retvar      : String
    cls         : NumClauses
open State


--compile-clause : Clause → State → Prog

-- Pack the information about new variables generated
-- by patterns in the clause, assignments to these,
-- and the list of conditions.  E.g.
--   foo : List ℕ → ℕ
--   foo (x ∷ xs) 2 = ...
--
-- Assume that we named top-level arguments [a, b]
-- Then, new variables for this clause are going to be
--     [x, xs]
-- Assignments are:
--     [x = hd a, xs = tl a]
-- Conditions are:
--     [is-cons a, b = 2]
record ClCond : Set where
  constructor clcond
  field
    vars    : List String
    assigns : List String
    conds   : List String

data MbClCond : Set where
  ok     : ClCond → MbClCond
  error  : String → MbClCond

_#c_ : MbClCond → MbClCond → MbClCond
error s #c _ = error s
_ #c error s = error s
ok (clcond a b c) #c ok (clcond a' b' c') = ok (clcond (a ++ a') (b ++ b') (c ++ c'))

{-# TERMINATING #-}
clause-ctx-vars : (pats : List $ Arg Pattern) → (vars : List String) → (counter : ℕ) → MbClCond

showLitProg : Literal → Prog

comp-term : Term → (varctx : List String) → Prog

sjoin : List String → String → String
sjoin [] delim = ""
sjoin (x ∷ []) delim = x
sjoin (x ∷ xs@(_ ∷ _)) delim = x ++s delim ++s sjoin xs delim


join' : List String → (delim : String) → (empty : String) → String
join' []        _ e = e
join' x@(_ ∷ _) d _ = sjoin x d

compile-cls : List Clause → State → Prog
compile-cls [] s = error "comile-cls: expected at least one clause"
compile-cls (clause ps t ∷ []) s with clause-ctx-vars ps (var-names s) 0
... | error msg = error msg
... | ok (clcond vars assgns conds) = let
        as = sconc (map (_++s "\n") assgns)
        rv = retvar s ++s " = "
    in okl (as ++s rv) #p comp-term t vars #p okl ";"
compile-cls (absurd-clause ps ∷ []) s with clause-ctx-vars ps (var-names s) 0
... | error msg = error msg
... | ok (clcond vars assgns conds) = okl "unreachable ();"
compile-cls (clause ps t ∷ xs@(_ ∷ _)) s with clause-ctx-vars ps (var-names s) 0
... | error msg = error msg
... | ok (clcond vars assgns conds) = let
        cs = join' conds " && " "true"
        as = sconc (map (_++s "\n") assgns)
        rv = retvar s ++s " = "
    in okl ("if (" ++s cs ++s ") {" ++s as ++s rv) #p comp-term t vars #p okl "; }"
       #p okl "else {"
       #p compile-cls xs s
       #p okl "}"
compile-cls (absurd-clause ps ∷ xs@(_ ∷ _)) s with clause-ctx-vars ps (var-names s) 0
... | error msg = error msg
... | ok (clcond vars assgns conds) = let
        -- XXX it would be weird if conds were empty... catch it?
        cs = join' conds " && " "true"
    in okl ("if (" ++s cs ++s ") { unreachable (); } else {" )
       #p compile-cls xs s
       #p okl "}"

clause-ctx-vars (arg i (con c ps) ∷ l) (v ∷ vars) vcnt with showName c
... | "Agda.Builtin.List.List.[]" =
           ok (clcond [] [] [ "emptyvec_p (" ++s v ++s ")" ])
           #c clause-ctx-vars l vars vcnt
... | "Agda.Builtin.List.List._∷_" =
           ok (clcond [] [] [ "nonemptyvec_p (" ++s v ++s ")" ])
           #c clause-ctx-vars (ps ++ l) (("hd (" ++s v ++s ")") ∷ ("tl (" ++s v ++s ")") ∷ vars) vcnt
... | "Agda.Builtin.Bool.Bool.true" =
           ok (clcond [] [] [ v {- == true -} ])
           #c clause-ctx-vars l vars vcnt
... | "Agda.Builtin.Bool.Bool.false" =
           ok (clcond [] [] [ "! " ++s v ])
           #c clause-ctx-vars l vars vcnt
... | "Agda.Builtin.Nat.Nat.suc" =
           ok (clcond [] [] [ v ++s " > 0" ])
           #c clause-ctx-vars (ps ++ l) ((v ++s " - 1") ∷ vars) vcnt
... | "Agda.Builtin.Nat.Nat.zero" =
           ok (clcond [] [] [ v ++s " == 0" ])
           #c clause-ctx-vars l vars vcnt
... | "Data.Fin.Base.Fin.zero" =
           ok (clcond [] [] [ v ++s " == 0" ])  -- XXX can also add v < u
           #c clause-ctx-vars l vars vcnt
... | "Data.Fin.Base.Fin.suc" =
           ok (clcond [] [] [ v ++s " > 0" ])  -- XXX can also add v < u
           #c clause-ctx-vars l vars vcnt
... | "Data.Vec.Base.Vec.[]"  =
           ok (clcond [] [] [ "emptyvec_p (" ++s v ++s ")" ])
           #c clause-ctx-vars l vars vcnt
... | "Data.Vec.Base.Vec._∷_" =
           ok (clcond [] [] [ "nonemptyvec_p (" ++s v ++s ")" ])
           #c clause-ctx-vars (ps ++ l) (("len (" ++s v ++s ") - 1") ∷ ("hd (" ++s v ++s ")") ∷ ("tl (" ++s v ++s ")") ∷ vars) vcnt
      -- Well, let's see how far we can go with this hack
... | "Array.Base.Ar.imap" =
--... | "test-extract.Ar'.imap" =
           ok (clcond [ "IMAP_" ++s v ] [ "\n#define IMAP_" ++s v ++s "(__x) " ++s v ++s "[__x]\n" ] [ "true" ])
           #c clause-ctx-vars l vars vcnt
... | x = error ("clause-ctx-vars: don't know what to do with `" ++s x ++s "` constructor in patterns")
clause-ctx-vars (arg i dot ∷ l) (v ∷ vars) vcnt =
           -- Dot patterns are skipped.
           clause-ctx-vars l vars vcnt
clause-ctx-vars (arg (arg-info visible r) (var s) ∷ l) (v ∷ vars) vcnt =
           -- If we have "_" as a variable, we need  to insert it
           -- into the list, but we don't generate an assignment for it.
           let asgn = case s ≈? "_" of λ where
                          -- XXX hopefully this is fine, otherwise
                          -- we can do the same thing as for hidden
                          -- vars.
                (yes p) → []
                (no ¬p) → [ s ++s " = " ++s v ++s ";" ]
           in ok (clcond [ s ] asgn [])
           #c clause-ctx-vars l vars vcnt
clause-ctx-vars (arg (arg-info hidden r) (var s) ∷ l) (v ∷ vars) vcnt =
           -- Hidden variables are simply added to the context
           -- as regular variables
           let s , vcnt = case s ≈? "_" of λ where
                (yes p) → s ++ "_" ++ showNat vcnt , 1 + vcnt
                (no ¬p) → s , vcnt
           in ok (clcond [ s ] [ s ++ " = " ++ v ++ ";" ] [])
           #c clause-ctx-vars l vars vcnt

clause-ctx-vars (arg (arg-info instance′ r) (var s) ∷ l) (v ∷ vars) vcnt =
           error "FIXME handle instance variables"
clause-ctx-vars (arg i (lit x) ∷ l) (v ∷ vars) vcnt =
           case showLitProg x of λ where
                (error s) → error s
                (ok s) → ok (clcond [] [] [ v ++s " == " ++s (sconc s) ])
                         #c clause-ctx-vars l vars vcnt
clause-ctx-vars (arg i (proj f) ∷ l) (v ∷ vars) vcnt =
           error "FIXME proj pattern"
clause-ctx-vars (arg i absurd ∷ l)  (v ∷ vars) vcnt =
           -- I assume that absurd can only appear in the
           -- absurd clause, therefore, we don't need a condition
           -- for this pattern, so we just skip it.
           clause-ctx-vars l vars vcnt
clause-ctx-vars [] [] _ =
           ok (clcond [] [] [])
clause-ctx-vars _  _  _ =
           error "mismatching number of patterns and types"


showLitProg (name x) = error ("Found name `" ++s (showName x) ++s "` as literal")
showLitProg (meta x) = error ("Found meta `" ++s (showMeta x) ++s "` as literal")
showLitProg x = okl (showLiteral x)


var-lkup : List String → ℕ → Prog
var-lkup [] n = error ("Variable not found")
var-lkup (x ∷ l) zero = okl x
var-lkup (x ∷ l) (suc n) = var-lkup l n


-- Compile each arg and join them with ", "
comp-arglist : List $ Arg Term → (varctx : List String) → Prog
comp-arglist args varctx = map (λ {(arg i x) → comp-term x varctx}) args /#p ", "

-- Helper for comp-arglist-mask
mk-mask : (n : ℕ) → List (Fin n) → List Bool
mk-mask n xs = V.toList $ go (V.replicate {n = n} false) xs
  where go : _ → _ → _
        go e [] = e
        go e (x ∷ xs) = go (updateAt x (λ _ → true) e) xs

comp-arglist-mask : List $ Arg Term → (mask : List Bool) → (varctx : List String) → Prog
comp-arglist-mask args mask varctx = go args mask varctx /#p ", "
  where
     go : List $ Arg Term → (mask : List Bool) → (varctx : List String) → List Prog
     go [] [] _ = []
     go [] (x ∷ mask) _ = [ error "Incorrect argument mask" ]
     go (x ∷ args) [] _ = [ error "Incorrect argument mask" ]
     go (x ∷ args) (false ∷ mask) vars = go args mask vars
     go (arg i x ∷ args) (true ∷ mask) vars = comp-term x vars ∷ go args mask vars



comp-term (var x []) vars = var-lkup (reverse vars) x
comp-term (var x args@(_ ∷ _)) vars = var-lkup (reverse vars) x #p okl "(" #p comp-arglist args vars #p okl ")"
--comp-term (var x (x₁ ∷ args)) vars with var-lkup (reverse vars) x
--comp-term (var x (x₁ ∷ args)) vars | ok l = error ("Variable " ++s (sconc l) ++s " used as a function call")
--comp-term (var x (x₁ ∷ args)) vars | error s = error s
comp-term (lit l) vars = showLitProg l
comp-term exp@(con c args) vars with showName c
... | "Data.Vec.Base.Vec.[]" =
      okl "[]"
... | "Data.Vec.Base.Vec._∷_" =
      okl "cons (" #p comp-arglist-mask args (mk-mask 5 $ # 3 ∷ # 4 ∷ []) vars #p okl ")"
... | "Agda.Builtin.Nat.Nat.suc" =
      okl "(1 + " #p comp-arglist-mask args (mk-mask 1 $ # 0 ∷ []) vars #p okl ")"
... | "Data.Fin.Base.Fin.zero" =
      okl "0"
... | "Data.Fin.Base.Fin.suc" =
      okl "(1 + " #p comp-arglist-mask args (mk-mask 2 $ # 1 ∷ []) vars #p okl ")"
... | "Array.Base.Ar.imap" =
--... | "test-extract.Ar'.imap" =
      case args of λ where
        (_ ∷ _ ∷ _ ∷ arg _ s ∷ arg _ (vLam x e) ∷ []) → let
             p = comp-term e (vars ++ [ x ])
             sh = comp-term s vars --infert exp
           in okl ("with { (. <= " ++s x ++s " <= .): ") #p p #p okl "; }:  genarray (" #p sh #p okl ")"
        _                               →
           error "comp-term: don't recognize arguments to imap"
... | "Array.Base.Ix.[]" =
      okl "[]"
... | "Array.Base.Ix._∷_" =
      okl "cons (" #p comp-arglist-mask args (mk-mask 5 $ # 3 ∷ # 4 ∷ []) vars #p okl ")"
... | n = error ("comp-term: don't know constructor `" ++s n ++s "`")
comp-term (def f args) vars with showName f
... | "Agda.Builtin.Nat._+_" =
      okl "_add_SxS_ (" #p comp-arglist args vars #p okl ")"
... | "Agda.Builtin.Nat._*_" =
      okl "_mul_SxS_ (" #p comp-arglist args vars #p okl ")"
... | "Data.Nat.DivMod._/_" =
      okl "_div_SxS_ (" #p comp-arglist-mask args (mk-mask 3 $ # 0 ∷ # 1 ∷ []) vars #p okl ")"
... | "Data.Fin.#_" =
      comp-arglist-mask args (mk-mask 3 $ # 0 ∷ []) vars
... | "Array.Base.ix-lookup" =
      case args of λ where
        (_ ∷ _ ∷ arg _ iv ∷ arg _ el ∷ []) → let
             iv′ = comp-term iv vars
             el′ = comp-term el vars
           in iv′ #p okl "[" #p el′ #p okl "]"
        _                                  →
           error "comp-term: don't recognize arguments to ix-lookup"
... | "Data.Vec.Base.[_]" =
      case args of λ where
        (_ ∷ _ ∷ arg _ x ∷ []) → okl "[" #p comp-term x vars #p  okl "]"
        _                      →
           error "comp-term: don't recognize arguments to Vec.[_]"

... | "Data.Fin.Base.raise" =
      -- Note that "raise" is a total junk, as it only makes sure that the
      -- Fin value is valid in some context; all we are interested in is the
      -- value of that Fin.
      case args of λ where
        (_ ∷ _ ∷ arg _ x ∷ []) → comp-term x vars
        _                      →
           error "comp-term: don't recognize arguments to Data.Fin.raise"

-- XXX we need to figure out what are we going to do with recursive functions,
--     as clearly its name can't be known in advance.  Probably add it to the
--     state?  Or maintain a list of functions?
... | n = nnorm n #p okl " ("  #p comp-arglist args vars #p okl ")"
--... | n = error ("comp-term: don't know definition `" ++s n ++s "`")
comp-term (lam v t) vars = error "comp-term: lambdas are not supported"
comp-term (pat-lam cs args) vars = error "comp-term: pattern-matching lambdas are not supported"
comp-term (pi a b) vars = error "comp-term: pi types are not supported"
comp-term (sort s) vars = error "comp-term: sorts are not supported" 
comp-term (meta x x₁) vars = error "comp-term: metas are not supported"
comp-term unknown vars = error "comp-term: unknowns are not supported"


record Pistate : Set where
  constructor pist-vc=_cv=_vctx=_tctx=_rv=_ret=_cons=_
  field
    var-counter : ℕ
    cur-var : String
    var-ctx : List String
    type-ctx : List String
    ret-var : String
    ret : Prog
    -- XXX come up with a better type for
    -- constraints on variables.
    cons : List (String × Prog)
open Pistate


trav-pi : Type → Pistate → Pistate
trav-pi (Π[ s ∶ arg i x ] y) pst
          = let
              varname = case s of λ where
                          "_" → "x_" ++s (showNat $ var-counter pst)
                          n   → n
              tp = trav-pi x (record pst {cur-var = varname}) -- ; cons = []})
            in case ret tp of λ where
              (error s) → tp
              (ok l)    → trav-pi y (record pst {var-counter = 1 + var-counter pst ;
                                                 cur-var = ret-var pst ;
                                                 var-ctx = var-ctx pst ++ [ varname ] ;
                                                 type-ctx = type-ctx pst ++ [ (sjoin l "") ] ;
                                                 cons =  cons tp}) --cons pst ++ cons tp })
trav-pi (con c args) pst with showName c
... | x = record pst {ret = error ("trav-pi: don't know how to handle `" ++s x ++s "` constructor")}
trav-pi (def f args) pst with showName f
... | "Agda.Builtin.Nat.ℕ" = record pst {ret = okl "int"}
... | "Agda.Builtin.Nat.Nat" = record pst {ret = okl "int"}
... | "Agda.Builtin.Bool.Bool" = record pst {ret = okl "bool"}
... | "Agda.Builtin.List.List" =
         -- We encode lists as 1-d arrays of their argument type.
         case args of λ where
           (_ ∷ arg i x ∷ _) → let tp = trav-pi x (record pst {cons = []})
                               in case ret tp of λ where
                                   (error s) → tp
                                   (ok l)    → record tp {ret = okl $ (sjoin l "") ++s "[.]"}
           _                 → record pst {ret = error "trav-pi: incorrect arguments to List"}

... | "Data.Vec.Base.Vec" =
         -- Vectors are also 1-d arrays (such as lists) but we extract
         -- a bit of extra infromation from these.
         case args of λ where
           (_ ∷ arg _ t ∷ arg _ x ∷ []) → let tp = trav-pi t (record pst {cur-var = "" {- XXX well, typeof (cur-var pst) is the thing -}
                                                                          }) --cons = []})
                                              p = comp-term x (var-ctx pst)
                                          in record tp {ret = ret tp #p okl "[.]" ;
                                                        cons = (cons tp)
                                                            ++ [ cur-var pst ,
                                                                 okl ("/* assert (shape (" ++s (cur-var pst) ++s ")[[0]] == ") #p p #p okl ") */" ]
                                                       }
           _                            → record pst {ret = error "trav-pi: incorrect arguments to Vec"}
... | "Data.Fin.Base.Fin" =
         case args of λ where
           (arg _ x ∷ []) → let
                p = comp-term x (var-ctx pst)
                in record pst {
                     ret  = okl "int";
                     cons = (cons pst)
                         ++ [ cur-var pst ,
                              okl ("/* assert (" ++s (cur-var pst) ++s " < ") #p p #p okl ") */"]
                   }
           _              →
                record pst {ret = error "trav-pi: incorrect arguments to Fin"}
... | "Array.Base.Ar" =
--... | "test-extract.Ar'" =
         case args of λ where
           (_ ∷ arg _ ty ∷ arg _ dim ∷ arg _ sh ∷ []) → let
                  ty′  = trav-pi ty pst
                  dim′ = comp-term dim (var-ctx pst)
                  sh′  = comp-term sh (var-ctx pst)
                in record ty′ {
                     ret = ret ty′ #p okl "[*]" ;
                     cons = cons ty′
                         ++ [ cur-var pst ,
                              okl ("/* assert (dim (" ++s (cur-var pst) ++s ") == ") #p dim′ #p okl " )*/" ]
                         ++ [ cur-var pst ,
                              okl ("/* assert (shape (" ++s (cur-var pst) ++s ") == ") #p sh′ #p okl " )*/" ]
                   }
           _                                     → 
                record pst {ret = error "trav-pi: incorrect arguments to Ar"}

... | x = record pst {ret = error ("trav-pi: don't know the `" ++s x ++s "` type")}
trav-pi _ pst = record pst {ret = error "trav-pi ERRR"}


find : List String → String → Bool
find [] x = false
find (y ∷ l) x with x ≈? y
... | yes _ = true
... | no _  = find l x

collect-var-cons : List (String × Prog) → (accum : List String) → List (String × Prog)
collect-var-cons [] acc = []
collect-var-cons ((x , v) ∷ l) acc with find acc x
... | true  = collect-var-cons l acc
... | false = (x , v #p collect l x) ∷ collect-var-cons l (x ∷ acc)
  where
     collect : _ → _ → _
     collect [] x = ok []
     collect ((y , v) ∷ l) x with y ≈? x
     ... | yes _ = v #p collect l x
     ... | no _ = collect l x

-- Get the value bound to the given variable or return (ok [])
lkup-var-cons : List (String × Prog) → String → Prog
lkup-var-cons [] s = ok []
lkup-var-cons ((x , v) ∷ xs) s with x ≈? s
... | yes _ = v
... | no  _ = lkup-var-cons xs s

fltr : List (String × Prog) → (var : String) → List (String × Prog)
fltr [] x = []
fltr ((y , v) ∷ l) x with x ≈? y
... | yes _ = fltr l x
... | no _ = (y , v) ∷ fltr l x


mkfun : Name → _ → Pistate → NumClauses → Prog
mkfun n cls ps nc = let
     rv = (ret-var ps)
     cs = collect-var-cons (cons ps) []
     arg-cons = map proj₂ $ fltr cs rv
     ret-cons = lkup-var-cons cs rv
  in (okl $ "// Function " ++s (showName n) ++s "\n")
  #p ret ps #p okl "\n"
  #p (nnorm $ showName n ++s "(")
  #p tvl (var-ctx ps) (type-ctx ps)
  #p okl ") {\n"
  --#p (cons ps) /#p "\n"
  #p arg-cons /#p "\n"
  #p ret ps #p okl (" " ++s rv ++s ";\n")
  #p compile-cls cls (st (var-ctx ps) rv nc)
  #p ret-cons
  #p okl ("return " ++s rv ++s ";\n}\n\n")
  where
    tvl : List String → List String → Prog
    tvl [] [] = ok []
    tvl [] (t ∷ typs) = error "more types than variables"
    tvl (x ∷ vars) [] = error "more variables than types"
    tvl (x ∷ []) (t ∷ []) = okl (t ++s " " ++s x)
    tvl (x ∷ []) (_ ∷ _ ∷ _) = error "more types than variables"
    tvl (_ ∷ _ ∷ _) (_ ∷ []) = error "more variables than types"
    tvl (x ∷ xs@(_ ∷ _)) (t ∷ ts@(_ ∷ _)) = okl (t ++s " " ++s x ++s ", ") #p tvl xs ts


compile' : (lam : Term) → (sig : Type) → (name : Maybe Name) → TC Prog
compile' (pat-lam cs args) t nm with nm
compile' (pat-lam cs args) t nm | nothing =
  return $ error "compile' got invalid function name"
compile' (pat-lam [] args) t nm | just x =
  return $ error "compile' got zero clauses in the lambda term"
compile' (pat-lam cs@(_ ∷ []) args) t nm | just x =
  -- XXX currently the name `__ret` is hardcoded.
  let ps = trav-pi t (pist-vc= 1 cv= "" vctx= [] tctx= [] rv= "__ret" ret= error "" cons= [])
  in return (mkfun x cs ps One)
compile' (pat-lam cs@(_ ∷ _ ∷ _) args) t nm | just x =
  -- XXX currently the name `__ret` is hardcoded.
  let ps = trav-pi t (pist-vc= 1 cv= "" vctx= [] tctx= [] rv= "__ret" ret= error "" cons= [])
  in return (mkfun x cs ps Many)
compile' x _ _  =
  return (error "compile' expected pattern-matching lambda")


macro
  compile : Term → Term → TC ⊤
  compile f a = do
     t ← derefT f
     v ← derefImmediate f
     let ctx = pi-to-ctx t
     let n = defName f
     --v ← pat-lam-norm v ctx
     let v = return v
     case v of λ where
       (ok v) → do
          v ← compile' v t n
          q ← quoteTC v
          unify a q
       e@(error s) →
          return e >>= quoteTC >>= unify a

---===== These are just all examples to play around ====---

tst-triv : ℕ → ℕ
tst-triv x = x + 1

-- Test pattern contraction
tst-ss : ℕ → ℕ
tst-ss (suc (suc x)) = x
tst-ss _ = 0

-- Here we have the (+ 0) in the last clause that
-- stays in the generated code.
tst-rew0 : ℕ → Bool → ℕ → ℕ
tst-rew0 x true y = let a = x * x in a + y
tst-rew0 x false y = x + 2 + 0

-- XXX can't do with clauses yet, but that shouldn
tst-with : ℕ → ℕ
tst-with x with x >? 0
tst-with x | yes p = 0
tst-with x | no ¬p = 1

-- Trivial test with Lists
lst-test : List ℕ → ℕ
lst-test [] = 0
lst-test (_∷_ x y) = x + 1

data Test : Set where
  cstctr : {x : ℕ} → x > 0 → Test

test-test : Test → ℕ
test-test (cstctr p) = 1

test-dot : (a : ℕ) → a > 0 → ℕ
test-dot a@(.(suc _)) (s≤s pf) = a

data Square : ℕ → Set where
  sq : (m : ℕ) → Square (m * m)


root : (m : ℕ) (n : ℕ) → Square n → ℕ
root a .(m * m) (sq m) =
  -- This is to show that square pattern is skipped
  -- from the context.  In the above case, the clause is
  -- represetned as: a , . , (sq m) ==ctx==> a , m
  -- and the expression is (var 0) + (var 1)
  m + a




open import Data.Vec hiding (concat)
tst-vec : ∀ {n} → Vec ℕ n → Vec ℕ (n + n * n) → ℕ
tst-vec [] _      = 0
tst-vec (x ∷ a) b = x

a = (reflect-ty tst-vec)


tst-undsc : _ → ℕ
tst-undsc n = 1 + n

vec-sum : ∀ {n} → Vec ℕ n → Vec ℕ (n) → Vec ℕ n
vec-sum [] _ = []
vec-sum (x ∷ a) (y ∷ b) = x + y ∷ vec-sum a b




vec-and-1 : ∀ {n} → Vec Bool n → Bool
vec-and-1 (x ∷ xs) = x ∧ vec-and-1 xs
vec-and-1 _ = true

vec-and : ∀ {n} → Vec Bool n → Vec Bool n → Vec Bool n
vec-and [] _ = []
vec-and (x ∷ a) (y ∷ b) = x ∧ y ∷ vec-and a b

vec-+ : ∀ {n} → Vec ℕ n → ℕ
vec-+ (x ∷ xs) = x + vec-+ xs
vec-+ _ = 0

f : ℕ → ℕ
f x = x * x

vec-tst : ∀ n → Vec ℕ (n) → ℕ
vec-tst 0 [] = 0
vec-tst (suc n) x = n * 2 -- (x ∷ xs) = n * 2

def-pst = (pist-vc= 1 cv= "" vctx= [] tctx= [] rv= "__ret" ret= error "" cons= []) --pist 1 [] [] (error "")

q : List String × List String × Prog
q = let (pist-vc= _ cv= _ vctx= v tctx= t rv= _ ret= r cons= _) = (trav-pi (reflect-ty vec-sum) def-pst) in (v , t , r)


--open import Data.Fin

xxx : Fin 5 → Fin 6
xxx zero = suc zero
xxx (suc _) = zero


fun-in-ty : (f : ℕ → ℕ) → Vec ℕ (f 3) → ℕ
fun-in-ty f x = 1 -- V.replicate 1

open import Array

data Ar' {a} (X : Set a) (d : ℕ) :  (Vec ℕ d) → Set a where
  imap : ∀ s → (Ix d s → X) → Ar' X d s

add-2v : ∀ {n} → let X = Ar ℕ 1 (n ∷ []) in X → X → X
add-2v (imap a) (imap b) = imap λ iv → a iv + b iv

postulate
  asum : ∀ {n} → Ar ℕ 1 (n ∷ []) → ℕ
  asum' : ∀ {n} → Ar' ℕ 1 (n ∷ []) → ℕ
  --sum (imap a)


mm : ∀ {m n k} → let Mat a b = Ar ℕ 2 (a ∷ b ∷ []) in
                 Mat m n → Mat n k → Mat m k
mm (imap a) (imap b) = imap λ iv → let i = ix-lookup iv (# 0)
                                       j = ix-lookup iv (# 1)
                                   in asum (imap λ kv → let k = ix-lookup kv (# 0)
                                                        in a (i ∷ k ∷ []) * b (k ∷ j ∷ []))


conv : ∀ {n} → let Ar1d n = Ar ℕ 1 V.[ n ] in
               Ar1d (3 + n) → Ar1d 3 → Ar1d (1 + n)
conv (imap inp) (imap ker) = imap λ iv → let i = ix-lookup iv (# 0)
                                         in (  inp (raise 2 i ∷ []) * ker (# 0 ∷ [])
                                             + inp (raise 1 (suc i) ∷ []) * ker (# 1 ∷ [])
                                             + inp (raise 0 (suc (suc i)) ∷ []) * ker (# 2 ∷ [])
                                            ) / 3
                                          where open import Data.Fin using (raise)
                                                open import Data.Nat.DivMod

test-fin : Fin 3 → Fin 4
test-fin x = suc x

w : String
w = case compile mm of λ where
     (error s) → s
     (ok l) → sjoin l ""

