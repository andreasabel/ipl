{-# OPTIONS --rewriting #-}

open import Library

-- Focusing proofs

-- parametrized by positive and negative atoms
-- module Formulas (PosAt NegAt : Set) where

-- module Formulas (Atoms : Set) where

postulate Atoms : Set

-- Polarity + (positive formulas) are those whose introduction requires

data Pol : Set where
  + - : Pol

-- -- Opposite polarities

-- data Op : (p q : Pol) → Set where
--   +- : Op + -
--   -+ : Op - +

-- Atoms : Pol → Set
-- Atoms + = PosAt
-- Atoms - = NegAt

data Form : Pol → Set where
  -- Atom : ∀{p} → Atoms p → Form p
  True : ∀{p} → Form p
  _∧_  : ∀{p} (A B : Form p) → Form p   -- +: tensor (strict tuple), -: record types (lazy tuple)
  -- only positive
  Atom : (P : Atoms) → Form +
  False : Form +
  _∨_  : (A B : Form +) → Form +
  -- only negative
  _⇒_  : (A : Form +) (B : Form -) → Form -
  -- embedding (switching)
  Comp  : (A : Form +) → Form -   -- The F of CBPV.
  Thunk : (A : Form -) → Form +   -- The U of CBPV.

  -- Sw   : ∀{p q} (op : Op p q) (A : Form p) → Form q

infixl 8 _∧_
infixl 7 _∨_
infixr 6 _⇒_

-- Generic hypotheses, taken from a set S.

module _ (S : Set) where

  data Cxt' : Set where
    ε : Cxt'
    _∙_ : (Γ : Cxt') (A : S) → Cxt'

  data Hyp' (A : S) : (Γ : Cxt') → Set where
    top : ∀{Γ} → Hyp' A (Γ ∙ A)
    pop : ∀{B Γ} (x : Hyp' A Γ) → Hyp' A (Γ ∙ B)

  infixl 4 _∙_

-- Contexts only contain negative formulas.
-- This is because we eagerly split positive ones.
-- In CBPV, hypotheses are positive (values).

Cxt = Cxt' (Form -)
Hyp = Hyp' (Form -)

-- Positive atoms in hypotheses via switching.
Atom- = λ P → Comp (Atom P)
HypAtom = λ P → Hyp (Atom- P)

-- Non-invertible left rules:

module _ (Nf : (Γ : Cxt) (A : Form +) → Set) where

  data Ne'  (Γ : Cxt) (A : Form -) : Set where
    hyp    : ∀    (x : Hyp A Γ) → Ne' Γ A
    impE   : ∀{B} (t : Ne' Γ (B ⇒ A)) (u : Nf Γ B) → Ne' Γ A
    andE₁  : ∀{B} (t : Ne' Γ (A ∧ B)) → Ne' Γ A
    andE₂  : ∀{B} (t : Ne' Γ (B ∧ A)) → Ne' Γ A

-- Invertible left rules:

-- Break up a positive formula and add the bits as hypotheses
-- "case tree" / "cover"

-- Produces a cover of Γ.A by splitting A

mutual

  AddHyp = λ Γ A J → AddHyp' Γ J A

  data AddHyp' (Γ : Cxt) (J : Cxt → Set) : (A : Form +) → Set where

    addAtom : ∀{P} (t : J (Γ ∙ Atom- P)) → AddHyp' Γ J (Atom P)
    addNeg  : ∀{A} (t : J (Γ ∙ A)) → AddHyp' Γ J (Thunk A)
    trueE   : (t : J Γ) → AddHyp' Γ J True

    falseE  : AddHyp' Γ J False
    andE    : ∀{A B} (t : AddHyp Γ A (λ Γ' → AddHyp Γ' B J)) → AddHyp' Γ J (A ∧ B)
    orE     : ∀{A B} (t : AddHyp Γ A J) (u : AddHyp Γ B J) → AddHyp' Γ J (A ∨ B)

addHyp : ∀ (A : Form +) {Γ} {J : Cxt → Set} (j : ∀{Δ} → J Δ) → AddHyp' Γ J A
addHyp (Atom P)  j = addAtom j
addHyp (Thunk A) j = addNeg j
addHyp True      j = trueE j
addHyp False     j = falseE
addHyp (A ∧ B)   j = andE (addHyp A (addHyp B j))
addHyp (A ∨ B)   j = orE (addHyp A j) (addHyp B j)


module _ (Ne : (Γ : Cxt) (A : Form +) → Set) where

  data Cover' (J : Cxt → Set) (Γ : Cxt) : Set where
    returnC : (t : J Γ) → Cover' J Γ
    caseC   : ∀{A} (t : Ne Γ A) (c : AddHyp Γ A (Cover' J)) → Cover' J Γ

-- Left focusing (break a negative hypothesis A down into something positive)
-- "spine"

mutual

  Ne = λ A Γ → Ne' RFoc Γ A
  Cover = Cover' λ Δ A → Ne (Comp A) Δ
  Foc = λ Γ C → Cover (flip RFoc C) Γ

  -- LFoc' = λ Γ A C → LFoc Γ C A

  -- data LFoc (Γ : Cxt) (C : Form +) : (A : Form -) → Set where
  --   -- Left focusing ends with new hypothesis
  --   swE : ∀{A} → LFoc Γ A (Comp A)
  --   -- Choice
  --   andE₁ : ∀{B A} (t : LFoc Γ C A) → LFoc Γ C (A ∧ B)
  --   andE₂ : ∀{A B} (t : LFoc Γ C B) → LFoc Γ C (A ∧ B)
  --   impE  : ∀{A B} (u : RFoc Γ A) (t : LFoc Γ C B) → LFoc Γ C (A ⇒ B)


  -- Non-invertible right rules:

  -- Right focusing (proof of a positive goal by decisions)
  -- "normal"

  data RFoc (Γ : Cxt) : (A : Form +) → Set where
    -- Right focusing stops at a negative formulas
    sw    : ∀{A} (t : RInv Γ A) → RFoc Γ (Thunk A)
    -- Success:
    hyp  : ∀{P} (x : HypAtom P Γ) → RFoc Γ (Atom P)
    trueI : RFoc Γ True
    -- Choices:
    andI  : ∀{A B} (t : RFoc Γ A) (u : RFoc Γ B) → RFoc Γ (A ∧ B)
    orI₁  : ∀{B A} (t : RFoc Γ A) → RFoc Γ (A ∨ B)
    orI₂  : ∀{A B} (u : RFoc Γ B) → RFoc Γ (A ∨ B)

  -- Focusing proof: after possibly some rounds of left focusing
  -- eventually right focusing

--   data Foc (Γ : Cxt) (C : Form +) : Set where
--     rFoc : (t : RFoc Γ C) → Foc Γ C
--     lFoc : ∀{A} (u : Ne' RFoc Γ (Comp A)) (t : AddHyp Γ A λ Γ' → Foc Γ' C) → Foc Γ C
-- --    lFoc : ∀{A B} (x : Hyp A Γ) (e : LFoc' Γ A B) (t : AddHyp Γ B λ Γ' → Foc Γ' C) → Foc Γ C
--       -- lFoc is unproductive if A is an atom.
--       -- This could be fixed by having a separated store of proven atoms,
--       -- which can only be used in RFoc

  -- Invertible right rules:

  -- Right inversion: break a goal into subgoals
  -- "eta"

  data RInv (Γ : Cxt) : (A : Form -) → Set where
    -- Right inversion ends at a positive formula
    sw  : ∀{A} (t : Foc Γ A) → RInv Γ (Comp A)
    -- Goal splitting
    trueI : RInv Γ True
    andI  : ∀{A B} (t : RInv Γ A) (u : RInv Γ B) → RInv Γ (A ∧ B)
    impI  : ∀{A B} (t : AddHyp Γ A (λ Γ' → RInv Γ' B)) → RInv Γ (A ⇒ B)


-- Pointwise mapping

_→̇_ : (P Q : Cxt → Set) → Set
P →̇ Q = ∀{Γ} → P Γ → Q Γ

mapAddHyp : ∀{P Q} (f : P →̇ Q) → ∀{A Γ} → AddHyp Γ A P → AddHyp Γ A Q
mapAddHyp f (addAtom t) = addAtom (f t)
mapAddHyp f (addNeg t)  = addNeg (f t)
mapAddHyp f (trueE t)   = trueE (f t)
mapAddHyp f falseE      = falseE
mapAddHyp f (andE t)    = andE (mapAddHyp (mapAddHyp f) t) -- By induction on types!
mapAddHyp f (orE t u)   = orE (mapAddHyp f t) (mapAddHyp f u)

{-# TERMINATING #-}
mapCover :  ∀{P Q} (f : P →̇ Q) → Cover P →̇ Cover Q
mapCover f (returnC t) = returnC (f t)
mapCover f (caseC t c) = caseC t (mapAddHyp (mapCover f) c)  -- Cover should be sized!

-- Cover monad

{-# TERMINATING #-}
joinCover : ∀{P} → Cover (Cover P) →̇ Cover P
joinCover (returnC t) = t
joinCover (caseC t c) = caseC t (mapAddHyp joinCover c)

-- Context extension (thinning)

infix 3 _≤_

data _≤_ : (Γ Δ : Cxt) → Set where
  id≤  : ∀{Γ} → Γ ≤ Γ
  weak : ∀{A Γ Δ} (τ : Γ ≤ Δ) → Γ ∙ A ≤ Δ
  lift : ∀{A Γ Δ} (τ : Γ ≤ Δ) → Γ ∙ A ≤ Δ ∙ A

postulate lift-id≤ : ∀{Γ A} → lift id≤ ≡ id≤ {Γ ∙ A}
{-# REWRITE lift-id≤ #-}

-- Category of thinnings

_•_ : ∀{Γ Δ Φ} (τ : Γ ≤ Δ) (σ : Δ ≤ Φ) → Γ ≤ Φ
id≤    • σ      = σ
weak τ • σ      = weak (τ • σ)
lift τ • id≤    = lift τ
lift τ • weak σ = weak (τ • σ)
lift τ • lift σ = lift (τ • σ)

•-id : ∀{Γ Δ} (τ : Γ ≤ Δ) → τ • id≤ ≡ τ
•-id id≤      = refl
•-id (weak τ) = cong weak (•-id τ)
•-id (lift τ) = refl

{-# REWRITE •-id #-}

-- Monotonicity

Mon : (P : Cxt → Set) → Set
Mon P = ∀{Γ Δ} (τ : Γ ≤ Δ) → P Δ → P Γ

-- Monotonicity of hypotheses

monH : ∀{A} → Mon (Hyp A)
monH id≤      x       = x
monH (weak τ) x       = pop (monH τ x)
monH (lift τ) top     = top
monH (lift τ) (pop x) = pop (monH τ x)

monH• : ∀{Γ Δ Φ A} (τ : Γ ≤ Δ) (σ : Δ ≤ Φ) (x : Hyp A Φ) → monH (τ • σ) x ≡ monH τ (monH σ x)
monH• id≤      σ        x       = refl
monH• (weak τ) σ        x       = cong pop (monH• τ σ x)
monH• (lift τ) id≤      x       = refl
monH• (lift τ) (weak σ) x       = cong pop (monH• τ σ x)
monH• (lift τ) (lift σ) top     = refl
monH• (lift τ) (lift σ) (pop x) = cong pop (monH• τ σ x)

{-# REWRITE monH• #-}

-- Monotonicity of neutrals

monNe' : ∀{P : Form + → Cxt → Set}
  (monP : ∀{A} → Mon (P A)) →
  ∀{A} → Mon (flip (Ne' (flip P)) A)
monNe' monP τ (hyp x)    = hyp (monH τ x)
monNe' monP τ (impE t u) = impE (monNe' monP τ t) (monP τ u)
monNe' monP τ (andE₁ t)  = andE₁ (monNe' monP τ t)
monNe' monP τ (andE₂ t)  = andE₂ (monNe' monP τ t)

-- Monotonicity of covers

monAddHyp : ∀{P} (monP : Mon P) → ∀{A} → Mon (λ Γ → AddHyp Γ A P)
monAddHyp monP τ (addAtom t) = addAtom (monP (lift τ) t)
monAddHyp monP τ (addNeg t)  = addNeg (monP (lift τ) t)
monAddHyp monP τ (trueE t)   = trueE (monP τ t)
monAddHyp monP τ falseE      = falseE
monAddHyp monP τ (andE t)    = andE (monAddHyp (monAddHyp monP) τ t)
monAddHyp monP τ (orE t u)   = orE (monAddHyp monP τ t) (monAddHyp monP τ u)

-- Monotonicity of derivations

mutual
  monNe : ∀{A} → Mon (Ne A)
  monNe = monNe' monRFoc

  {-# TERMINATING #-}
  monCover : ∀{P} (monP : Mon P) → Mon (Cover P)
  monCover monP τ (returnC t) = returnC (monP τ t)
  monCover monP τ (caseC t c) = caseC (monNe τ t) (monAddHyp (monCover monP) τ c)

  monRFoc : ∀{A} → Mon (flip RFoc A)
  monRFoc τ (sw t)      = sw (monRInv τ t)
  monRFoc τ (hyp x)     = hyp (monH τ x)
  monRFoc τ trueI       = trueI
  monRFoc τ (andI t t₁) = andI (monRFoc τ t) (monRFoc τ t₁)
  monRFoc τ (orI₁ t)    = orI₁ (monRFoc τ t)
  monRFoc τ (orI₂ t)    = orI₂ (monRFoc τ t)

  monRInv : ∀{A} → Mon (flip RInv A)
  monRInv τ (sw t)      = sw (monCover monRFoc τ t)
  monRInv τ trueI       = trueI
  monRInv τ (andI t t₁) = andI (monRInv τ t) (monRInv τ t₁)
  monRInv τ (impI t)    = impI (monAddHyp monRInv τ t)

KFun : (P Q : Cxt → Set) (Γ : Cxt) → Set
KFun P Q Γ = ∀{Δ} (τ : Δ ≤ Γ) → P Δ → Q Δ

mapAddHyp' : ∀{P Q Γ} (f : KFun P Q Γ) → ∀{A} → AddHyp Γ A P → AddHyp Γ A Q
mapAddHyp' f (addAtom t) = addAtom (f (weak id≤) t)
mapAddHyp' f (addNeg t)  = addNeg (f (weak id≤) t)
mapAddHyp' f (trueE t)   = trueE (f id≤ t)
mapAddHyp' f falseE      = falseE
mapAddHyp' f (andE t)    = andE (mapAddHyp' (λ τ → mapAddHyp' λ τ' → f (τ' • τ)) t) -- By induction on types!
mapAddHyp' f (orE t u)   = orE (mapAddHyp' f t) (mapAddHyp' f u)

{-# TERMINATING #-}
mapCover' :  ∀{P Q Γ} (f : KFun P Q Γ) (c : Cover P Γ) → Cover Q Γ
mapCover' f (returnC t) = returnC (f id≤ t)
mapCover' f (caseC t c) = caseC t (mapAddHyp' (λ τ → mapCover' λ τ' → f (τ' • τ)) c)  -- Cover should be sized!

-- Semantics

⟦_⟧ : ∀{p} (A : Form p) (Γ : Cxt) → Set
⟦ Atom P ⟧  Γ = HypAtom P Γ
⟦ False ⟧   Γ = ⊥
⟦ A ∨ B ⟧   Γ = ⟦ A ⟧ Γ ⊎ ⟦ B ⟧ Γ
⟦ True ⟧    Γ = ⊤
⟦ A ∧ B ⟧   Γ = ⟦ A ⟧ Γ × ⟦ B ⟧ Γ
⟦ A ⇒ B ⟧   Γ = ∀ {Δ} (τ : Δ ≤ Γ) (a : ⟦ A ⟧ Δ) → ⟦ B ⟧ Δ

⟦ Comp A ⟧ = Cover ⟦ A ⟧  -- values to computations
⟦ Thunk A ⟧ = ⟦ A ⟧

-- Monotonicity of semantics

mon⟦_⟧ : ∀{p} (A : Form p) → Mon ⟦ A ⟧
mon⟦ True    ⟧ τ _       = _
mon⟦ A ∧ B   ⟧ τ (a , b) = mon⟦ A ⟧ τ a , mon⟦ B ⟧ τ b
mon⟦ Atom P  ⟧           = monH
mon⟦ False   ⟧ τ ()
mon⟦ A ∨ B   ⟧ τ         = map-⊎ (mon⟦ A ⟧ τ) (mon⟦ B ⟧ τ)
mon⟦ A ⇒ B   ⟧ τ f δ     = f (δ • τ)
mon⟦ Comp A ⟧           = monCover mon⟦ A ⟧
mon⟦ Thunk A ⟧           = mon⟦ A ⟧

-- Reflection and reification.

mutual

  reify- : ∀ (A : Form -) {Γ} → ⟦ A ⟧ Γ → RInv Γ A
  reify- True _ = trueI
  reify- (A ∧ B) (a , b) = andI (reify- A a) (reify- B b)
  reify- (A ⇒ B) f = impI (reflectHyp A λ τ a → reify- B (f τ a))
  reify- (Comp A) c = sw (mapCover (reify+ A) c)

  reify+ : ∀ (A : Form +) {Γ} → ⟦ A ⟧ Γ → RFoc Γ A
  reify+ True _ = trueI
  reify+ (A ∧ B) (a , b) = andI (reify+ A a) (reify+ B b)
  reify+ (Atom P) x = hyp x
  reify+ False ()
  reify+ (A ∨ B) (inj₁ a) = orI₁ (reify+ A a)
  reify+ (A ∨ B) (inj₂ b) = orI₂ (reify+ B b)
  reify+ (Thunk A) a = sw (reify- A a)

  reflectHyp : ∀ A {Γ} {J} (k : ∀ {Δ} (τ : Δ ≤ Γ) → ⟦ A ⟧ Δ → J Δ) → AddHyp Γ A J
  reflectHyp True      k = trueE (k id≤ _)
  reflectHyp (A ∧ B)   k = andE (reflectHyp A λ τ a →
                                 reflectHyp B λ τ' b → k (τ' • τ) (mon⟦ A ⟧ τ' a , b))  -- need monT
  reflectHyp (Atom P)  k = addAtom (k (weak id≤) top)
  reflectHyp False     k = falseE
  reflectHyp (A ∨ B)   k = orE (reflectHyp A (λ τ a → k τ (inj₁ a)))
                               (reflectHyp B (λ τ b → k τ (inj₂ b)))
  reflectHyp (Thunk A) k = addNeg (k (weak id≤) (reflect A (hyp top)))

  -- Since we only have negative hypotheses, we only need to reflect these

  reflect : ∀ (A : Form -) → Ne A →̇ ⟦ A ⟧
  reflect True t = _
  reflect (A ∧ B) t = reflect A (andE₁ t) , reflect B (andE₂ t)
  reflect (A ⇒ B) t τ a = reflect B (impE (monNe τ t) (reify+ A a))  -- need monNe
  reflect (Comp A) t = caseC t (reflectHyp A λ τ a → returnC a)

-- Negative propositions are comonadic

paste : ∀ (A : Form -) → Cover ⟦ A ⟧ →̇ ⟦ A ⟧
paste True    _     = _
paste (A ∧ B) c     = paste A (mapCover proj₁ c) , paste B (mapCover proj₂ c)
paste (A ⇒ B) c τ a = paste B (mapCover' (λ τ' f → f id≤ (mon⟦ A ⟧ τ' a)) (monCover mon⟦ A ⇒ B ⟧ τ c))
paste (Comp A)      = joinCover

-- Intuitionistic propositional logic

data IPL : Set where
  Atom        : (P : Atoms) → IPL
  True False  : IPL
  _∨_ _∧_ _⇒_ : (A B : IPL) → IPL

mutual

  _⁺ : IPL → Form +
  Atom P ⁺  = Atom P
  True ⁺    = True
  False ⁺   = False
  (A ∨ B) ⁺ = A ⁺ ∨ B ⁺
  (A ∧ B) ⁺ = A ⁺ ∧ B ⁺
  (A ⇒ B) ⁺ = Thunk (A ⁺ ⇒ B ⁻)

  _⁻ : IPL → Form -
  Atom P ⁻  = Atom- P
  True ⁻    = True
  False ⁻   = Comp False
  (A ∨ B) ⁻ = Comp (A ⁺ ∨ B ⁺)
  (A ∧ B) ⁻ = A ⁻ ∧ B ⁻
  (A ⇒ B) ⁻ = A ⁺ ⇒ B ⁻

-- Derivations

infix 2 _⊢_

data _⊢_ (Γ : Cxt' IPL) : (A : IPL) → Set where
  hyp    : ∀{A} (x : Hyp' IPL A Γ) → Γ ⊢ A
  impI   : ∀{A B} (t : Γ ∙ A ⊢ B) → Γ ⊢ A ⇒ B
  impE   : ∀{A B} (t : Γ ⊢ A ⇒ B) (u : Γ ⊢ A) → Γ ⊢ B
  andI   : ∀{A B} (t : Γ ⊢ A) (u : Γ ⊢ B) → Γ ⊢ A ∧ B
  andE₁  : ∀{A B} (t : Γ ⊢ A ∧ B) → Γ ⊢ A
  andE₂  : ∀{A B} (t : Γ ⊢ A ∧ B) → Γ ⊢ B
  orI₁   : ∀{A B} (t : Γ ⊢ A) → Γ ⊢ A ∨ B
  orI₂   : ∀{A B} (t : Γ ⊢ B) → Γ ⊢ A ∨ B
  orE    : ∀{A B C} (t : Γ ⊢ A ∨ B) (u : Γ ∙ A ⊢ C) (v : Γ ∙ B ⊢ C) → Γ ⊢ C
  falseE : ∀{C} (t : Γ ⊢ False) → Γ ⊢ C
  trueI  : Γ ⊢ True

Tm = λ A Γ → Γ ⊢ A

-- Call-by value evaluation

module CBV where

  V⟦_⟧ = λ A → ⟦ A ⁺ ⟧
  C⟦_⟧ = λ A → ⟦ A ⁻ ⟧

  return : ∀ A → V⟦ A ⟧ →̇ C⟦ A ⟧
  return (Atom P) v = returnC v
  return True v = v
  return False v = returnC v
  return (A ∨ B) v = returnC v
  return (A ∧ B) (a , b) = return A a , return B b
  return (A ⇒ B) v = v

  run : ∀ A → C⟦ A ⟧ →̇ Cover V⟦ A ⟧
  run (Atom P) c = c
  run True c = returnC c
  run False c = c
  run (A ∨ B) c = c
  run (A ∧ B) c = joinCover (mapCover' (λ τ a → mapCover' (λ τ' b → (mon⟦ A ⁺ ⟧ τ' a , b)) (run B (mon⟦ B ⁻ ⟧ τ (proj₂ c)))) (run A (proj₁ c)))
  run (A ⇒ B) c = returnC c

  -- Fundamental theorem
  -- Extension of ⟦_⟧ to contexts

  G⟦_⟧ : ∀ (Γ : Cxt' IPL) (Δ : Cxt) → Set
  G⟦ ε     ⟧ Δ = ⊤
  G⟦ Γ ∙ A ⟧ Δ = G⟦ Γ ⟧ Δ × V⟦ A ⟧ Δ

  -- monG : ∀{Γ Δ Φ} (τ : Φ ≤ Δ) → G⟦ Γ ⟧ Δ → G⟦ Γ ⟧ Φ

  monG : ∀{Γ} → Mon G⟦ Γ ⟧
  monG {ε} τ _ = _
  monG {Γ ∙ A} τ (γ , a) = monG τ γ , mon⟦ A ⁺ ⟧ τ a

  -- Variable case.

  lookup : ∀{Γ A} (x : Hyp' IPL A Γ) → G⟦ Γ ⟧ →̇ V⟦ A ⟧
  lookup top     = proj₂
  lookup (pop x) = lookup x ∘ proj₁

  impIntro : ∀ {A B Γ} (f : KFun (Cover ⟦ A ⟧) ⟦ B ⟧ Γ) → ⟦ A ⇒ B ⟧ Γ
  impIntro f τ a = f τ (returnC a)

  -- impElim : ∀ A B {Γ} → (f : C⟦ A ⇒ B ⟧ Γ) (a : C⟦ A ⟧ Γ) → C⟦ B ⟧ Γ
  -- impElim (Atom P) B f = paste (B ⁻) ∘ mapCover' f
  -- impElim False B f = paste (B ⁻) ∘ mapCover' f
  -- impElim True B f = f id≤
  -- impElim (A ∨ A₁) B f = paste (B ⁻) ∘ mapCover' f
  -- impElim (A ∧ A₁) B f = {!paste (B ⁻) ∘ mapCover' f!}
  -- impElim (A ⇒ A₁) B f = f id≤

  impElim : ∀ A B {Γ} → (f : C⟦ A ⇒ B ⟧ Γ) (a : C⟦ A ⟧ Γ) → C⟦ B ⟧ Γ
  impElim A B f a = paste (B ⁻) (mapCover' f (run A a))

  -- A lemma for the orE case.

  orElim : ∀ A B C {Γ} → C⟦ A ∨ B ⟧ Γ → C⟦ A ⇒ C ⟧ Γ → C⟦ B ⇒ C ⟧ Γ → C⟦ C ⟧ Γ
  orElim A B C c g h = paste (C ⁻) (mapCover' (λ τ → [ g τ , h τ ]) c)

  -- A lemma for the falseE case.

  -- Casts an empty cover into any semantic value (by contradiction).

  falseElim : ∀ C → C⟦ False ⟧ →̇ C⟦ C ⟧
  falseElim C = paste (C ⁻) ∘ mapCover ⊥-elim

  -- The fundamental theorem
  eval :  ∀{A Γ} (t : Γ ⊢ A) → G⟦ Γ ⟧ →̇ C⟦ A ⟧
  eval {A} (hyp x)           = return A ∘ lookup x
  eval (impI t)    γ τ a     = eval t (monG τ γ , a)
  eval (impE {A} {B} t u)  γ = impElim A B (eval t γ) (eval u γ)
  eval (andI t u)  γ         = eval t γ , eval u γ
  eval (andE₁ t)             = proj₁ ∘ eval t
  eval (andE₂ t)             = proj₂ ∘ eval t
  eval (orI₁ {A} {B} t) γ    = mapCover inj₁ (run A (eval t γ))
  eval (orI₂ {A} {B} t) γ    = mapCover inj₂ (run B (eval t γ))
  eval (orE {A} {B} {C} t u v) γ = orElim A B C (eval t γ)
    (λ τ a → eval u (monG τ γ , a))
    (λ τ b → eval v (monG τ γ , b))
  eval {C} (falseE t) γ      = falseElim C (eval t γ)
  eval trueI       γ         = _

  _⁺⁺ : (Γ : Cxt' IPL) → Cxt
  ε ⁺⁺ = ε
  (Γ ∙ A) ⁺⁺ = Γ ⁺⁺ ∙ A ⁻

  -- Identity environment

  ide : ∀ Γ → Cover G⟦ Γ ⟧ (Γ ⁺⁺)
  ide ε = returnC _
  ide (Γ ∙ A) = {!!}
    -- monG (weak id≤) (ide Γ) , {! reflectHyp (A ⁺) (λ τ a → a) !}
{-
  -- Normalization

  norm : ∀{A : IPL} {Γ : Cxt' IPL} → Tm A Γ → RInv (Γ ⁺⁺) (A ⁻)
  norm t = reify- _ (eval t (ide _))


-- -}
-- -}
-- -}
