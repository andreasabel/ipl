{-# OPTIONS --rewriting #-}

open import Library

-- Focusing proofs

-- parametrized by positive and negative atoms
-- module Formulas (PosAt NegAt : Set) where

module Formulas (Atoms : Set) where

data Pol : Set where
  + - : Pol

-- Opposite polarities

data Op : (p q : Pol) → Set where
  +- : Op + -
  -+ : Op - +

-- Atoms : Pol → Set
-- Atoms + = PosAt
-- Atoms - = NegAt

data Form : Pol → Set where
  -- Atom : ∀{p} → Atoms p → Form p
  True : ∀{p} → Form p
  _∧_  : ∀{p} (A B : Form p) → Form p
  -- only positive
  Atom : (P : Atoms) → Form +
  False : Form +
  _∨_  : (A B : Form +) → Form +
  -- only negative
  _⇒_  : (A : Form +) (B : Form -) → Form -
  -- embedding (switching)
  Sw   : ∀{p q} (op : Op p q) (A : Form p) → Form q

infixl 8 _∧_
infixl 7 _∨_
infixr 6 _⇒_

-- Contexts only contain negative formulas

data Cxt : Set where
  ε : Cxt
  _∙_ : (Γ : Cxt) (A : Form -) → Cxt

infixl 4 _∙_

-- Hypotheses (negative)

data Hyp (A : Form -) :  (Γ : Cxt)→ Set where
  top : ∀{Γ} → Hyp A (Γ ∙ A)
  pop : ∀{B Γ} (x : Hyp A Γ) → Hyp A (Γ ∙ B)

-- Positive atoms in hypotheses

Atom- = λ P → Sw +- (Atom P)
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
    addNeg  : ∀{A} (t : J (Γ ∙ A)) → AddHyp' Γ J (Sw -+ A)
    trueE   : (t : J Γ) → AddHyp' Γ J True

    falseE  : AddHyp' Γ J False
    andE    : ∀{A B} (t : AddHyp Γ A (λ Γ' → AddHyp Γ' B J)) → AddHyp' Γ J (A ∧ B)
    orE     : ∀{A B} (t : AddHyp Γ A J) (u : AddHyp Γ B J) → AddHyp' Γ J (A ∨ B)

addHyp : ∀ (A : Form +) {Γ} {J : Cxt → Set} (j : ∀{Δ} → J Δ) → AddHyp' Γ J A
addHyp (Atom P)  j = addAtom j
addHyp (Sw -+ A) j = addNeg j
addHyp True      j = trueE j
addHyp False     j = falseE
addHyp (A ∧ B)   j = andE (addHyp A (addHyp B j))
addHyp (A ∨ B)   j = orE (addHyp A j) (addHyp B j)


module _ (Ne : (Γ : Cxt) (A : Form +) → Set) where

  data Cover' (Γ : Cxt) (J : Cxt → Set) : Set where
    returnC : (t : J Γ) → Cover' Γ J
    caseC   : ∀{A} (t : Ne Γ A) (c : AddHyp Γ A λ Γ' → Cover' Γ' J) → Cover' Γ J

-- Left focusing (break a negative hypothesis A down into something positive)
-- "spine"

mutual

  Ne = λ A Γ → Ne' RFoc Γ A
  Cover = Cover' λ Δ A → Ne (Sw +- A) Δ
  Foc = λ Γ C → Cover Γ λ Γ' → RFoc Γ' C

  -- LFoc' = λ Γ A C → LFoc Γ C A

  -- data LFoc (Γ : Cxt) (C : Form +) : (A : Form -) → Set where
  --   -- Left focusing ends with new hypothesis
  --   swE : ∀{A} → LFoc Γ A (Sw +- A)
  --   -- Choice
  --   andE₁ : ∀{B A} (t : LFoc Γ C A) → LFoc Γ C (A ∧ B)
  --   andE₂ : ∀{A B} (t : LFoc Γ C B) → LFoc Γ C (A ∧ B)
  --   impE  : ∀{A B} (u : RFoc Γ A) (t : LFoc Γ C B) → LFoc Γ C (A ⇒ B)


  -- Non-invertible right rules:

  -- Right focusing (proof of a positive goal by decisions)
  -- "normal"

  data RFoc (Γ : Cxt) : (A : Form +) → Set where
    -- Right focusing stops at a negative formulas
    sw    : ∀{A} (t : RInv Γ A) → RFoc Γ (Sw -+ A)
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
--     lFoc : ∀{A} (u : Ne' RFoc Γ (Sw +- A)) (t : AddHyp Γ A λ Γ' → Foc Γ' C) → Foc Γ C
-- --    lFoc : ∀{A B} (x : Hyp A Γ) (e : LFoc' Γ A B) (t : AddHyp Γ B λ Γ' → Foc Γ' C) → Foc Γ C
--       -- lFoc is unproductive if A is an atom.
--       -- This could be fixed by having a separated store of proven atoms,
--       -- which can only be used in RFoc

  -- Invertible right rules:

  -- Right inversion: break a goal into subgoals
  -- "eta"

  data RInv (Γ : Cxt) : (A : Form -) → Set where
    -- Right inversion ends at a positive formula
    sw  : ∀{A} (t : Foc Γ A) → RInv Γ (Sw +- A)
    -- Goal splitting
    trueI : RInv Γ True
    andI  : ∀{A B} (t : RInv Γ A) (u : RInv Γ B) → RInv Γ (A ∧ B)
    impI  : ∀{A B} (t : AddHyp Γ A (λ Γ' → RInv Γ' B)) → RInv Γ (A ⇒ B)



-- Context extension (thinning)

infix 3 _≤_

data _≤_ : (Γ Δ : Cxt) → Set where
  id≤ : ∀{Γ} → Γ ≤ Γ
  weak : ∀{A Γ Δ} (τ : Γ ≤ Δ) → Γ ∙ A ≤ Δ
  lift : ∀{A Γ Δ} (τ : Γ ≤ Δ) → Γ ∙ A ≤ Δ ∙ A

postulate lift-id≤ : ∀{Γ A} → lift id≤ ≡ id≤ {Γ ∙ A}
{-# REWRITE lift-id≤ #-}

-- Category of thinnings

_•_ : ∀{Γ Δ Φ} (τ : Γ ≤ Δ) (σ : Δ ≤ Φ) → Γ ≤ Φ
id≤ • σ = σ
weak τ • σ = weak (τ • σ)
lift τ • id≤ = lift τ
lift τ • weak σ = weak (τ • σ)
lift τ • lift σ = lift (τ • σ)

•-id : ∀{Γ Δ} (τ : Γ ≤ Δ) → τ • id≤ ≡ τ
•-id id≤ = refl
•-id (weak τ) = cong weak (•-id τ)
•-id (lift τ) = refl

{-# REWRITE •-id #-}

⟦_⟧ : ∀{p} (A : Form p) (Γ : Cxt) → Set
⟦ Atom P ⟧  Γ = HypAtom P Γ
⟦ False ⟧   Γ = ⊥
⟦ A ∨ B ⟧   Γ = ⟦ A ⟧ Γ ⊎ ⟦ B ⟧ Γ
⟦ True ⟧    Γ = ⊤
⟦ A ∧ B ⟧   Γ = ⟦ A ⟧ Γ × ⟦ B ⟧ Γ
⟦ A ⇒ B ⟧   Γ = ∀ {Δ} (τ : Δ ≤ Γ) → ⟦ A ⟧ Δ → ⟦ B ⟧ Δ

⟦ Sw +- A ⟧ Γ = Cover Γ ⟦ A ⟧
⟦ Sw -+ A ⟧ Γ = ⟦ A ⟧ Γ

-- ⟦_⟧ { - } (A ∧ B) Γ = ⟦ A ⟧ Γ × ⟦ B ⟧ Γ

Nf : ∀{p} (A : Form p) (Γ : Cxt) → Set
Nf { - } A Γ = RInv Γ A
Nf { + } A Γ = RFoc Γ A

trueNf : ∀{p Γ} → Nf (True {p}) Γ
trueNf { + } = trueI
trueNf { - } = trueI

-- NOT NEEDED:
pasteNf : ∀ {A : Form +} {Γ} → Cover Γ (Nf A) → Nf A Γ
pasteNf (returnC t) = t
pasteNf (caseC t c) = {!!}

mutual
  reify : ∀{p} (A : Form p) {Γ} → ⟦ A ⟧ Γ → Nf A Γ
  reify { + } True _ = trueI
  reify { - } True _ = trueI
  reify { + } (A ∧ B) (a , b) = andI (reify A a) (reify B b)
  reify { - } (A ∧ B) (a , b) = andI (reify A a) (reify B b)
  reify (Atom P) x = hyp x
  reify False ()
  reify (A ∨ B) (inj₁ a) = orI₁ (reify A a)
  reify (A ∨ B) (inj₂ b) = orI₂ (reify B b)
  reify (A ⇒ B) {Γ} f₀ = impI (reifyWithHyp A f₀)
    where
    reifyWithHyp : ∀ A {Γ} (f : ∀ {Δ} (τ : Δ ≤ Γ) → ⟦ A ⟧ Δ → ⟦ B ⟧ Δ) → AddHyp Γ A (Nf B)
    reifyWithHyp True f = trueE (reify B (f id≤ _))
    reifyWithHyp (A₁ ∧ A₂) f = andE {!reifyWithHyp A₁ !}  -- need CPS version
    reifyWithHyp (Atom P) f = addAtom (reify B (f (weak id≤) top))
    reifyWithHyp False f = falseE
    reifyWithHyp (A ∨ B) f = orE (reifyWithHyp A (λ τ a → f τ (inj₁ a)))
                                   (reifyWithHyp B (λ τ b → f τ (inj₂ b)))
    reifyWithHyp (Sw -+ A) f = addNeg (reify B (f (weak id≤) (reflect A (hyp top))))

  reify (Sw +- A) c = sw {!mapC (reify A) c!} -- {!sw (pasteNf {! reify A c!})!}
  reify (Sw -+ A) a = sw (reify A a)

  -- Since we only have negative hypotheses, we only need to reflect these

  reflect : ∀ (A : Form -) {Γ} → Ne A Γ → ⟦ A ⟧ Γ
  reflect True t = _
  reflect (A ∧ B) t = reflect A (andE₁ t) , reflect B (andE₂ t)
  reflect (A ⇒ B) t τ a = reflect B (impE {!!} (reify A a))  -- need monNe
  reflect (Sw +- A) t = caseC t {! reflectHyp A !}
    where
    reflectHyp : ∀ (A : Form +) {Γ : Cxt} → AddHyp Γ A λ Γ' → Cover Γ' ⟦ A ⟧
    reflectHyp True = trueE (returnC _)
    reflectHyp (A₁ ∧ A₂) = andE {!reflectHyp A₁!}  -- need CPS version of reflectHyp
    reflectHyp (Atom P) = addAtom (returnC top)
    reflectHyp False = falseE
    reflectHyp (A₁ ∨ A₂) = orE {!reflectHyp A₁!} {!!}  -- need monotonicity of AddHyp / Cover
    reflectHyp (Sw -+ A₁) = addNeg (returnC (reflect A₁ (hyp top)))
