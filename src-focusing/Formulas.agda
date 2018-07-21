
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
  ⊤    : ∀{p} → Form p
  _∧_  : ∀{p} (A B : Form p) → Form p
  -- only positive
  Atom : (P : Atoms) → Form +
  ⊥    : Form +
  _∨_  : (A B : Form +) → Form +
  -- only negative
  _⇒_  : (A : Form +) (B : Form -) → Form -
  -- embedding (switching)
  Sw   : ∀{p q} (op : Op p q) (A : Form p) → Form q

-- Contexts only contain negative formulas

data Cxt : Set where
  ε : Cxt
  _∙_ : (Γ : Cxt) (A : Form -) → Cxt

data Hyp (A : Form -) :  (Γ : Cxt)→ Set where
  top : ∀{Γ} → Hyp A (Γ ∙ A)
  pop : ∀{B Γ} (x : Hyp A Γ) → Hyp A (Γ ∙ B)


-- Break up a positive formula and add the bits as hypotheses
-- "case tree" / "cover"

-- Produces a cover of Γ.A

mutual

  AddHyp = λ Γ A J → AddHyp' Γ J A

  data AddHyp' (Γ : Cxt) (J : Cxt → Set) : (A : Form +) → Set where
    addAtom : ∀{P} (t : J (Γ ∙ Sw +- (Atom P))) → AddHyp' Γ J (Atom P)
    addNeg  : ∀{A} (t : J (Γ ∙ A)) → AddHyp' Γ J (Sw -+ A)
    trueE   : (t : J Γ) → AddHyp' Γ J ⊤
    andE    : ∀{A B} (t : AddHyp Γ A (λ Γ' → AddHyp Γ' B J)) → AddHyp' Γ J (A ∧ B)
    orE     : ∀{A B} (t : AddHyp Γ A J) (u : AddHyp Γ B J) → AddHyp' Γ J (A ∨ B)
    falseE  : AddHyp' Γ J ⊥

addHyp : ∀ (A : Form +) {Γ} {J : Cxt → Set} (j : ∀{Δ} → J Δ) → AddHyp' Γ J A
addHyp ⊤         j = trueE j
addHyp (A ∧ B)   j = andE (addHyp A (addHyp B j))
addHyp (Atom P)  j = addAtom j
addHyp ⊥         j = falseE
addHyp (A ∨ B)   j = orE (addHyp A j) (addHyp B j)
addHyp (Sw -+ A) j = addNeg j


-- Left focusing (break a hypothesis A down and add it)
-- "neutral"

mutual

  LFoc' = λ Γ A J → LFoc Γ J A

  data LFoc (Γ : Cxt) (J : Cxt → Set) : (A : Form -) → Set where
    -- Left focusing ends with new hypothesis
    swE : ∀{A} (t : AddHyp' Γ J A) → LFoc Γ J (Sw +- A)
    -- Left focusing ends trivially (no progress)
    trueE : (t : J Γ) → LFoc Γ J ⊤
    -- Jhoice
    andE₁ : ∀{B A} (t : LFoc Γ J A) → LFoc Γ J (A ∧ B)
    andE₂ : ∀{A B} (t : LFoc Γ J B) → LFoc Γ J (A ∧ B)
    impE  : ∀{A B} (u : RFoc Γ A) (t : LFoc Γ J B) → LFoc Γ J (A ⇒ B)


  -- Right focusing (proof of a positive goal by decisions)
  -- "normal"

  data RFoc (Γ : Cxt) : (A : Form +) → Set where
    -- Right focusing stops at a negative formulas
    swI   : ∀{A} (t : RInv Γ A) → RFoc Γ (Sw -+ A)
    -- Success:
    hyp  : ∀{P} (x : Hyp (Sw +- (Atom P)) Γ) → RFoc Γ (Atom P)
    trueI : RFoc Γ ⊤
    -- Choices:
    andI  : ∀{A B} (t : RFoc Γ A) (u : RFoc Γ B) → RFoc Γ (A ∧ B)
    orI₁  : ∀{B A} (t : RFoc Γ A) → RFoc Γ (A ∨ B)
    orI₂  : ∀{A B} (u : RFoc Γ B) → RFoc Γ (A ∨ B)

  -- Focusing proof: after possibly some rounds of left focusing
  -- eventually right focusing

  data Foc (Γ : Cxt) (C : Form +) : Set where
    rFoc : (t : RFoc Γ C) → Foc Γ C
    lFoc : ∀{A} (x : Hyp A Γ) (t : LFoc' Γ A λ Γ' → Foc Γ' C) → Foc Γ C
      -- lFoc is unproductive if A is an atom.
      -- This could be fixed by having a separated store of proven atoms,
      -- which can only be used in RFoc

  -- Right inversion: break a goal into subgoals
  -- "eta"

  data RInv (Γ : Cxt) : (A : Form -) → Set where
    -- Right inversion ends at a positive formula
    swI : ∀{A} (t : Foc Γ A) → RInv Γ (Sw +- A)
    -- Goal splitting
    trueI : RInv Γ ⊤
    andI  : ∀{A B} (t : RInv Γ A) (u : RInv Γ B) → RInv Γ (A ∧ B)
    impI  : ∀{A B} (t : AddHyp Γ A (λ Γ' → RInv Γ' B)) → RInv Γ (A ⇒ B)
