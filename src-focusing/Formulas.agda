
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
  Atom : Atoms → Form +
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

-- Focusing proofs

mutual

  -- Focusing proof: either left focusing or right focusing

  data Foc (Γ : Cxt) (C : Form +) : Set where
    rFoc : (t : RFoc Γ C) → Foc Γ C
    lFoc : ∀{A} (x : Hyp A Γ) (t : LFoc Γ C A) → Foc Γ C
      -- lFoc is unproductive if A is an atom.
      -- This could be fixed by having a separated store of proven atoms,
      -- which can only be used in RFoc

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

  -- Left focusing (break a hypothesis A down, does not solve goal C)
  -- "neutral"

  data LFoc (Γ : Cxt) (C : Form +) : (A : Form -) → Set where
    -- Left focusing ends with new hypothesis
    swE : ∀{A} (t : LInv Γ C A) → LFoc Γ C (Sw +- A)
    -- Left focusing ends trivially (no progress)
    trueE : (t : Foc Γ C) → LFoc Γ C ⊤
    -- Choice
    andE₁ : ∀{B A} (t : LFoc Γ C A) → LFoc Γ C (A ∧ B)
    andE₂ : ∀{A B} (t : LFoc Γ C B) → LFoc Γ C (A ∧ B)
    impE  : ∀{A B} (u : RFoc Γ A) (t : LFoc Γ C B) → LFoc Γ C (A ⇒ B)

  -- Right inversion: break a goal into subgoals
  -- "eta"

  data RInv (Γ : Cxt) : (A : Form -) → Set where
    -- Right inversion ends at a positive formula
    swI : ∀{A} (t : Foc Γ A) → RInv Γ (Sw +- A)
    -- Goal splitting
    trueI : RInv Γ ⊤
    andI  : ∀{A B} (t : RInv Γ A) (u : RInv Γ B) → RInv Γ (A ∧ B)
    impI  : ∀{A B} (t : AddHyp Γ A (λ Γ' → RInv Γ' B)) → RInv Γ (A ⇒ B)

  -- Left inversion: add a hypothesis and continue in base state

  LInv : (Γ : Cxt) (C : Form +) (A : Form +) → Set
  LInv Γ C A = AddHyp Γ A (λ Γ' → Foc Γ' C)

  AddHyp = λ Γ A J → AddHyp' Γ J A

  -- Break up a positive formula and add the bits as hypotheses
  -- "case tree" / "cover"

  data AddHyp' (Γ : Cxt) (J : Cxt → Set) : (A : Form +) → Set where
    addAtom : ∀{P} (t : J (Γ ∙ Sw +- (Atom P))) → AddHyp' Γ J (Atom P)
    addNeg  : ∀{A} (t : J (Γ ∙ A)) → AddHyp' Γ J (Sw -+ A)
    trueE : (t : J Γ) → AddHyp' Γ J ⊤
    andE  : ∀{A B} (t : AddHyp Γ A (λ Γ' → AddHyp Γ' B J)) → AddHyp' Γ J (A ∧ B)
    orE   : ∀{A B} (t : AddHyp Γ A J) (u : AddHyp Γ B J) → AddHyp' Γ J (A ∨ B)


  -- data LInv (Γ : Cxt) (C : Form +) : (A : Form +) → Set where
