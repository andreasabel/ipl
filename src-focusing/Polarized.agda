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
Atom-   = λ P → Comp (Atom P)
HypAtom = λ P → Hyp (Atom- P)

-- Non-invertible left rules:

module _ (Nf : (A : Form +) (Γ : Cxt) → Set) where

  data Ne' (C : Form -) (Γ : Cxt) : Set where
    hyp    : ∀    (x : Hyp C Γ) → Ne' C Γ
    impE   : ∀{A} (t : Ne' (A ⇒ C) Γ) (u : Nf A Γ) → Ne' C Γ
    andE₁  : ∀{D} (t : Ne' (C ∧ D) Γ) → Ne' C Γ
    andE₂  : ∀{D} (t : Ne' (D ∧ C) Γ) → Ne' C Γ

-- Invertible left rules:

-- Break up a positive formula and add the bits as hypotheses
-- "case tree" / "cover"

-- Produces a cover of Γ.A by splitting A

mutual

  AddHyp = λ A J Γ → AddHyp' Γ J A

  data AddHyp' (Γ : Cxt) (J : Cxt → Set) : (A : Form +) → Set where

    addAtom : ∀{P} (t : J (Γ ∙ Atom- P)) → AddHyp (Atom P)  J Γ
    addNeg  : ∀{A} (t : J (Γ ∙ A))       → AddHyp (Thunk A) J Γ

    trueE   :        (t : J Γ)                     → AddHyp True    J Γ
    andE    : ∀{A B} (t : AddHyp A (AddHyp B J) Γ) → AddHyp (A ∧ B) J Γ

    falseE  :                                                AddHyp False   J Γ
    orE     : ∀{A B} (t : AddHyp A J Γ) (u : AddHyp B J Γ) → AddHyp (A ∨ B) J Γ


module _ (Ne : (A : Form +) (Γ : Cxt) → Set) where

  data Cover' (i : Size) (J : Cxt → Set) (Γ : Cxt) : Set where
    returnC : (t : J Γ) → Cover' i J Γ
    matchC   : ∀{j : Size< i} {A} (t : Ne A Γ) (c : AddHyp A (Cover' j J) Γ) → Cover' i J Γ

-- Left focusing (break a negative hypothesis A down into something positive)
-- "spine"

mutual

  -- Neutrals, containing values (RFoc) as arguments to functions.

  Ne : (i : Size) (C : Form -) (Γ : Cxt) → Set
  Ne  i = Ne' (RFoc i)

  -- Cover monad, containing neutrals of type (Comp A) as scrutinees.

  Cover : (i j : Size) (J : Cxt → Set) (Γ : Cxt) → Set
  Cover i j = Cover' (λ A → Ne j (Comp A)) i

  -- Non-invertible right rules:

  -- Right focusing (proof of a positive goal by decisions)
  -- "normal" / values.

  data RFoc : (i : Size) (A : Form +) (Γ : Cxt) → Set where
    -- Right focusing stops at a negative formulas
    thunk : ∀{i Γ A} (t : RInv i A Γ) → RFoc (↑ i) (Thunk A) Γ
    -- Success:
    hyp   : ∀{i Γ P} (x : HypAtom P Γ) → RFoc (↑ i) (Atom P) Γ
    trueI : ∀{i Γ} → RFoc (↑ i) True Γ
    -- Choices:
    andI  : ∀{i Γ A B} (t : RFoc i A Γ) (u : RFoc i B Γ) → RFoc (↑ i) (A ∧ B) Γ
    orI₁  : ∀{i Γ B A} (t : RFoc i A Γ) → RFoc (↑ i) (A ∨ B) Γ
    orI₂  : ∀{i Γ A B} (u : RFoc i B Γ) → RFoc (↑ i) (A ∨ B) Γ

  -- Invertible right rules:

  -- Right inversion: break a goal into subgoals
  -- "eta" / definitions by copattern matching.

  data RInv : (i : Size) (A : Form -) (Γ : Cxt) → Set where
    -- Right inversion ends at a positive formula
    ret  : ∀{i Γ A} (t : Cover ∞ i (RFoc i A) Γ) → RInv (↑ i) (Comp A) Γ
    -- Goal splitting
    trueI : ∀{i Γ} → RInv (↑ i) True Γ
    andI  : ∀{i Γ A B} (t : RInv i A Γ) (u : RInv i B Γ) → RInv (↑ i) (A ∧ B) Γ
    impI  : ∀{i Γ A B} (t : AddHyp A (RInv i B) Γ) → RInv (↑ i) (A ⇒ B) Γ


-- Pointwise mapping

_→̇_ : (P Q : Cxt → Set) → Set
P →̇ Q = ∀{Γ} → P Γ → Q Γ

mapAddHyp : ∀{P Q} (f : P →̇ Q) → ∀{A} → AddHyp A P →̇ AddHyp A Q
mapAddHyp f (addAtom t) = addAtom (f t)
mapAddHyp f (addNeg t)  = addNeg (f t)
mapAddHyp f (trueE t)   = trueE (f t)
mapAddHyp f falseE      = falseE
mapAddHyp f (andE t)    = andE (mapAddHyp (mapAddHyp f) t) -- By induction on types!
mapAddHyp f (orE t u)   = orE (mapAddHyp f t) (mapAddHyp f u)

mapCover :  ∀{P Q} (f : P →̇ Q) {i j} → Cover i j P →̇ Cover i j Q
mapCover f (returnC t) = returnC (f t)
mapCover f (matchC t c) = matchC t (mapAddHyp (mapCover f) c)  -- Cover should be sized!

-- Cover monad

joinCover : ∀{i j P} → Cover i j (Cover ∞ j P) →̇ Cover ∞ j P
joinCover (returnC t) = t
joinCover (matchC t c) = matchC t (mapAddHyp joinCover c)

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
  ∀{A} → Mon (Ne' P A)
monNe' monP τ (hyp x)    = hyp (monH τ x)
monNe' monP τ (impE t u) = impE (monNe' monP τ t) (monP τ u)
monNe' monP τ (andE₁ t)  = andE₁ (monNe' monP τ t)
monNe' monP τ (andE₂ t)  = andE₂ (monNe' monP τ t)

-- Monotonicity of covers

monAddHyp : ∀{P} (monP : Mon P) → ∀{A} → Mon (AddHyp A P)
monAddHyp monP τ (addAtom t) = addAtom (monP (lift τ) t)
monAddHyp monP τ (addNeg t)  = addNeg (monP (lift τ) t)
monAddHyp monP τ (trueE t)   = trueE (monP τ t)
monAddHyp monP τ falseE      = falseE
monAddHyp monP τ (andE t)    = andE (monAddHyp (monAddHyp monP) τ t)
monAddHyp monP τ (orE t u)   = orE (monAddHyp monP τ t) (monAddHyp monP τ u)

-- Monotonicity of derivations

mutual
  monNe : ∀{i A} → Mon (Ne i A)
  monNe {i} τ t =  monNe' (monRFoc {i}) τ t

  monCover : ∀{i j P} (monP : Mon P) → Mon (Cover i j P)
  monCover         monP τ (returnC t)      = returnC (monP τ t)
  monCover {i} {j} monP τ (matchC {i'} t c) = matchC (monNe τ t)
    (monAddHyp (monCover {i'} {j} monP) τ c)

  monRFoc : ∀{i A} → Mon (RFoc i A)
  monRFoc τ (thunk t)   = thunk (monRInv τ t)
  monRFoc τ (hyp x)     = hyp   (monH τ x)
  monRFoc τ trueI       = trueI
  monRFoc τ (andI t t₁) = andI (monRFoc τ t) (monRFoc τ t₁)
  monRFoc τ (orI₁ t)    = orI₁ (monRFoc τ t)
  monRFoc τ (orI₂ t)    = orI₂ (monRFoc τ t)

  monRInv : ∀{i A} → Mon (RInv i A)
  monRInv τ (ret {i} t)     = ret (monCover (monRFoc {i}) τ t)
  monRInv τ trueI       = trueI
  monRInv τ (andI t t₁) = andI (monRInv τ t) (monRInv τ t₁)
  monRInv τ (impI {i} t)    = impI (monAddHyp (monRInv {i}) τ t)

KFun : (P Q : Cxt → Set) (Γ : Cxt) → Set
KFun P Q Γ = ∀{Δ} (τ : Δ ≤ Γ) → P Δ → Q Δ

_⇒̂_ : (P Q : Cxt → Set) (Γ : Cxt) → Set
_⇒̂_ P Q Γ = ∀{Δ} (τ : Δ ≤ Γ) → P Δ → Q Δ

mapAddHyp' : ∀{P Q Γ} (f : (P ⇒̂ Q) Γ) → ∀{A} → AddHyp A P Γ → AddHyp A Q Γ
mapAddHyp' f (addAtom t) = addAtom (f (weak id≤) t)
mapAddHyp' f (addNeg t)  = addNeg (f (weak id≤) t)
mapAddHyp' f (trueE t)   = trueE (f id≤ t)
mapAddHyp' f falseE      = falseE
mapAddHyp' f (andE t)    = andE (mapAddHyp' (λ τ → mapAddHyp' λ τ' → f (τ' • τ)) t) -- By induction on types!
mapAddHyp' f (orE t u)   = orE (mapAddHyp' f t) (mapAddHyp' f u)

mapCover' :  ∀{P Q Γ} (f : (P ⇒̂ Q) Γ) {i j} (c : Cover i j P Γ) → Cover i j Q Γ
mapCover' f (returnC t) = returnC (f id≤ t)
mapCover' f (matchC t c) = matchC t (mapAddHyp' (λ τ → mapCover' λ τ' → f (τ' • τ)) c)  -- Cover is sized!

-- Remark: Graded monad (andE)

bindAddHyp : ∀{A B J K} (monJ : Mon J) → AddHyp A J →̇ ((J ⇒̂ AddHyp B K) ⇒̂ AddHyp (A ∧ B) K)
bindAddHyp monJ t τ k = andE (mapAddHyp' k (monAddHyp monJ τ t))

-- Semantics

⟦_⟧ : ∀{p} (A : Form p) (Γ : Cxt) → Set
⟦ Atom P ⟧  Γ = HypAtom P Γ
⟦ False ⟧   Γ = ⊥
⟦ A ∨ B ⟧   Γ = ⟦ A ⟧ Γ ⊎ ⟦ B ⟧ Γ
⟦ True ⟧    Γ = ⊤
⟦ A ∧ B ⟧   Γ = ⟦ A ⟧ Γ × ⟦ B ⟧ Γ
⟦ A ⇒ B ⟧   Γ = ∀ {Δ} (τ : Δ ≤ Γ) (a : ⟦ A ⟧ Δ) → ⟦ B ⟧ Δ

⟦ Comp A ⟧ = Cover ∞ ∞ ⟦ A ⟧  -- values to computations
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

  reify- : ∀ (A : Form -) → ⟦ A ⟧ →̇ RInv ∞ A
  reify- True     _       = trueI
  reify- (A ∧ B)  (a , b) = andI (reify- A a) (reify- B b)
  reify- (A ⇒ B)  f       = impI (reflectHyp A λ τ a → reify- B (f τ a))
  reify- (Comp A) c       = ret (mapCover (reify+ A) c)

  reify+ : ∀ (A : Form +) → ⟦ A ⟧ →̇ RFoc ∞ A
  reify+ True _           = trueI
  reify+ (A ∧ B) (a , b)  = andI (reify+ A a) (reify+ B b)
  reify+ (Atom P) x       = hyp x
  reify+ False ()
  reify+ (A ∨ B) (inj₁ a) = orI₁ (reify+ A a)
  reify+ (A ∨ B) (inj₂ b) = orI₂ (reify+ B b)
  reify+ (Thunk A) a      = thunk (reify- A a)

  reflectHyp : ∀ A {Γ} {J} (k : ∀ {Δ} (τ : Δ ≤ Γ) → ⟦ A ⟧ Δ → J Δ) → AddHyp A J Γ
  reflectHyp True      k = trueE (k id≤ _)
  reflectHyp (A ∧ B)   k = andE (reflectHyp A λ τ a →
                                 reflectHyp B λ τ' b → k (τ' • τ) (mon⟦ A ⟧ τ' a , b))  -- need monT
  reflectHyp (Atom P)  k = addAtom (k (weak id≤) top)
  reflectHyp False     k = falseE
  reflectHyp (A ∨ B)   k = orE (reflectHyp A (λ τ a → k τ (inj₁ a)))
                               (reflectHyp B (λ τ b → k τ (inj₂ b)))
  reflectHyp (Thunk A) k = addNeg (k (weak id≤) (reflect A (hyp top)))

  -- Since we only have negative hypotheses, we only need to reflect these

  reflect : ∀ (A : Form -) → Ne ∞ A →̇ ⟦ A ⟧
  reflect True t = _
  reflect (A ∧ B) t = reflect A (andE₁ t) , reflect B (andE₂ t)
  reflect (A ⇒ B) t τ a = reflect B (impE (monNe τ t) (reify+ A a))  -- need monNe
  reflect (Comp A) t = matchC t (reflectHyp A λ τ a → returnC a)

-- Negative propositions are comonadic

paste : ∀ (A : Form -) → Cover ∞ ∞ ⟦ A ⟧ →̇ ⟦ A ⟧
paste True    _     = _
paste (A ∧ B) c     = paste A (mapCover proj₁ c) , paste B (mapCover proj₂ c)
paste (A ⇒ B) c τ a = paste B (mapCover' (λ τ' f → f id≤ (mon⟦ A ⟧ τ' a)) (monCover mon⟦ A ⇒ B ⟧ τ c))
paste (Comp A)      = joinCover

-- Snippets to define evaluation in polarized lambda calculus

module Evaluation where

  -- Environments

  G⟦_⟧ : (Γ : Cxt) → Cxt → Set
  G⟦ ε     ⟧ Δ = ⊤
  G⟦ Γ ∙ P ⟧ Δ = G⟦ Γ ⟧ Δ × ⟦ P ⟧ Δ

  monG⟦_⟧ : (Γ : Cxt) → Mon (G⟦ Γ ⟧)
  monG⟦ ε ⟧ = _
  monG⟦ Γ ∙ P ⟧ τ (γ , a) = monG⟦ Γ ⟧ τ γ , mon⟦ P ⟧ τ a

  Ev : (R : Set) (Δ Γ : Cxt) → Set
  Ev R Δ Γ = G⟦ Γ ⟧ Δ → R

  cut : ∀{R P Δ} → ⟦ P ⟧ Δ → AddHyp P (Ev R Δ) →̇ Ev R Δ
  cut x        (addAtom t) γ = t (γ , returnC x)
  cut a        (addNeg t)  γ = t (γ , a)
  cut _        (trueE t)     = t
  cut (a , b)  (andE t)      = cut a (mapAddHyp (cut b) t)
  cut ()       falseE
  cut (inj₁ a) (orE t u)     = cut a t
  cut (inj₂ b) (orE t u)     = cut b u


-- Intuitionistic propositional logic

data IPL : Set where
  Atom        : (P : Atoms) → IPL
  True False  : IPL
  _∨_ _∧_ _⇒_ : (A B : IPL) → IPL

module CallByName where

  _⁻ : IPL → Form -
  Atom P ⁻  = Atom- P
  True ⁻    = True
  False ⁻   = Comp False
  (A ∨ B) ⁻ = Comp (Thunk (A ⁻) ∨ Thunk (B ⁻))
  (A ∧ B) ⁻ = A ⁻ ∧ B ⁻
  (A ⇒ B) ⁻ = Thunk (A ⁻) ⇒ B ⁻

module CallByValue where

  _⁺ : IPL → Form +
  Atom P ⁺  = Atom P
  True ⁺    = True
  False ⁺   = False
  (A ∨ B) ⁺ = A ⁺ ∨ B ⁺
  (A ∧ B) ⁺ = A ⁺ ∧ B ⁺
  (A ⇒ B) ⁺ = Thunk (A ⁺ ⇒ Comp (B ⁺))

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

  run : ∀ A → C⟦ A ⟧ →̇ Cover ∞ ∞ V⟦ A ⟧
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

  impIntro : ∀ {A B Γ} (f : KFun (Cover ∞ ∞ ⟦ A ⟧) ⟦ B ⟧ Γ) → ⟦ A ⇒ B ⟧ Γ
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

  ide : ∀ Γ → Cover ∞ ∞ G⟦ Γ ⟧ (Γ ⁺⁺)
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
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
