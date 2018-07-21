{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}

-- A Beth model for normalization by evaluation

open import Library

module NbeModel (Base : Set) (B⦅_⦆ : Base → Set) where

import Formulas      ; open module Form = Formulas    Base hiding (Mon)
import Derivations   ; open module Der  = Derivations Base
import Interpretation; open module Intp = Interpretation Base B⦅_⦆

-- Form of Kripke predicates into a set S

KPred' : (S : Set) → Set₁
KPred' S = ∀ Γ → (C⦅ Γ ⦆ → S) → Set

-- Form of Kripke predicate on functions into type A
-- KPred A = ∀ Γ → Fun Γ A → Set

KPred : (A : Form) → Set₁
KPred A = KPred' T⦅ A ⦆

-- Pointwise inclusion of Kripke predicates

Sub : ∀ A (P Q : KPred A) → Set
Sub A P Q = ∀{Γ f} → P Γ f → Q Γ f

⟨_⟩_↪_ : ∀ A (P Q : KPred A) → Set
⟨ A ⟩ P ↪ Q = ∀{Γ f} → P Γ f → Q Γ f

_↪_ : ∀{A} (P Q : KPred A) → Set
P ↪ Q = ∀{Γ f} → P Γ f → Q Γ f

-- Conv generalizes _↪_ to move to a new proposition.

Conv : ∀{S T : Set} (g : S → T) (P : KPred' S) (Q : KPred' T) → Set
Conv {S} g P Q = ∀ {Γ} {f : C⦅ Γ ⦆ → S} (p : P Γ f) → Q Γ (g ∘ f)

⟪_⟫_↪_ = Conv

⟪_⟫₂_↪_↪_ : ∀{R S T : Set} (f : R → S → T) (𝓡 : KPred' R) (𝓢 : KPred' S) (𝓣 : KPred' T) → Set
⟪ f ⟫₂ 𝓡 ↪ 𝓢 ↪ 𝓣 = ∀{Γ g h} → 𝓡 Γ g → 𝓢 Γ h → 𝓣 Γ (λ γ → f (g γ) (h γ))

-- Statement of monotonicity for Kripke predicates

Mon : ∀{S} (𝓐 : KPred' S) → Set
Mon {S} 𝓐 = ∀ {Γ Δ} (τ : Δ ≤ Γ) {f : Fun' Γ S} → 𝓐 Γ f → 𝓐 Δ (f ∘ R⦅ τ ⦆)

-- Image under evaluation of a neutral term

NeImg : ∀ A → KPred A
NeImg A Γ f = ∃ λ (t : Ne Γ A) → Ne⦅ t ⦆ ≡ f

-- Image under evaluation of a normal term

NfImg : ∀ A → KPred A
NfImg A Γ f = ∃ λ (t : Nf Γ A) → Nf⦅ t ⦆ ≡ f

-- Being an image is Kripke (monotone in weakening)
-- ∀ (f : Fun Γ A) (τ : Δ ≤ Γ) → Img Γ A f → Img Δ A (f ∘ R⦅ τ ⦆)

monNeImg : ∀{A} → Mon (NeImg A)
monNeImg τ (t , refl) = monNe τ t , natD τ (ne[ t ])

monNfImg : ∀{A} → Mon (NfImg A)
monNfImg τ (t , refl) = monNf τ t , natD τ nf[ t ]

-- Extending the constructions of neutral and normal forms to images of such.

-- Neutrals of base type are normal

iNe : ∀{P} → NeImg (Atom P) ↪ NfImg (Atom P)
iNe (t , eq) =  ne t , eq

-- Variables are neutral

iHyp : ∀{Γ A} (x : Hyp A Γ) → NeImg A Γ H⦅ x ⦆
iHyp x = (hyp x , refl)

-- Abstraction operates on normal forms

iImpI : ∀{Γ A B f} → NfImg B (Γ ∙ A) f → NfImg (A ⇒ B) Γ (curry f)
iImpI (t , eq) = impI t , cong curry eq

-- Application of a neutral is neutral
-- iImpE : NeImg (A ⇒ B) Γ f → NfImg A Γ g → NeImg B Γ (apply f g)

iImpE : ∀{A B} → ⟪ _$_ ⟫₂ NeImg (A ⇒ B) ↪ NfImg A ↪ NeImg B
iImpE (t , eq) (u , eq') = (impE t u , cong₂ apply eq eq')

-- Empty tuple is normal

iTrueI : ∀{Γ f} → NfImg True Γ f
iTrueI = trueI , refl

-- Pairing operates on normal forms

iAndI : ∀{A B} → ⟪ _,_ ⟫₂ NfImg A ↪ NfImg B ↪ NfImg (A ∧ B)
iAndI (t , eq) (u , eq') = andI t u , cong₂ <_,_> eq eq'

-- Projection of a neutral is neutral

iAndE₁ : ∀{A B} → ⟪ proj₁ ⟫ NeImg (A ∧ B) ↪ NeImg A
iAndE₁ (t , eq) = andE₁ t , cong (proj₁ ∘_) eq

iAndE₂ : ∀{A B} → ⟪ proj₂ ⟫ NeImg (A ∧ B) ↪ NeImg B
iAndE₂ (t , eq) = andE₂ t , cong (proj₂ ∘_) eq

-- Injections operate on normal forms

iOrI₁ : ∀{A B} → ⟪ inj₁ ⟫ NfImg A ↪ NfImg (A ∨ B)
iOrI₁ (t , eq) = orI₁ t , cong (inj₁ ∘_) eq

iOrI₂ : ∀{A B} → ⟪ inj₂ ⟫ NfImg B ↪ NfImg (A ∨ B)
iOrI₂ (t , eq) = orI₂ t , cong (inj₂ ∘_) eq

-- Case splitting forms:

iOrE : ∀{Γ A B C f g h}
  → NeImg (A ∨ B) Γ f
  → NfImg C (Γ ∙ A) g
  → NfImg C (Γ ∙ B) h
  → NfImg C Γ (caseof f g h)
iOrE (t , eqt) (u , equ) (v , eqv) = orE t u v , cong₃ caseof eqt equ eqv

iFalseE : ∀{C} → ⟪ ⊥-elim ⟫ NeImg False ↪ NfImg C
iFalseE (t , eq) = falseE t , cong (⊥-elim ∘_) eq

-- For falseE, we can get the stronger:

iFalseE' : ∀{Γ C f}
  → Ne Γ False
  → NfImg C Γ (⊥-elim ∘ f)
iFalseE' t = falseE t , ⊥-elim-ext

-- Cover A (P : KPred A) : KPred A  is an extension of Kripke predicate P
-- (on functions into A) by case trees (whose leaves satisfy P).

data Cover (A : Form) (P : KPred A)  (Δ : Cxt) : (f : Fun Δ A) → Set where
  return : ∀{f} (p : P Δ f) → Cover A P Δ f
  falseC : (t : Ne Δ False) → Cover A P Δ (⊥-elim ∘ Ne⦅ t ⦆)
  orC    : ∀{C D} (t : Ne Δ (C ∨ D))
           {g} (cg : Cover A P (Δ ∙ C) g)
           {h} (ch : Cover A P (Δ ∙ D) h) → Cover A P Δ (caseof Ne⦅ t ⦆ g h)

-- Cover is monotone in P

mapC : ∀{A} {P Q : KPred A} (P⊂Q : ⟨ A ⟩ P ↪ Q) → ⟨ A ⟩ Cover A P ↪ Cover A Q
mapC P⊂Q (return p)    = return (P⊂Q p)
mapC P⊂Q (falseC t)    = falseC t
mapC P⊂Q (orC t cg ch) = orC t (mapC P⊂Q cg) (mapC P⊂Q ch)

-- Case trees can be composed, which makes  Cover A  a monad
-- in the category of kripke predicates  KPred A  and  their embeddings
-- ⟨ A ⟩.

joinC : ∀{A} {P : KPred A} → ⟨ A ⟩ Cover A (Cover A P) ↪ Cover A P
joinC (return c)    = c
joinC (falseC t)    = falseC t
joinC (orC t cg ch) = orC t (joinC cg) (joinC ch)

-- Weakening covers (Cover preserves Kripke)
-- (τ : Δ ≤ Γ) → Cover A Γ P f → Cover A Δ P (f ∘ R⦅ τ ⦆)

monC : ∀{A} {P : KPred A} (monP : Mon P) → Mon (Cover A P)
monC monP τ (return p)    = return (monP τ p)
monC monP τ (falseC t)    = subst (Cover _ _ _) ⊥-elim-ext (falseC (monNe τ t))
monC monP τ (orC t cg ch) = orC (monNe τ t) (monC monP (lift τ) cg) (monC monP (lift τ) ch)
  -- REWRITE monD-ne natD

-- Converting covers to a new target proposition

-- A (simple) converter for covers (pointwise in the context)

convC : ∀{A B} (g : T⦅ A ⦆ → T⦅ B ⦆) {P Q} (P⊂Q : ⟪ g ⟫ P ↪ Q) → ⟪ g ⟫ Cover A P ↪ Cover B Q
convC g P⊂Q (return p)    = return (P⊂Q p)
convC g P⊂Q (falseC t)    = subst (Cover _ _ _) ⊥-elim-ext (falseC t)
convC g P⊂Q (orC t cg ch) = subst (Cover _ _ _) (caseof-perm g {Ne⦅ t ⦆})
  (orC t (convC g P⊂Q cg) (convC g P⊂Q ch))

-- A general converter going to a new target proposition and an extended context at the same time.
-- (subsumes mapC, monC, convC).

record Converter A B (P : KPred A) (Q : KPred B) {Γ₀ Δ₀} (τ₀ : Δ₀ ≤ Γ₀) : Set where
  field
    -- Conversion functional
    φ      : ∀ {Γ Δ} (δ : Δ ≤ Δ₀) (τ : Δ ≤ Γ) → Fun Γ A → Fun Δ B

    -- φ distributes over case
    φ-case : ∀ {Γ Δ} (δ : Δ ≤ Δ₀) (τ : Δ ≤ Γ) →
             ∀ C D (f : Fun Γ (C ∨ D)) (g : Fun (Γ ∙ C) A) (h : Fun (Γ ∙ D) A)
             → caseof (f ∘ R⦅ τ ⦆) (φ (weak δ) (lift {C} τ) g)
                                  (φ (weak δ) (lift {D} τ) h) ≡ φ δ τ (caseof f g h)

    -- φ transports from P to Q
    P⊂Q   : ∀{Γ Δ} (δ : Δ ≤ Δ₀) (τ : Δ ≤ Γ) {f} → P Γ f → Q Δ (φ δ τ f)

-- The conversion is implemented by recursion over the case tree

module _ A B (P : KPred A) (Q : KPred B) {Γ₀ Δ₀} (τ₀ : Δ₀ ≤ Γ₀)
  (conv : Converter A B P Q τ₀) (open Converter conv) where

  convCov : ∀{Γ Δ} (δ : Δ ≤ Δ₀) (τ : Δ ≤ Γ) {f} → Cover A P Γ f → Cover B Q Δ (φ δ τ f)
  convCov {Γ} {Δ} δ τ (return p) = return (P⊂Q δ τ p)
  convCov {Γ} {Δ} δ τ (falseC t) = subst (Cover _ _ _) ⊥-elim-ext (falseC (monNe τ t))
  convCov {Γ} {Δ} δ τ (orC {C} {D} t {g} cg {h} ch) =
    subst (Cover _ _ _)
      (φ-case δ τ C D Ne⦅ t ⦆ g h)
      (orC (monNe τ t)
        (convCov (weak δ) (lift {C} τ) cg)
        (convCov (weak δ) (lift {D} τ) ch))

    -- Just for documentation:
    where
    τC = lift {C} τ
    cg' : Cover B Q (Δ ∙ C) (φ (weak δ) τC g)
    cg' = convCov (weak δ) τC cg

    τD = lift {D} τ
    ch' : Cover B Q (Δ ∙ D) (φ (weak δ) τD h)
    ch' = convCov (weak δ) τD ch

    c' : Cover B Q Δ (caseof (Ne⦅ t ⦆ ∘ R⦅ τ ⦆) (φ (weak δ) τC g) (φ (weak δ) τD h))
    c' = orC (monNe τ t) cg' ch'

-- Implementations in terms of convCov (all need monotonicity of P)

-- Cover is monotone in P

mapCᶜ : ∀{A} {P Q : KPred A} (monP : Mon P) (P⊂Q : ⟨ A ⟩ P ↪ Q) → ⟨ A ⟩ Cover A P ↪ Cover A Q
mapCᶜ {A} {P} {Q} monP P⊂Q {Γ} {f} c = convCov A A P Q id≤ conv id≤ id≤ c
  where
  conv : Converter A A P Q id≤
  conv = record
    { φ      = λ δ τ f         → f ∘ R⦅ τ ⦆
    ; φ-case = λ δ τ C D f g h → refl
    ; P⊂Q    = λ δ τ ⟦f⟧       → P⊂Q (monP τ ⟦f⟧)
    }

-- Weakening Covers

monCᶜ : ∀{A} {P : KPred A} (monP : Mon P) → Mon (Cover A P)
monCᶜ {A} {P} monP {Γ} {Δ} τ {f} c = convCov A A P P id≤ conv id≤ τ c
  where
  conv : Converter A A P P id≤
  conv = record
    { φ      = λ δ τ f         → f ∘ R⦅ τ ⦆
    ; φ-case = λ δ τ C D f g h → refl
    ; P⊂Q    = λ δ τ ⟦f⟧       → monP τ ⟦f⟧
    }

-- A converter for covers (pointwise in the context)

convCᶜ : ∀{A B} (g : T⦅ A ⦆ → T⦅ B ⦆) {P Q} (monP : Mon P) (P⊂Q : ⟪ g ⟫ P ↪ Q) → ⟪ g ⟫ Cover A P ↪ Cover B Q
convCᶜ {A} {B} g₀ {P} {Q} monP P⊂Q {Γ} {f} p = convCov A B P Q id≤ conv id≤ id≤ p
  where
  conv : Converter A B P Q id≤
  conv = record
    { φ      = λ δ τ f         → g₀ ∘ f ∘ R⦅ τ ⦆
    ; φ-case = λ δ τ C D f g h → caseof-perm g₀ {f ∘ R⦅ τ ⦆}
    ; P⊂Q    = λ δ τ ⟦f⟧       → P⊂Q (monP τ ⟦f⟧)
    }

-- Syntactic paste:
-- a case tree over normal forms is a normal form.

pasteNf : ∀{A} → ⟨ A ⟩ Cover A (NfImg A) ↪ NfImg A
pasteNf (return t)    = t
pasteNf (falseC t)    = iFalseE (t , refl)
pasteNf (orC t cg ch) = iOrE (t , refl) (pasteNf cg) (pasteNf ch)

-- Bicartesian closure of KPred

-- Semantic absurdity type (initial object)

Absurd : KPred False
Absurd _ _ = ⊥

-- Semantic disjunction type (coproduct)

data Disj A B (⟦A⟧ : KPred A) (⟦B⟧ : KPred B) Γ : Fun Γ (A ∨ B) → Set where
  left  : {g : Fun Γ A} (⟦g⟧ : ⟦A⟧ Γ g) → Disj _ _ _ _ _ (inj₁ ∘ g)
  right : {h : Fun Γ B} (⟦h⟧ : ⟦B⟧ Γ h) → Disj _ _ _ _ _ (inj₂ ∘ h)

monDisj : ∀{A B ⟦A⟧ ⟦B⟧} (monA : Mon ⟦A⟧) (monB : Mon ⟦B⟧) → Mon (Disj A B ⟦A⟧ ⟦B⟧)
monDisj monA monB τ (left  ⟦g⟧) = left  (monA τ ⟦g⟧)
monDisj monA monB τ (right ⟦h⟧) = right (monB τ ⟦h⟧)

-- Semantic truth type (terminal object)

Truth : KPred True
Truth _ _ = ⊤

-- Semantic conjunction type (product)

Conj : ∀ A B (⟦A⟧ : KPred A) (⟦B⟧ : KPred B) → KPred (A ∧ B)
Conj A B ⟦A⟧ ⟦B⟧ Γ f = ⟦A⟧ Γ (proj₁ ∘ f) × ⟦B⟧ Γ (proj₂ ∘ f)

-- Semantic implication type (exponential)

Imp : ∀ A B (⟦A⟧ : KPred A) (⟦B⟧ : KPred B) → KPred (A ⇒ B)
Imp A B ⟦A⟧ ⟦B⟧ Γ f = ∀{Δ} (τ : Δ ≤ Γ) {a : Fun Δ A} (⟦a⟧ : ⟦A⟧ Δ a) → ⟦B⟧ Δ (kapp A B f τ a)

-- The Beth model

T⟦_⟧ : (A : Form) → KPred A
T⟦ Atom P ⟧ = NfImg (Atom P)
T⟦ True   ⟧ = Truth
T⟦ False  ⟧ = Cover False   Absurd
T⟦ A ∨ B  ⟧ = Cover (A ∨ B) (Disj A B (T⟦ A ⟧) (T⟦ B ⟧))
T⟦ A ∧ B  ⟧ = Conj A B T⟦ A ⟧ T⟦ B ⟧
T⟦ A ⇒ B  ⟧ = Imp A B T⟦ A ⟧ T⟦ B ⟧

-- Monotonicity of semantics
-- (τ : Δ ≤ Γ) → T⟦ A ⟧ Γ f → T⟦ A ⟧ Δ (f ∘ R⦅ τ ⦆)

monT : ∀ A → Mon T⟦ A ⟧
monT (Atom P)  = monNfImg
monT True      = _
monT False     = monC λ _ ()
monT (A ∨ B)   = monC (monDisj (monT A) (monT B))
monT (A ∧ B) τ = monT A τ ×̇ monT B τ
monT (A ⇒ B) τ f σ = f (σ • τ)

-- Reflection / reification

mutual

  reflect : ∀ A → ⟨ A ⟩ NeImg A ↪ T⟦ A ⟧
  reflect (Atom P)      = iNe
  reflect True          = _
  reflect False (t , _) = subst (Cover _ _ _) ⊥-elim-ext (falseC t)

  -- x : A ∨ B  is reflected as case(x, y. inl y, z. inr z)
  -- Need a proof of caseof x inj₁ inj₂ = x
  reflect (A ∨ B) (t , refl) = subst (Cover _ _ _) (caseof-eta Ne⦅ t ⦆)
    (orC t (return (left  (reflect A (iHyp top))))
           (return (right (reflect B (iHyp top)))))

  reflect (A ∧ B) i     = reflect A (iAndE₁ i) , reflect B (iAndE₂ i)
  reflect (A ⇒ B) i τ a = reflect B (iImpE (monNeImg τ i) (reify A a))

  reify : ∀ A → ⟨ A ⟩ T⟦ A ⟧ ↪ NfImg A
  reify (Atom P)        = id
  reify True _          = iTrueI
  reify False           = pasteNf ∘ mapC λ()
  reify (A ∨ B)         = pasteNf ∘ mapC reifyDisj
  reify (A ∧ B) (a , b) = iAndI (reify A a) (reify B b)
  reify (A ⇒ B) ⟦f⟧     = iImpI (reify B (⟦f⟧ (weak id≤) (reflect A (iHyp top))))

  reifyDisj : ∀{A B} → ⟨ A ∨ B ⟩ Disj A B T⟦ A ⟧ T⟦ B ⟧ ↪ NfImg (A ∨ B)
  reifyDisj {A} {B} (left  ⟦g⟧) = iOrI₁ (reify A ⟦g⟧)
  reifyDisj {A} {B} (right ⟦h⟧) = iOrI₂ (reify B ⟦h⟧)

-- Semantic paste

paste : ∀ A → ⟨ A ⟩ Cover A (T⟦ A ⟧) ↪ T⟦ A ⟧
paste (Atom P) = pasteNf
paste True     = _
paste False    = joinC
paste (A ∨ B)  = joinC
paste (A ∧ B)  = < paste A ∘ convC proj₁ proj₁ , paste B ∘ convC proj₂ proj₂ >
paste (A ⇒ B) {Γ₀} {f} c {Δ₀} τ₀ {a} ⟦a⟧ = paste B (convCov (A ⇒ B) B P Q τ₀ record{Conv} id≤ τ₀ c)
  where
  P = Imp A B T⟦ A ⟧ T⟦ B ⟧
  Q = T⟦ B ⟧

  module Conv where
    φ : ∀ {Γ Δ} (δ : Δ ≤ Δ₀) (τ : Δ ≤ Γ) → Fun Γ (A ⇒ B) → Fun Δ B
    φ δ τ f = kapp A B f τ (a ∘ R⦅ δ ⦆)

    P⊂Q : ∀ {Γ Δ} (δ : Δ ≤ Δ₀) (τ : Δ ≤ Γ) {f} → P Γ f → Q Δ (φ δ τ f)
    P⊂Q δ τ ⟦f⟧ = ⟦f⟧ τ (monT A δ ⟦a⟧)

    φ-case : ∀ {Γ Δ} (δ : Δ ≤ Δ₀) (τ : Δ ≤ Γ) →
             ∀ C D (f : Fun Γ (C ∨ D)) (g : Fun (Γ ∙ C) (A ⇒ B)) (h : Fun (Γ ∙ D) (A ⇒ B))
             → caseof (f ∘ R⦅ τ ⦆) (φ (weak δ) (lift {C} τ) g)
                                   (φ (weak δ) (lift {D} τ) h) ≡ φ δ τ (caseof f g h)

    φ-case δ τ C D f g h = caseof-kapply f g h R⦅ τ ⦆ (a ∘ R⦅ δ ⦆)


-- Fundamental theorem

-- Extension of T⟦_⟧ to contexts

G⟦_⟧ : ∀ Γ → KPred' C⦅ Γ ⦆
G⟦ ε     ⟧ Δ ρ = ⊤
G⟦ Γ ∙ A ⟧ Δ ρ = G⟦ Γ ⟧ Δ (proj₁ ∘ ρ) × T⟦ A ⟧ Δ (proj₂ ∘ ρ)

-- monG : ∀{Γ Δ Φ ρ} (τ : Φ ≤ Δ) → G⟦ Γ ⟧ Δ ρ → G⟦ Γ ⟧ Φ (ρ ∘ R⦅ τ ⦆)
monG : ∀{Γ} → Mon G⟦ Γ ⟧
monG {ε}     τ _       = _
monG {Γ ∙ A} τ (γ , a) = monG τ γ , monT A τ a

-- Variable case
-- fundH : (x : Hyp A Γ) (γ : G⟦ Γ ⟧ Δ ρ) → T⟦ A ⟧ Δ (H⦅ x ⦆ ∘ ρ)

fundH : ∀{Γ A} (x : Hyp A Γ) → ⟪ H⦅ x ⦆ ⟫ G⟦ Γ ⟧ ↪ T⟦ A ⟧
fundH top     = proj₂
fundH (pop x) = fundH x ∘ proj₁

-- orE case

orElim : ∀ E {Γ A B}
         {f} (⟦f⟧ : T⟦ A ∨ B ⟧ Γ f)
         {g} (⟦g⟧ : T⟦ A ⇒ E ⟧ Γ g)
         {h} (⟦h⟧ : T⟦ B ⇒ E ⟧ Γ h) →
         T⟦ E ⟧ Γ (caseof f (uncurry g) (uncurry h))
orElim E {Γ₀} {A} {B} ⟦f⟧ {g} ⟦g⟧ {h} ⟦h⟧ = paste E
  (convCov (A ∨ B) E P Q {Γ₀} id≤ record{Conv} id≤ id≤ ⟦f⟧)
  where

  P = Disj A B T⟦ A ⟧ T⟦ B ⟧
  Q = T⟦ E ⟧

  module Conv where

    φ : ∀ {Γ Δ} (δ : Δ ≤ Γ₀) (τ : Δ ≤ Γ) → Fun Γ (A ∨ B) → Fun Δ E
    φ δ τ f = caseof (f ∘ R⦅ τ ⦆) (uncurry (g ∘ R⦅ δ ⦆)) (uncurry (h ∘ R⦅ δ ⦆ ))

    P⊂Q : ∀{Γ Δ} (δ : Δ ≤ Γ₀) (τ : Δ ≤ Γ) {f} → P Γ f → Q Δ (φ δ τ f)
    P⊂Q δ τ (left  ⟦a⟧) = ⟦g⟧ δ (monT A τ ⟦a⟧)
    P⊂Q δ τ (right ⟦b⟧) = ⟦h⟧ δ (monT B τ ⟦b⟧)

    φ-case : ∀ {Γ Δ} (δ : Δ ≤ Γ₀) (τ : Δ ≤ Γ) →
      ∀ C D (k : Fun Γ (C ∨ D)) (i : Fun (Γ ∙ C) (A ∨ B)) (j : Fun (Γ ∙ D) (A ∨ B)) →

        caseof (k ∘ R⦅ τ ⦆) (φ (weak δ) (lift {C} τ) i)
                           (φ (weak δ) (lift {D} τ) j)
        ≡ φ δ τ (caseof k i j)

    φ-case δ τ C D k i j =
     caseof-swap
       (k ∘ R⦅ τ ⦆)
       (uncurry (curry i ∘ R⦅ τ ⦆))
       (uncurry (curry j ∘ R⦅ τ ⦆))
       (g ∘ R⦅ δ ⦆)
       (h ∘ R⦅ δ ⦆)

-- A lemma for the falseE case

falseElim : ∀ A → ⟪ ⊥-elim ⟫ T⟦ False ⟧ ↪ T⟦ A ⟧
falseElim A = paste A ∘ convC ⊥-elim ⊥-elim

-- The fundamental theorem

-- fund :  ∀{A Γ} (t : Γ ⊢ A) {Δ ρ} (γ : G⟦ Γ ⟧ Δ ρ) → T⟦ A ⟧ Δ (D⦅ t ⦆ ∘ ρ)
fund :  ∀{A Γ} (t : Γ ⊢ A) → ⟪ D⦅ t ⦆ ⟫ G⟦ Γ ⟧ ↪ T⟦ A ⟧
fund (hyp x)           = fundH x
fund (impI t) γ τ a    = fund t (monG τ γ , a)
fund (impE t u) γ      = fund t γ id≤ (fund u γ)
fund (andI t u)        = < fund t , fund u >
fund (andE₁ t)         = proj₁ ∘ fund t
fund (andE₂ t)         = proj₂ ∘ fund t
fund (orI₁ t) γ        = return (left  (fund t γ))
fund (orI₂ t) γ        = return (right (fund t γ))
fund {A} (orE t u v) γ =  orElim A (fund t γ)
  (λ τ a → fund u (monG τ γ , a))
  (λ τ b → fund v (monG τ γ , b))
fund {A} (falseE t) γ  =  falseElim A (fund t γ)
fund trueI γ           = _

-- Identity environment

ide : ∀ Γ → G⟦ Γ ⟧ Γ id
ide ε = _
ide (Γ ∙ A) = monG (weak id≤) (ide Γ) , reflect A (iHyp top)

-- Normalization by evaluation

norm : ∀{Γ A} (t : Γ ⊢ A) → NfImg A Γ D⦅ t ⦆
norm t = reify _ (fund t (ide _))

-- -}
-- -}
