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

iNe : ∀{Γ P f} → NeImg (Atom P) Γ f → NfImg (Atom P) Γ f
iNe (t , eq) =  ne t , eq

-- Variables are neutral

iHyp : ∀{Γ A} (x : Hyp A Γ) → NeImg A Γ H⦅ x ⦆
iHyp x = (hyp x , refl)

-- Abstraction operates on normal forms

iImpI : ∀{Γ A B f} → NfImg B (Γ ∙ A) f → NfImg (A ⇒ B) Γ (curry f)
iImpI (t , eq) = impI t , cong curry eq

-- Application of a neutral is neutral

iImpE : ∀{Γ A B f g} → NeImg (A ⇒ B) Γ f → NfImg A Γ g → NeImg B Γ (apply f g)
iImpE (t , eq) (u , eq') = (impE t u , cong₂ apply eq eq')

-- Empty tuple is normal

iTrueI : ∀{Γ f} → NfImg True Γ f
iTrueI = trueI , refl

-- Pairing operates on normal forms

iAndI : ∀{Γ A B f g} → NfImg A Γ f → NfImg B Γ g → NfImg (A ∧ B) Γ < f , g >
iAndI (t , eq) (u , eq') = andI t u , cong₂ <_,_> eq eq'

-- Projection of a neutral is neutral

iAndE₁ : ∀{Γ A B f} → NeImg (A ∧ B) Γ f → NeImg A Γ (proj₁ ∘ f)
iAndE₁ (t , eq) = andE₁ t , cong (proj₁ ∘_) eq

iAndE₂ : ∀{Γ A B f} → NeImg (A ∧ B) Γ f → NeImg B Γ (proj₂ ∘ f)
iAndE₂ (t , eq) = andE₂ t , cong (proj₂ ∘_) eq

-- Injections operate on normal forms

iOrI₁ : ∀{Γ A B f} → NfImg A Γ f → NfImg (A ∨ B) Γ (inj₁ ∘ f)
iOrI₁ (t , eq) = orI₁ t , cong (inj₁ ∘_) eq

iOrI₂ : ∀{Γ A B f} → NfImg B Γ f → NfImg (A ∨ B) Γ (inj₂ ∘ f)
iOrI₂ (t , eq) = orI₂ t , cong (inj₂ ∘_) eq

-- Case splitting forms:

iOrE : ∀{Γ A B C f g h}
  → NeImg (A ∨ B) Γ f
  → NfImg C (Γ ∙ A) g
  → NfImg C (Γ ∙ B) h
  → NfImg C Γ (caseof f g h)
iOrE (t , eqt) (u , equ) (v , eqv) = orE t u v , cong₃ caseof eqt equ eqv

iFalseE : ∀{Γ C f}
  → NeImg False Γ f
  → NfImg C Γ (⊥-elim ∘ f)
iFalseE (t , eq) = falseE t , cong (⊥-elim ∘_) eq

-- For falseE, we can get the stronger:

iFalseE' : ∀{Γ C f}
  → Ne Γ False
  → NfImg C Γ (⊥-elim ∘ f)
iFalseE' t = falseE t , ⊥-elim-ext

-- Beth model

data Cover (X : Form) (P : KPred X)  (Δ : Cxt) : (f : Fun Δ X) → Set where
  idc  : ∀{f} (p : P Δ f) → Cover X P Δ f
  bot  : (t : Ne Δ False) → Cover X P Δ (⊥-elim ∘ Ne⦅ t ⦆)
  node : ∀{A B} (t : Ne Δ (A ∨ B))
         {g} (cg : Cover X P (Δ ∙ A) g)
         {h} (ch : Cover X P (Δ ∙ B) h) → Cover X P Δ (caseof Ne⦅ t ⦆ g h)

-- Cover is monotone in P

monCP : ∀{A} {P Q : KPred A} (P⊂Q : Sub A P Q) → Sub A (Cover A P) (Cover A Q)
monCP P⊂Q (idc p) = idc (P⊂Q p)
monCP P⊂Q (bot t) = bot t
monCP P⊂Q (node t cg ch) = node t (monCP P⊂Q cg) (monCP P⊂Q ch)

Conv : ∀{S T : Set} (g : S → T) (P : KPred' S) (Q : KPred' T) → Set
Conv {S} g P Q = ∀ {Γ} {f : C⦅ Γ ⦆ → S} (p : P Γ f) → Q Γ (g ∘ f)

convC : ∀{A B} (g : T⦅ A ⦆ → T⦅ B ⦆) {P Q} (P⊂Q : Conv g P Q) → Conv g (Cover A P) (Cover B Q)
convC g P⊂Q (idc p) = idc (P⊂Q p)
convC g P⊂Q (bot t) = subst (Cover _ _ _) ⊥-elim-ext (bot t)
convC g P⊂Q (node t cg ch) = subst (Cover _ _ _) (caseof-perm g {Ne⦅ t ⦆})
  (node t (convC g P⊂Q cg) (convC g P⊂Q ch))

-- Weakening Covers

monC : ∀{X} {P : KPred X} (monP : Mon P) → Mon (Cover X P)
  -- {Γ} {f : Fun Γ X} {Δ} (τ : Δ ≤ Γ) (C : Cover X Γ P f) → Cover X Δ P (f ∘ R⦅ τ ⦆)
monC monP τ (idc p) = idc (monP τ p)
monC monP τ (bot t) = subst (Cover _ _ _) ⊥-elim-ext (bot (monNe τ t))
monC monP τ (node t cg ch) = node (monNe τ t) (monC monP (lift τ) cg) (monC monP (lift τ) ch)
  -- REWRITE monD-ne natD

-- Syntactic paste (from Thorsten)

paste' : ∀{A Γ f} (C : Cover A (NfImg A) Γ f) → NfImg A Γ f
paste' (idc t)        = t
paste' (bot t)        = iFalseE (t , refl)
paste' (node t cg ch) = iOrE (t , refl) (paste' cg) (paste' ch)

-- Monad

joinC : ∀{A} {P : KPred A} → Sub A (Cover A (Cover A P)) (Cover A P)
joinC (idc c)        = c
joinC (bot t)        = bot t
joinC (node t cg ch) = node t (joinC cg) (joinC ch)

-- Semantic absurdity type

Absurd : KPred False
Absurd _ _ = ⊥

-- Semantic disjunction type

data Disj A B (⟦A⟧ : KPred A) (⟦B⟧ : KPred B) Γ : Fun Γ (A ∨ B) → Set where
  left  : {g : Fun Γ A} (⟦g⟧ : ⟦A⟧ Γ g) → Disj _ _ _ _ _ (inj₁ ∘ g)
  right : {h : Fun Γ B} (⟦h⟧ : ⟦B⟧ Γ h) → Disj _ _ _ _ _ (inj₂ ∘ h)

monDisj : ∀{A B ⟦A⟧ ⟦B⟧} (monA : Mon ⟦A⟧) (monB : Mon ⟦B⟧) → Mon (Disj A B ⟦A⟧ ⟦B⟧)
monDisj monA monB τ (left  ⟦g⟧) = left  (monA τ ⟦g⟧)
monDisj monA monB τ (right ⟦h⟧) = right (monB τ ⟦h⟧)

-- Semantic conjunction type

Conj : ∀ A B (⟦A⟧ : KPred A) (⟦B⟧ : KPred B) → KPred (A ∧ B)
Conj A B ⟦A⟧ ⟦B⟧ Γ f = ⟦A⟧ Γ (proj₁ ∘ f) × ⟦B⟧ Γ (proj₂ ∘ f)

-- Semantic implication type

Imp : ∀ A B (⟦A⟧ : KPred A) (⟦B⟧ : KPred B) → KPred (A ⇒ B)
Imp A B ⟦A⟧ ⟦B⟧ Γ f = ∀{Δ} (τ : Δ ≤ Γ) {a : Fun Δ A} (⟦a⟧ : ⟦A⟧ Δ a) → ⟦B⟧ Δ (kapp A B f τ a)

-- The Beth model

T⟦_⟧ : (A : Form) (Γ : Cxt) (f : Fun Γ A) → Set
T⟦ Atom P ⟧ = NfImg (Atom P)
T⟦ True ⟧ _ _ = ⊤
T⟦ False ⟧ = Cover False   Absurd
T⟦ A ∨ B ⟧ = Cover (A ∨ B) (Disj A B (T⟦ A ⟧) (T⟦ B ⟧))
T⟦ A ∧ B ⟧ = Conj A B T⟦ A ⟧ T⟦ B ⟧
T⟦ A ⇒ B ⟧ = Imp A B T⟦ A ⟧ T⟦ B ⟧

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

  reflect : ∀{Γ} A {f} (t : NeImg A Γ f) → T⟦ A ⟧ Γ f
  reflect (Atom P) t = iNe t
  reflect True t = _
  reflect False (t , _) = subst (Cover _ _ _) ⊥-elim-ext (bot t)

  -- x : A ∨ B  is reflected as case(x, y. inl y, z. inr z)
  -- Need a proof of caseof x inj₁ inj₂ = x
  reflect (A ∨ B) (t , refl) =  subst (Cover _ _ _) (caseof-eta Ne⦅ t ⦆)
    (node t (idc (left  (reflect A (iHyp top))))
            (idc (right (reflect B (iHyp top)))))

  reflect (A ∧ B) t = reflect A (iAndE₁ t) , reflect B (iAndE₂ t)
  reflect (A ⇒ B) t τ a = reflect B (iImpE (monNeImg τ t) (reify A a))

  reify : ∀{Γ} A {f} (⟦f⟧ : T⟦ A ⟧ Γ f) → NfImg A Γ f
  reify (Atom P) t      = t
  reify True _          = iTrueI
  reify False           = paste' ∘ monCP λ()
  reify (A ∨ B)         = paste' ∘ monCP reifyDisj
  reify (A ∧ B) (a , b) = iAndI (reify A a) (reify B b)
  reify (A ⇒ B) ⟦f⟧     = iImpI (reify B (⟦f⟧ (weak id≤) (reflect A (iHyp top))))

  reifyDisj : ∀{A B} → Sub (A ∨ B) (Disj A B T⟦ A ⟧ T⟦ B ⟧) (NfImg (A ∨ B))
  reifyDisj {A} {B} (left  ⟦g⟧) = iOrI₁ (reify A ⟦g⟧)
  reifyDisj {A} {B} (right ⟦h⟧) = iOrI₂ (reify B ⟦h⟧)

-- A general converter for covers
-- (subsumes monC, monCP, convC).

convCov : ∀ A B (P : KPred A) (Q : KPred B) {Γ₀ Δ₀} (τ₀ : Δ₀ ≤ Γ₀)

  → (φ : ∀ {Γ Δ} (δ : Δ ≤ Δ₀) (τ : Δ ≤ Γ) → Fun Γ A → Fun Δ B)

  → (P⊂Q : ∀{Γ Δ} (δ : Δ ≤ Δ₀) (τ : Δ ≤ Γ) {f} → P Γ f → Q Δ (φ δ τ f))

  → (φ-case : ∀ {Γ Δ} (δ : Δ ≤ Δ₀) (τ : Δ ≤ Γ) →
       ∀ C D (f : Fun Γ (C ∨ D)) (g : Fun (Γ ∙ C) A) (h : Fun (Γ ∙ D) A)
       → caseof (f ∘ R⦅ τ ⦆) (φ (weak δ) (lift {C} τ) g)
                            (φ (weak δ) (lift {D} τ) h) ≡ φ δ τ (caseof f g h))

  → ∀{Γ Δ} (δ : Δ ≤ Δ₀) (τ : Δ ≤ Γ) {f} → Cover A P Γ f → Cover B Q Δ (φ δ τ f)

convCov A B P Q τ₀ φ P⊂Q φ-case {Γ} {Δ} δ τ (idc p) = idc (P⊂Q δ τ p)
convCov A B P Q τ₀ φ P⊂Q φ-case {Γ} {Δ} δ τ (bot t) = subst (Cover _ _ _) ⊥-elim-ext (bot (monNe τ t))
convCov A B P Q τ₀ φ P⊂Q φ-case {Γ} {Δ} δ τ (node {C} {D} t {g} cg {h} ch) =
  subst (Cover _ _ _)
    (φ-case δ τ C D Ne⦅ t ⦆ g h)
    (node (monNe τ t)
      (convCov A B P Q τ₀ φ P⊂Q φ-case (weak δ) (lift {C} τ) cg)
      (convCov A B P Q τ₀ φ P⊂Q φ-case (weak δ) (lift {D} τ) ch))

  -- Just for documentation:
  where
  τC = lift {C} τ
  cg' : Cover B Q (Δ ∙ C) (φ (weak δ) τC g)
  cg' = convCov A B P Q τ₀ φ P⊂Q φ-case (weak δ) τC cg

  τD = lift {D} τ
  ch' : Cover B Q (Δ ∙ D) (φ (weak δ) τD h)
  ch' = convCov A B P Q τ₀ φ P⊂Q φ-case (weak δ) τD ch

  c' : Cover B Q Δ (caseof (Ne⦅ t ⦆ ∘ R⦅ τ ⦆) (φ (weak δ) τC g) (φ (weak δ) τD h))
  c' = node (monNe τ t) cg' ch'

-- Semantic paste

paste : ∀ A {Γ f} (c : Cover A (T⟦ A ⟧) Γ f) → T⟦ A ⟧ Γ f
paste (Atom P) = paste'
paste True     = _
paste False    = joinC
paste (A ∨ B)  = joinC
paste (A ∧ B)  = < paste A ∘ convC proj₁ proj₁ , paste B ∘ convC proj₂ proj₂ >
  where
  fst : ∀ Γ f → Cover (A ∧ B) (Conj A B T⟦ A ⟧ T⟦ B ⟧) Γ f → Cover A T⟦ A ⟧ Γ (proj₁ ∘ f)
  fst Γ f c = convC proj₁ {Conj A B T⟦ A ⟧ T⟦ B ⟧} {T⟦ A ⟧} proj₁ c

paste (A ⇒ B) {Γ₀} {f} c {Δ₀} τ₀ {a} ⟦a⟧ = paste B (convCov (A ⇒ B) B P Q τ₀ φ P⊂Q φ-case id≤ τ₀ c)
  where
  P = Imp A B T⟦ A ⟧ T⟦ B ⟧
  Q = T⟦ B ⟧

  φ : ∀ {Γ Δ} (δ : Δ ≤ Δ₀) (τ : Δ ≤ Γ) → Fun Γ (A ⇒ B) → Fun Δ B
  φ δ τ f = kapp A B f τ (a ∘ R⦅ δ ⦆)

  P⊂Q : ∀ {Γ Δ} (δ : Δ ≤ Δ₀) (τ : Δ ≤ Γ) {f} → Imp A B T⟦ A ⟧ T⟦ B ⟧ Γ f → T⟦ B ⟧ Δ (φ δ τ f)
  P⊂Q δ τ ⟦f⟧ = ⟦f⟧ τ (monT A δ ⟦a⟧)

  φ-case : ∀ {Γ Δ} (δ : Δ ≤ Δ₀) (τ : Δ ≤ Γ) →
           ∀ C D (f : Fun Γ (C ∨ D)) (g : Fun (Γ ∙ C) (A ⇒ B)) (h : Fun (Γ ∙ D) (A ⇒ B))
           → caseof (f ∘ R⦅ τ ⦆) (φ (weak δ) (lift {C} τ) g)
                                 (φ (weak δ) (lift {D} τ) h) ≡ φ δ τ (caseof f g h)

  φ-case δ τ C D f g h = caseof-kapply f g h R⦅ τ ⦆ (a ∘ R⦅ δ ⦆)


-- Fundamental theorem

-- Extension of T⟦_⟧ to contexts

G⟦_⟧ : ∀ (Γ Δ : Cxt) (ρ : Mor Δ Γ) → Set
G⟦ ε     ⟧ Δ ρ = ⊤
G⟦ Γ ∙ A ⟧ Δ ρ = G⟦ Γ ⟧ Δ (proj₁ ∘ ρ) × T⟦ A ⟧ Δ (proj₂ ∘ ρ)

monG : ∀{Γ Δ Φ ρ} (τ : Φ ≤ Δ) → G⟦ Γ ⟧ Δ ρ → G⟦ Γ ⟧ Φ (ρ ∘ R⦅ τ ⦆)
monG {ε}     τ _       = _
monG {Γ ∙ A} τ (γ , a) = monG τ γ , monT A τ a

-- Variable case

fundH : ∀{Γ Δ A ρ} (x : Hyp A Γ) (γ : G⟦ Γ ⟧ Δ ρ) → T⟦ A ⟧ Δ (H⦅ x ⦆ ∘ ρ)
fundH top     = proj₂
fundH (pop x) = fundH x ∘ proj₁

-- orE case

orElim : ∀ X {Γ A B}
         {f} (⟦f⟧ : T⟦ A ∨ B ⟧ Γ f)
         {g} (⟦g⟧ : T⟦ A ⇒ X ⟧ Γ g)
         {h} (⟦h⟧ : T⟦ B ⇒ X ⟧ Γ h) →
         T⟦ X ⟧ Γ (caseof f (uncurry g) (uncurry h))
orElim X {Γ₀} {A} {B} ⟦f⟧ {g} ⟦g⟧ {h} ⟦h⟧ = paste X
  (convCov (A ∨ B) X (Disj A B T⟦ A ⟧ T⟦ B ⟧) T⟦ X ⟧ {Γ₀} id≤ φ P⊂Q φ-case id≤ id≤ ⟦f⟧)

  where
  φ : ∀ {Γ Δ} (δ : Δ ≤ Γ₀) (τ : Δ ≤ Γ) → Fun Γ (A ∨ B) → Fun Δ X
  φ δ τ f = caseof (f ∘ R⦅ τ ⦆) (uncurry (g ∘ R⦅ δ ⦆)) (uncurry (h ∘ R⦅ δ ⦆ ))

  P⊂Q : ∀{Γ Δ} (δ : Δ ≤ Γ₀) (τ : Δ ≤ Γ) {f} → Disj A B T⟦ A ⟧ T⟦ B ⟧ Γ f → T⟦ X ⟧ Δ (φ δ τ f)
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

falseElim : ∀ A {Γ f} (ce : Cover False Absurd Γ f) → T⟦ A ⟧ Γ (⊥-elim ∘ f)
falseElim A {Γ} ce = paste A (convC ⊥-elim ⊥-elim ce)

-- The fundamental theorem

fund :  ∀{A Γ} (t : Γ ⊢ A) {Δ ρ} (γ : G⟦ Γ ⟧ Δ ρ) → T⟦ A ⟧ Δ (D⦅ t ⦆ ∘ ρ)
fund (hyp x) = fundH x
fund (impI t) γ τ a = fund t (monG τ γ , a)
fund (impE t u) γ = fund t γ id≤ (fund u γ)
fund (andI t u) γ = fund t γ , fund u γ
fund (andE₁ t) = proj₁ ∘ fund t
fund (andE₂ t) = proj₂ ∘ fund t
fund (orI₁ t) γ = idc (left  (fund t γ))
fund (orI₂ t) γ = idc (right (fund t γ))
fund {A} (orE t u v) γ =  orElim A (fund t γ)
  (λ τ a → fund u (monG τ γ , a))
  (λ τ b → fund v (monG τ γ , b))
fund {A} (falseE t) γ =  falseElim A (fund t γ)
fund trueI γ = _

-- Identity environment

ide : ∀ Γ → G⟦ Γ ⟧ Γ id
ide ε = _
ide (Γ ∙ A) = monG (weak id≤) (ide Γ) , reflect A (iHyp top)

-- Normalization by evaluation

norm : ∀{Γ A} (t : Γ ⊢ A) → NfImg A Γ D⦅ t ⦆
norm t = reify _ (fund t (ide _))

-- -}
-- -}
