{-# OPTIONS --rewriting #-}

-- A Beth model of normal forms

open import Library

module NbeModel (Base : Set) (B⦅_⦆ : Base → Set) where

import Formulas      ; open module Form = Formulas    Base
import Derivations   ; open module Der  = Derivations Base
import Interpretation; open module Intp = Interpretation Base B⦅_⦆

KPred : (A : Form) → Set₁
KPred A = ∀ Γ → Fun Γ A → Set

Sub : ∀ A (P Q : KPred A) → Set
Sub A P Q = ∀{Γ f} → P Γ f → Q Γ f

Mon : ∀{S} (𝓐 : ∀ Γ (f : C⦅ Γ ⦆ → S) → Set) → Set
Mon {S} 𝓐 = ∀ {Γ Δ} (τ : Δ ≤ Γ) {f : C⦅ Γ ⦆ → S} → 𝓐 Γ f → 𝓐 Δ (f ∘ R⦅ τ ⦆)

NeImg : ∀ A → KPred A
NeImg A Γ f = ∃ λ (t : Ne Γ A) → Ne⦅ t ⦆ ≡ f

NfImg : ∀ A → KPred A
NfImg A Γ f = ∃ λ (t : Nf Γ A) → Nf⦅ t ⦆ ≡ f

monNeImg : ∀{A} → Mon (NeImg A) -- ∀{Γ Δ} (τ : Δ ≤ Γ) {A f} (nei : NeImg Γ A f) → NeImg Δ A (f ∘ R⦅ τ ⦆)
monNeImg τ (t , refl) = monNe τ t , natD τ (ne[ t ])

monNfImg : ∀{A} → Mon (NfImg A) -- ∀{Γ Δ} (τ : Δ ≤ Γ) {A f} (nfi : NfImg Γ A f) → NfImg Δ A (f ∘ R⦅ τ ⦆)
monNfImg τ (t , refl) = monNf τ t , natD τ nf[ t ]

iNe : ∀{Γ P f} → NeImg (Atom P) Γ f → NfImg (Atom P) Γ f
iNe (t , eq) =  ne t , eq

-- iNe : ∀{Γ A f} → NeImg Γ A f → NfImg Γ A f
-- iNe (t , eq) = ne t , eq

iHyp : ∀{Γ A} (x : Hyp Γ A) → NeImg A Γ H⦅ x ⦆
iHyp x = (hyp x , refl)

iImpI : ∀{Γ A B f} → NfImg B (Γ ∙ A) f → NfImg (A ⇒ B) Γ (curry f)
iImpI (t , eq) = impI t , cong curry eq

iImpE : ∀{Γ A B f g} → NeImg (A ⇒ B) Γ f → NfImg A Γ g → NeImg B Γ (apply f g)
iImpE (t , eq) (u , eq') = (impE t u , cong₂ apply eq eq')

iAndE₁ : ∀{Γ A B f} → NeImg (A ∧ B) Γ f → NeImg A Γ (proj₁ ∘ f)
iAndE₁ (t , eq) = andE₁ t , cong (proj₁ ∘_) eq

iAndE₂ : ∀{Γ A B f} → NeImg (A ∧ B) Γ f → NeImg B Γ (proj₂ ∘ f)
iAndE₂ (t , eq) = andE₂ t , cong (proj₂ ∘_) eq

iTrueI : ∀{Γ f} → NfImg True Γ f
iTrueI = trueI , refl

iAndI : ∀{Γ A B f g} → NfImg A Γ f → NfImg B Γ g → NfImg (A ∧ B) Γ < f , g >
iAndI (t , eq) (u , eq') = andI t u , cong₂ <_,_> eq eq'

iOrI₁ : ∀{Γ A B f} → NfImg A Γ f → NfImg (A ∨ B) Γ (inj₁ ∘ f)
iOrI₁ (t , eq) = orI₁ t , cong (inj₁ ∘_) eq

iOrI₂ : ∀{Γ A B f} → NfImg B Γ f → NfImg (A ∨ B) Γ (inj₂ ∘ f)
iOrI₂ (t , eq) = orI₂ t , cong (inj₂ ∘_) eq

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


GPred : (S : Set) → Set₁
GPred S = ∀ Γ (f : C⦅ Γ ⦆ → S) → Set

Func : Cxt → Set → Set
Func Γ S = C⦅ Γ ⦆ → S

module SUB where


  CF : (S T : Set) (Γ : Cxt) → Set
  CF S T Γ = ∀{Δ} (τ : Δ ≤ Γ) → Func Δ S → Func Δ T

  Conv : ∀{S T : Set} (P : GPred S) (Q : GPred T) → Set
  Conv {S} {T} P Q = ∀ {Γ} (φ : CF S T Γ) →
    ∀{Δ} (τ : Δ ≤ Γ) {f : Func Δ S} (p : P Δ f) → Q Δ (φ τ f)

  convC : ∀{X Y} {P Q} (P⊂Q : Conv P Q) → Conv (Cover X P) (Cover Y Q)
  convC P⊂Q φ τ (idc p) = idc (P⊂Q φ τ p)
  convC P⊂Q φ τ (bot t) = subst (Cover _ _ _) ⊥-elim-ext (bot t)
  convC P⊂Q φ τ (node t {g} cg {h} ch) = subst (Cover _ _ _) {! caseof-perm' {!φ τ!} !}
    (node t (convC P⊂Q φ (weak τ) cg) (convC P⊂Q φ (weak τ) ch))
    -- where
    -- aux : ∀{X Y C A : Set} (φ : (C → X) → (C → Y) → (C × A → X) → C × A → Y
    -- aux φ g (c , a) = IMPOSSIBLE

Conv : ∀{S T : Set} (g : S → T) (P : GPred S) (Q : GPred T) → Set
Conv {S} g P Q = ∀ {Γ} {f : C⦅ Γ ⦆ → S} (p : P Γ f) → Q Γ (g ∘ f)

convC : ∀{A B} (g : T⦅ A ⦆ → T⦅ B ⦆) {P Q} (P⊂Q : Conv g P Q) → Conv g (Cover A P) (Cover B Q)
convC g P⊂Q (idc p) = idc (P⊂Q p)
convC g P⊂Q (bot t) = subst (Cover _ _ _) ⊥-elim-ext (bot t)
convC g P⊂Q (node t cg ch) = subst (Cover _ _ _) (caseof-perm g {Ne⦅ t ⦆})
  (node t (convC g P⊂Q cg) (convC g P⊂Q ch))

-- -- NOT THE RIGHT FORMULATION YET
-- Func : Cxt → Set → Set
-- Func Γ S = C⦅ Γ ⦆ → S

-- Conv : ∀{S T : Set} (P : GPred S) (Q : GPred T) → Set
-- Conv {S} {T} P Q = ∀ {Γ} (φ : Func Γ S → Func Γ T) {f : Func Γ S} (p : P Γ f) → Q Γ (φ f)

-- convC : ∀{X Y} {P Q} (P⊂Q : Conv P Q) → Conv (Cover X P) (Cover Y Q)
-- convC P⊂Q φ (idc p) = idc (P⊂Q φ p)
-- convC P⊂Q φ (bot t) = subst (Cover _ _ _) ⊥-elim-ext (bot t)
-- convC P⊂Q φ (node t {g} cg {h} ch) = subst (Cover _ _ _) {! (caseof-perm φ {Ne⦅ t ⦆}) !}
--   (node t (convC P⊂Q (λ x x₁ → {!!}) cg) (convC P⊂Q {!aux φ!} ch))
--   -- where
--   -- aux : ∀{X Y C A : Set} (φ : (C → X) → (C → Y) → (C × A → X) → C × A → Y
--   -- aux φ g (c , a) = IMPOSSIBLE

-- Conv : ∀{S T : Set} (g : ∀{Γ} → Func Γ S → Func Γ T) (P : GPred S) (Q : GPred T) → Set
-- Conv {S} g P Q = ∀ {Γ} {f : Func Γ S} (p : P Γ f) → Q Γ (g f)

-- convC : ∀{X Y} (φ : ∀{Γ} → Fun Γ X → Fun Γ Y) {P Q} (P⊂Q : Conv φ P Q) → Conv φ (Cover X P) (Cover Y Q)
-- convC φ P⊂Q (idc p) = idc (P⊂Q p)
-- convC φ P⊂Q (bot t) = subst (Cover _ _ _) ⊥-elim-ext (bot t)
-- convC φ P⊂Q (node t {g} cg {h} ch) = subst (Cover _ _ _) {! (caseof-perm φ {Ne⦅ t ⦆}) !}
--   (node t (convC φ P⊂Q cg) (convC φ P⊂Q ch))

{-
  where
  lemma : ∀{A B C D E : Set} (k : (C × A → D) → C × A → E) {f : C → A ⊎ A} {g : C × A → D} {h : C × A → D} c →
         [ (λ a → k g (c , a)) , (λ b → k h (c , b)) ] (f c) ≡
         k (λ c → [ (λ a → g (c , a)) , (λ b → h (c , b)) ] (f c)) c
  lemma c = ?
-}

{-
DPred : (S : Cxt → Set) → Set₁
DPred S = ∀ Γ (f : C⦅ Γ ⦆ → S Γ) → Set

Conv' : ∀{S T : Cxt → Set} (g : ∀{Γ Δ} (τ : Δ ≤ Γ) → S Γ → T Δ) (P : DPred S) (Q : DPred T) → Set
Conv' {S} g P Q = ∀ {Γ} {f : C⦅ Γ ⦆ → S Γ} {Δ} (τ : Δ ≤ Γ) (p : P Γ f) → Q Δ ((g τ ∘ f) ∘ R⦅ τ ⦆)

convC' : ∀{A B} (g : ∀{Γ Δ} (τ : Δ ≤ Γ) → Fun Γ A → Fun Δ B) {P Q} (P⊂Q : Conv' g P Q) → Conv' g (Cover A P) (Cover B Q)
convC' g P⊂Q τ (idc p) = idc (P⊂Q τ p)
convC' g P⊂Q τ (bot t) = subst (Cover _ _ _) ⊥-elim-ext (bot (monNe τ t))
convC' g P⊂Q τ (node t cg ch) = subst (Cover _ _ _) (caseof-perm g {Ne⦅ t ⦆ ∘ R⦅ τ ⦆})
  (node (monNe τ t) (convC' g P⊂Q (lift τ) cg) (convC' g P⊂Q (lift τ) ch))
-}
-- Weakening Covers

monC : ∀{X} {P : KPred X} (monP : Mon P) → Mon (Cover X P)
  -- {Γ} {f : Fun Γ X} {Δ} (τ : Δ ≤ Γ) (C : Cover X Γ P f) → Cover X Δ P (f ∘ R⦅ τ ⦆)
monC monP τ (idc p) = idc (monP τ p)
monC monP τ (bot t) = subst (Cover _ _ _) ⊥-elim-ext (bot (monNe τ t))
monC monP τ (node t cg ch) = node (monNe τ t) (monC monP (lift τ) cg) (monC monP (lift τ) ch)
  -- REWRITE monD-ne natD

-- Syntactic paste (from Thorsten)

paste' : ∀{A Γ f} (C : Cover A (NfImg A) Γ f) → NfImg A Γ f
paste' (idc t) = t
paste' (bot t) = falseE t , refl
paste' (node t cg ch) with paste' cg | paste' ch
... | u , refl | v , refl = orE t u v , refl

-- Monad

joinC : ∀{A} {P : KPred A} → Sub A (Cover A (Cover A P)) (Cover A P)
joinC (idc c) = c
joinC (bot t) = bot t
joinC (node t cg ch) = node t (joinC cg) (joinC ch)

{-
data _∈_ Γ : ({Δ} : Cxt) (C : Cover Δ) → Set where
  here  : Γ ∈ idc {Γ}
  left  : ∀{Δ A B C D} {t : Ne Δ (A ∨ B)} (e : Γ ∈ C) → Γ ∈ node t C D
  right : ∀{Δ A B C D} {t : Ne Δ (A ∨ B)} (e : Γ ∈ D) → Γ ∈ node t C D

coverWk : ∀{Γ Δ} {C : Cover Δ} (e : Γ ∈ C) → Γ ≤ Δ
coverWk here      = id≤
coverWk (left  e) = coverWk e • weak id≤
coverWk (right e) = coverWk e • weak id≤

E⦅_⦆ : ∀{Γ Δ} {C : Cover Δ} (e : Γ ∈ C) → Mor Γ Δ
E⦅ e ⦆ = R⦅ coverWk e ⦆

transC : ∀{Γ} (C : Cover Γ) (f : ∀{Δ} → Δ ∈ C → Cover Δ) → Cover Γ
transC idc f = f here
transC (bot t) f = bot t
transC (node t C D) f = node t (transC C (f ∘ left)) (transC D (f ∘ right))

-- UNUSED:
trans∈ : ∀{Γ} (C : Cover Γ) (f : ∀{Δ} → Δ ∈ C → Cover Δ) →
  ∀ {Φ} {Δ} (e : Δ ∈ C) → Φ ∈ f e → Φ ∈ transC C f
trans∈ idc f here = id
trans∈ (bot t) f ()
trans∈ (node t C D) f (left  e) = left  ∘ trans∈ C (f ∘ left ) e
trans∈ (node t C D) f (right e) = right ∘ trans∈ D (f ∘ right) e

split∈ : ∀{Γ} (C : Cover Γ) (f : ∀{Δ} → Δ ∈ C → Cover Δ) {Φ} (e : Φ ∈ transC C f)
  → ∃ λ Δ → ∃ λ (e : Δ ∈ C) → Φ ∈ f e
split∈ idc f e = _ , _ , e
split∈ (bot t) f ()
split∈ (node t C D) f (left e) with split∈ C (f ∘ left) e
... | Δ , e₁ , e₂ = Δ , left e₁ , e₂
split∈ (node t C D) f (right e) with split∈ D (f ∘ right) e
... | Δ , e₁ , e₂ = Δ , right e₁ , e₂
-}
-- Empty cover

EmptyCover : KPred False
EmptyCover = Cover False λ _ _ → ⊥

-- Empty cover is isomorphic to a witness of inconsistency

toEmptyCover : ∀{Γ} (t : Ne Γ False) → EmptyCover Γ (⊥-elim ∘ Ne⦅ t ⦆)
toEmptyCover t = bot t

fromEmptyCover : ∀{Γ f} (ec : EmptyCover Γ f) → NfImg False Γ f
fromEmptyCover ec =  paste' (monCP (λ()) ec)

fromEmptyCover' : ∀{Γ f} (ec : EmptyCover Γ f) → NfImg False Γ f
fromEmptyCover' (idc ())
fromEmptyCover' (bot t) = falseE t , refl
fromEmptyCover' (node t eg eh) with fromEmptyCover' eg | fromEmptyCover' eh
... | u , refl | v , refl = orE t u v , refl

{-
transE : ∀{Γ} (C : Cover Γ) (f : ∀{Δ} → Δ ∈ C → EmptyCover Δ) → EmptyCover Γ
transE C f = transC C (proj₁ ∘ f) , λ e → let _ , e₁ , e₂ = split∈ C (proj₁ ∘ f) e in f e₁ .proj₂ e₂

-}

{-
mon∈ : ∀{Γ Δ Φ} (C : Cover Γ) (τ : Δ ≤ Γ) (e : Φ ∈ monC τ C) → ∃ λ Ψ → Ψ ∈ C × Φ ≤ Ψ
mon∈ {Γ} {Δ} {.Δ} idc τ here = _ , here , τ
mon∈ {Γ} {Δ} {Φ} (bot t) τ ()
mon∈ {Γ} {Δ} {Φ} (node t C D) τ (left e) with mon∈ C (lift τ) e
... | Ψ , e' , σ = Ψ , left e' , σ
mon∈ {Γ} {Δ} {Φ} (node t C D) τ (right e) with mon∈ D (lift τ) e
... | Ψ , e' , σ = Ψ , right e' , σ
-- -}

data Disj A B (⟦A⟧ : KPred A) (⟦B⟧ : KPred B) Γ : Fun Γ (A ∨ B) → Set where
  left  : {g : Fun Γ A} (⟦g⟧ : ⟦A⟧ Γ g) → Disj _ _ _ _ _ (inj₁ ∘ g)
  right : {h : Fun Γ B} (⟦h⟧ : ⟦B⟧ Γ h) → Disj _ _ _ _ _ (inj₂ ∘ h)

monDisj : ∀{A B ⟦A⟧ ⟦B⟧} (monA : Mon ⟦A⟧) (monB : Mon ⟦B⟧) → Mon (Disj A B ⟦A⟧ ⟦B⟧)
monDisj monA monB τ (left  ⟦g⟧) = left  (monA τ ⟦g⟧)
monDisj monA monB τ (right ⟦h⟧) = right (monB τ ⟦h⟧)

Conj : ∀ A B (⟦A⟧ : KPred A) (⟦B⟧ : KPred B) → KPred (A ∧ B)
Conj A B ⟦A⟧ ⟦B⟧ Γ f = ⟦A⟧ Γ (proj₁ ∘ f) × ⟦B⟧ Γ (proj₂ ∘ f)

Imp : ∀ A B (⟦A⟧ : KPred A) (⟦B⟧ : KPred B) → KPred (A ⇒ B)
Imp A B ⟦A⟧ ⟦B⟧ Γ f = ∀{Δ} (τ : Δ ≤ Γ) {a : Fun Δ A} (⟦a⟧ : ⟦A⟧ Δ a) → ⟦B⟧ Δ (kapp {A = A} {B = B} f τ a)

-- The Beth model

T⟦_⟧ : (A : Form) (Γ : Cxt) (f : Fun Γ A) → Set
T⟦ Atom P ⟧ Γ = NfImg (Atom P) Γ
T⟦ True ⟧ Γ _ = ⊤
T⟦ False ⟧ = Cover False   λ _ _ → ⊥
T⟦ A ∨ B ⟧ = Cover (A ∨ B) (Disj A B (T⟦ A ⟧) (T⟦ B ⟧))
-- T⟦ A ∨ B ⟧ Γ = Cover (A ∨ B) Γ λ Δ f →
--   (∃ λ (g : Fun Δ A) → f ≡ inj₁ ∘ g × T⟦ A ⟧ Δ g) ⊎
--   (∃ λ (h : Fun Δ B) → f ≡ inj₂ ∘ h × T⟦ B ⟧ Δ h)
T⟦ A ∧ B ⟧ = Conj A B T⟦ A ⟧ T⟦ B ⟧
T⟦ A ⇒ B ⟧ = Imp A B T⟦ A ⟧ T⟦ B ⟧

monT : ∀ A → Mon T⟦ A ⟧
   -- {Γ Δ} {f : Fun Γ A} (τ : Δ ≤ Γ) → T⟦ A ⟧ Γ f → T⟦ A ⟧ Δ (f ∘ R⦅ τ ⦆)
monT (Atom P) τ = monNfImg τ
monT True τ _ = _
monT False τ = monC (λ _ ()) τ
monT (A ∨ B) = monC (monDisj (monT A) (monT B))
monT (A ∧ B) τ (a , b) = monT A τ a , monT B τ b
monT (A ⇒ B) τ f σ = f (σ • τ)
-- monT (Atom P) τ nfi = monNfImg τ nfi
-- monT True τ _ = _
-- monT False τ (C , f) = monC τ C , λ {Φ} e → f (proj₁ (proj₂ (mon∈ C τ e)))
-- monT (A ∨ B) {Γ} {Δ} τ (C , f) = monC τ C ,  λ {Φ} e →
--   let Ψ , e' , σ = mon∈ C τ e
--   in  {! map-⊎ (monT A σ) (monT B σ) (f {Ψ} e') !}
-- monT (A ∧ B) τ (a , b) = monT A τ a , monT B τ b
-- monT (A ⇒ B) τ f σ = f (σ • τ)

-- Reflection / reification

mutual

  reflect : ∀{Γ} A {f} (t : NeImg A Γ f) → T⟦ A ⟧ Γ f
  reflect (Atom P) t = iNe t
  reflect True t = _
  reflect False (t , refl) = subst (Cover _ _ _) ⊥-elim-ext (bot t)

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
  reify False   cov     = fromEmptyCover cov
  reify (A ∨ B) cov     = paste' (monCP reifyDisj cov)
  reify (A ∧ B) (a , b) = iAndI (reify A a) (reify B b)
  reify (A ⇒ B) ⟦f⟧     = iImpI (reify B (⟦f⟧ (weak id≤) (reflect A (iHyp top))))

  reifyDisj : ∀{A B} → Sub (A ∨ B) (Disj A B T⟦ A ⟧ T⟦ B ⟧) (NfImg (A ∨ B))
  reifyDisj {A} {B} (left  ⟦g⟧) = iOrI₁ (reify A ⟦g⟧)
  reifyDisj {A} {B} (right ⟦h⟧) = iOrI₂ (reify B ⟦h⟧)

-- Semantic paste

paste : ∀ A {Γ f} (c : Cover A (T⟦ A ⟧) Γ f) → T⟦ A ⟧ Γ f
paste (Atom P) c = paste' c
paste True c = _
paste False c = joinC c
paste (A ∨ B) c = joinC c
paste (A ∧ B) c = paste A (convC proj₁ proj₁ c) , paste B (convC proj₂ proj₂ c)
  where
  fst : ∀ Γ f → Cover (A ∧ B) (Conj A B T⟦ A ⟧ T⟦ B ⟧) Γ f → Cover A T⟦ A ⟧ Γ (proj₁ ∘ f)
  fst Γ f c = convC proj₁ {Conj A B T⟦ A ⟧ T⟦ B ⟧} {T⟦ A ⟧} proj₁ c

paste (A ⇒ B) {Γ} {f} c {Δ} τ {a} ⟦a⟧ = paste B {!convC'!}
  where
  aux : Cover (A ⇒ B) (Imp A B T⟦ A ⟧ T⟦ B ⟧) Γ f → Cover B T⟦ B ⟧ Δ (kapp {A = A} {B = B} f τ a)
  -- aux c = convC' {!λ g → g a!} {Imp A B T⟦ A ⟧ T⟦ B ⟧} {T⟦ B ⟧} {!!} τ c
  aux (idc ⟦f⟧) = idc (⟦f⟧ τ ⟦a⟧)
  aux (bot t) = subst (Cover _ _ _ ) ⊥-elim-ext (bot (monNe τ t))
  aux (node t cg ch) = {!subst (Cover _ _ _) ? (node (monNe τ t) (aux cg) (aux ch))!}
-- paste (Atom P) = {! paste' !}
-- paste True C f = _
-- paste False C f = transE C f
-- paste (A ∨ B) C f = transC C (proj₁ ∘ f) , λ e → let _ , e₁ , e₂ = split∈ C (proj₁ ∘ f) e in {! f e₁ .proj₂ e₂ !}
-- paste (A ∧ B) C f = paste A C (proj₁ ∘ f) , paste B C (proj₂ ∘ f)
-- paste (A ⇒ B) C f τ a = paste B (monC τ C) λ {Δ} e → let Ψ , e' , σ  = mon∈ C τ e in {! f e' σ (monT A (coverWk e) a) !}

-- Fundamental theorem

-- Extension of T⟦_⟧ to contexts

G⟦_⟧ : ∀ (Γ Δ : Cxt) (ρ : Mor Δ Γ) → Set
G⟦ ε     ⟧ Δ ρ = ⊤
G⟦ Γ ∙ A ⟧ Δ ρ = G⟦ Γ ⟧ Δ (proj₁ ∘ ρ) × T⟦ A ⟧ Δ (proj₂ ∘ ρ)

monG : ∀{Γ Δ Φ ρ} (τ : Φ ≤ Δ) → G⟦ Γ ⟧ Δ ρ → G⟦ Γ ⟧ Φ (ρ ∘ R⦅ τ ⦆)
monG {ε} τ _ = _
monG {Γ ∙ A} τ (γ , a) = monG τ γ , monT A τ a

-- Variable case

fundH : ∀{Γ Δ A ρ} (x : Hyp Γ A) (γ : G⟦ Γ ⟧ Δ ρ) → T⟦ A ⟧ Δ (H⦅ x ⦆ ∘ ρ)
fundH top     = proj₂
fundH (pop x) = fundH x ∘ proj₁


-- A lemma for the orE case
{-
orElim : ∀ {Γ A B X} (C : Cover Γ) (f : {Δ : Cxt} → Δ ∈ C → T⟦ A ⟧ Δ ⊎ T⟦ B ⟧ Δ) →
         (∀{Δ} (τ : Δ ≤ Γ) → T⟦ A ⟧ Δ → T⟦ X ⟧ Δ) →
         (∀{Δ} (τ : Δ ≤ Γ) → T⟦ B ⟧ Δ → T⟦ X ⟧ Δ) →
         T⟦ X ⟧ Γ
orElim C f g h = paste _ C λ e → [ g (coverWk e) , h (coverWk e) ] (f e)
-}
-- orElim' : ∀ X {Γ A B} {f g h } → (⟦f⟧ : Disj A B T⟦ A ⟧ T⟦ B ⟧ Γ f) →
--          (⟦g⟧ : T⟦ A ⇒ X ⟧ Γ (curry g)) →
--          (⟦h⟧ : T⟦ B ⇒ X ⟧ Γ (curry h)) →
--          T⟦ X ⟧ Γ (caseof f g h)
-- orElim' X (left ⟦a⟧) ⟦g⟧ ⟦h⟧ = ⟦g⟧ (id≤) ⟦a⟧
-- orElim' X (right ⟦b⟧) ⟦g⟧ ⟦h⟧ = ⟦h⟧ id≤ ⟦b⟧

CF : (S T : Set) (Γ : Cxt) → Set
CF S T Γ = ∀{Δ} (τ : Δ ≤ Γ) → Func Δ S → Func Δ T

CovConv : ∀{S T : Set} (P : GPred S) (Q : GPred T) {Γ} (φ : CF S T Γ) → Set
CovConv {S} {T} P Q {Γ} φ =
  ∀{Δ} (τ : Δ ≤ Γ) {f : Func Δ S} (p : P Δ f) → Q Δ (φ τ f)

CFT : (A B : Form) (Γ : Cxt) → Set
CFT A B = CF T⦅ A ⦆ T⦅ B ⦆

CovConvT : ∀ A B (P : KPred A) (Q : KPred B) {Γ} (φ : CFT A B Γ) → Set
CovConvT A B = CovConv

φCase : ∀ X A B {Γ} (g : Fun Γ (A ⇒ X)) (h : Fun Γ (B ⇒ X)) → CFT (A ∨ B) X Γ
       --  ∀ {Δ} (τ : Δ ≤ Γ) (f : Fun Δ (A ∨ B)) → Fun Δ X
φCase X A B g h τ f = (caseof f (uncurry (g ∘ R⦅ τ ⦆)) (uncurry (h ∘ R⦅ τ ⦆)))

orElim' : ∀ X {Γ A B}
         g (⟦g⟧ : T⟦ A ⇒ X ⟧ Γ g)
         h (⟦h⟧ : T⟦ B ⇒ X ⟧ Γ h) → CovConvT (A ∨ B) X (Disj A B T⟦ A ⟧ T⟦ B ⟧) (T⟦ X ⟧) (φCase X A B g h)
         -- ∀{Δ} (τ : Δ ≤ Γ) {f} (⟦f⟧ : Disj A B T⟦ A ⟧ T⟦ B ⟧ Δ f) →
         -- T⟦ X ⟧ Δ (φCase X A B g h τ f)
orElim' X g ⟦g⟧ h ⟦h⟧ τ (left  ⟦a⟧) = ⟦g⟧ τ ⟦a⟧
orElim' X g ⟦g⟧ h ⟦h⟧ τ (right ⟦b⟧) = ⟦h⟧ τ ⟦b⟧

convOr : ∀ X {Γ A B}
         g (⟦g⟧ : T⟦ A ⇒ X ⟧ Γ g)
         h (⟦h⟧ : T⟦ B ⇒ X ⟧ Γ h) →
         CovConv (Cover (A ∨ B) (Disj A B T⟦ A ⟧ T⟦ B ⟧)) (Cover X T⟦ X ⟧) (φCase X A B g h)
convOr X {Γ} {A} {B} g ⟦g⟧ h ⟦h⟧ τ {f} (idc p) = idc {f = φCase X A B g h τ f} ( orElim' X g ⟦g⟧ h ⟦h⟧ τ p )
convOr X g ⟦g⟧ h ⟦h⟧ τ (bot t) = subst (Cover _ _ _) ⊥-elim-ext (bot t)
convOr X {Γ} {A} {B} g ⟦g⟧ h ⟦h⟧ {Δ} τ (node {C} {D} t {i} ci {j} cj) =
  subst (Cover _ _ _) (caseof-swap Ne⦅ t ⦆ i j (g ∘ R⦅ τ ⦆) (h ∘ R⦅ τ ⦆))  -- (funExt (aux Ne⦅ t ⦆))
    (node t (convOr X g ⟦g⟧ h ⟦h⟧ (weak τ) ci)
            (convOr X g ⟦g⟧ h ⟦h⟧ (weak τ) cj))
  where
  -- NOT NEEDED, use caseof-swap
  aux : ∀ (f : Fun Δ (C ∨ D)) (δ : C⦅ Δ ⦆) →
      caseof f (φCase X A B g h (weak {A = C} τ) i) (φCase X A B g h (weak {A = D} τ) j) δ
      ≡ φCase X A B g h τ (caseof f i j) δ
  aux f δ with f δ
  aux f δ | inj₁ a = refl
  aux f δ | inj₂ b = refl
  -- = funExt λ δ → case f δ of λ{ (inj₁ a) → {!refl!} ; (inj₂ b) → {!!} }


-- orElim should be a call to paste, using a converted Cover

orElim : ∀ X {Γ A B}
         {f} (⟦f⟧ : T⟦ A ∨ B ⟧ Γ f)
         {g} (⟦g⟧ : T⟦ A ⇒ X ⟧ Γ g)
         {h} (⟦h⟧ : T⟦ B ⇒ X ⟧ Γ h) →
         T⟦ X ⟧ Γ (caseof f (uncurry g) (uncurry h))
-- orElim X (idc ⟦f⟧) ⟦g⟧ ⟦h⟧ = orElim' X ⟦f⟧ ⟦g⟧ ⟦h⟧
-- orElim X (bot t) ⟦g⟧ ⟦h⟧ =  subst (T⟦ X ⟧ _) ⊥-elim-ext (paste X (bot t))
--   -- {!convC ⊥-elim ⊥-elim (toEmptyCover t)!}
-- orElim X (node t ⟦a⟧ ⟦b⟧) ⟦g⟧ ⟦h⟧ = {!!}
orElim X ⟦f⟧ {g} ⟦g⟧ {h} ⟦h⟧ = paste X (convOr X g ⟦g⟧ h ⟦h⟧ id≤ ⟦f⟧)
  -- paste X (convC {!λ f → caseof f g h!} {!λ d → orElim' X d ⟦g⟧ ⟦h⟧!} ⟦f⟧)  -- NEED generalization of convC

-- A lemma for the falseE case

falseElim : ∀ A {Γ f} (ce : EmptyCover Γ f) → T⟦ A ⟧ Γ (⊥-elim ∘ f)
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

-- Normalization

norm : ∀{Γ A} (t : Γ ⊢ A) → Nf Γ A
norm t = proj₁ (reify _ (fund t (ide _)))

-- -}
-- -}
