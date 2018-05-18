{-# OPTIONS --rewriting #-}

-- A Beth model of normal forms

open import Library

module NbeModel (Base : Set) (B⦅_⦆ : Base → Set) where

import Formulas      ; open module Form = Formulas    Base
import Derivations   ; open module Der  = Derivations Base
import Interpretation; open module Intp = Interpretation Base B⦅_⦆

NeImg : (Γ : Cxt) (A : Form) (f : Fun Γ A) → Set
NeImg Γ A f = ∃ λ (t : Ne Γ A) → Ne⦅ t ⦆ ≡ f

NfImg : (Γ : Cxt) (A : Form) (f : Fun Γ A) → Set
NfImg Γ A f = ∃ λ (t : Nf Γ A) → Nf⦅ t ⦆ ≡ f

monNeImg : ∀{Γ Δ} (τ : Δ ≤ Γ) {A f} (nei : NeImg Γ A f) → NeImg Δ A (f ∘ R⦅ τ ⦆)
monNeImg τ (t , refl) = monNe τ t , natD τ (ne[ t ])

monNfImg : ∀{Γ Δ} (τ : Δ ≤ Γ) {A f} (nfi : NfImg Γ A f) → NfImg Δ A (f ∘ R⦅ τ ⦆)
monNfImg τ (t , refl) = monNf τ t , natD τ nf[ t ]

iNe : ∀{Γ P f} → NeImg Γ (Atom P) f → NfImg Γ (Atom P) f
iNe (t , eq) =  ne t , eq

-- iNe : ∀{Γ A f} → NeImg Γ A f → NfImg Γ A f
-- iNe (t , eq) = ne t , eq

iHyp : ∀{Γ A} (x : Hyp Γ A) → NeImg Γ A H⦅ x ⦆
iHyp x = (hyp x , refl)

iImpI : ∀{Γ A B f} → NfImg (Γ ∙ A) B f → NfImg Γ (A ⇒ B) (curry f)
iImpI (t , eq) = impI t , cong curry eq

iImpE : ∀{Γ A B f g} → NeImg Γ (A ⇒ B) f → NfImg Γ A g → NeImg Γ B (apply f g)
iImpE (t , eq) (u , eq') = (impE t u , cong₂ apply eq eq')

iAndE₁ : ∀{Γ A B f} → NeImg Γ (A ∧ B) f → NeImg Γ A (proj₁ ∘ f)
iAndE₁ (t , eq) = andE₁ t , cong (proj₁ ∘_) eq

iAndE₂ : ∀{Γ A B f} → NeImg Γ (A ∧ B) f → NeImg Γ B (proj₂ ∘ f)
iAndE₂ (t , eq) = andE₂ t , cong (proj₂ ∘_) eq

iTrueI : ∀{Γ f} → NfImg Γ True f
iTrueI = trueI , refl

iAndI : ∀{Γ A B f g} → NfImg Γ A f → NfImg Γ B g → NfImg Γ (A ∧ B) < f , g >
iAndI (t , eq) (u , eq') = andI t u , cong₂ <_,_> eq eq'

iOrI₁ : ∀{Γ A B f} → NfImg Γ A f → NfImg Γ (A ∨ B) (inj₁ ∘ f)
iOrI₁ (t , eq) = orI₁ t , cong (inj₁ ∘_) eq

iOrI₂ : ∀{Γ A B f} → NfImg Γ B f → NfImg Γ (A ∨ B) (inj₂ ∘ f)
iOrI₂ (t , eq) = orI₂ t , cong (inj₂ ∘_) eq

-- Beth model

KPred : (A : Form) → Set₁
KPred A = ∀ Γ → Fun Γ A → Set

Mon : ∀{S} (𝓐 : ∀ Γ (f : C⦅ Γ ⦆ → S) → Set) → Set
Mon {S} 𝓐 = ∀ {Γ Δ} (τ : Δ ≤ Γ) {f : C⦅ Γ ⦆ → S} → 𝓐 Γ f → 𝓐 Δ (f ∘ R⦅ τ ⦆)

-- Need to track domain C⦅ Δ ⦆ → Set

data Cover (X : Form) (Δ : Cxt) (P : ∀ Γ → Fun Γ X → Set) : (f : Fun Δ X) → Set where
  idc  : ∀{f} → P Δ f → Cover X Δ P f
  bot  : (t : Ne Δ False) → Cover X Δ P (⊥-elim ∘ Ne⦅ t ⦆)
  node : ∀{A B} (t : Ne Δ (A ∨ B))
         {g} (cg : Cover X (Δ ∙ A) P g)
         {h} (ch : Cover X (Δ ∙ B) P h) → Cover X Δ P (caseof Ne⦅ t ⦆ g h)

-- Weakening Covers

monC : ∀{X} {P : ∀ Δ  → Fun Δ X → Set} (monP : Mon P)
  {Γ} {f : Fun Γ X} {Δ} (τ : Δ ≤ Γ) (C : Cover X Γ P f) → Cover X Δ P (f ∘ R⦅ τ ⦆)
monC monP τ (idc p) = idc (monP τ p)
monC monP τ (bot t) = subst (Cover _ _ _) ⊥-elim-ext (bot (monNe τ t))
monC monP τ (node t cg ch) = node (monNe τ t) (monC monP (lift τ) cg) (monC monP (lift τ) ch)
  -- REWRITE monD-ne natD

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

-- Empty cover

EmptyCover : (Γ : Cxt) → Set
EmptyCover Γ = Σ (Cover Γ) λ C → ∀{Δ} → Δ ∈ C → ⊥

-- Empty cover is isomorphic to a witness of inconsistency

toEmptyCover : ∀{Γ} (t : Ne Γ False) → EmptyCover Γ
toEmptyCover t = bot t , λ()

fromEmptyCover : ∀{Γ} (ec : EmptyCover Γ) → Nf Γ False
fromEmptyCover (C , f) = reifyF C f
  where
  reifyF : ∀ {Γ} (C : Cover Γ) (f : ∀ {Δ} → Δ ∈ C → ⊥) → Nf Γ False
  reifyF idc          f = ⊥-elim (f here)
  reifyF (bot t)      f = ne t
  reifyF (node t C D) f = orE t (reifyF C (f ∘ left)) (reifyF D (f ∘ right))

transE : ∀{Γ} (C : Cover Γ) (f : ∀{Δ} → Δ ∈ C → EmptyCover Δ) → EmptyCover Γ
transE C f = transC C (proj₁ ∘ f) , λ e → let _ , e₁ , e₂ = split∈ C (proj₁ ∘ f) e in f e₁ .proj₂ e₂

-- Syntactic paste (from Thorsten)

paste' : ∀{A Γ} (C : Cover Γ) (f : ∀{Δ} (e : Δ ∈ C) → Nf Δ A) → Nf Γ A
paste' idc          f = f here
paste' (bot t)      f = falseE t
paste' (node t C D) f = orE t (paste' C (f ∘ left)) (paste' D (f ∘ right))
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

data Disj A B Γ (⟦A⟧ : Fun Γ A → Set) (⟦B⟧ : Fun Γ B → Set) : Fun Γ (A ∨ B) → Set where
  left  : {g : Fun Γ A} (⟦g⟧ : ⟦A⟧ g) → Disj _ _ _ _ _ (inj₁ ∘ g)
  right : {h : Fun Γ B} (⟦h⟧ : ⟦B⟧ h) → Disj _ _ _ _ _ (inj₂ ∘ h)

-- The Beth model

T⟦_⟧ : (A : Form) (Γ : Cxt) (f : Fun Γ A) → Set
T⟦ Atom P ⟧ Γ = NfImg Γ (Atom P)
T⟦ True ⟧ Γ _ = ⊤
T⟦ False ⟧ Γ = Cover False Γ (λ _ _ → ⊥)
T⟦ A ∨ B ⟧ Γ = Cover (A ∨ B) Γ λ Δ f → Disj A B Δ (T⟦ A ⟧ Δ) (T⟦ B ⟧ Δ) f
-- T⟦ A ∨ B ⟧ Γ = Cover (A ∨ B) Γ λ Δ f →
--   (∃ λ (g : Fun Δ A) → f ≡ inj₁ ∘ g × T⟦ A ⟧ Δ g) ⊎
--   (∃ λ (h : Fun Δ B) → f ≡ inj₂ ∘ h × T⟦ B ⟧ Δ h)
T⟦ A ∧ B ⟧ Γ f = T⟦ A ⟧ Γ (proj₁ ∘ f) × T⟦ B ⟧ Γ (proj₂ ∘ f)
T⟦ A ⇒ B ⟧ Γ f = ∀{Δ} (τ : Δ ≤ Γ) {a : Fun Δ A} (⟦a⟧ : T⟦ A ⟧ Δ a) → T⟦ B ⟧ Δ (kapp {A = A} {B = B} f τ a)


monT : ∀ A → Mon T⟦ A ⟧
   -- {Γ Δ} {f : Fun Γ A} (τ : Δ ≤ Γ) → T⟦ A ⟧ Γ f → T⟦ A ⟧ Δ (f ∘ R⦅ τ ⦆)
monT (Atom P) τ = monNfImg τ
monT True τ _ = _
monT False τ = monC (λ _ ()) τ
monT (A ∨ B) {Γ} {Δ} τ = monC {!!} τ
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
{-
-- Reflection / reification

mutual

  reflect : ∀{Γ} A {f} (t : NeImg Γ A f) → T⟦ A ⟧ Γ f
  reflect (Atom P) t = iNe t
  reflect True t = _
  reflect False = toEmptyCover ∘ proj₁
  reflect (A ∨ B) t = {! node t idc idc , aux !}
{-
    where
    aux : ∀{Δ} → Δ ∈ node t idc idc → T⟦ A ⟧ Δ ⊎ T⟦ B ⟧ Δ
    aux (left  here) = inj₁ (reflect A (hyp top))
    aux (right here) = inj₂ (reflect B (hyp top))
-}
  reflect (A ∧ B) t = reflect A (iAndE₁ t) , reflect B (iAndE₂ t)
  reflect (A ⇒ B) t τ a = reflect B (iImpE (monNeImg τ t) (reify A a))

  reify : ∀{Γ} A {f} (⟦f⟧ : T⟦ A ⟧ Γ f) → NfImg Γ A f
  reify (Atom P) t      = t
  reify True _          = iTrueI
  reify False {f} cov   = fromEmptyCover cov , funExt (⊥-elim ∘ f)
  reify (A ∨ B) (C , f) = {! paste' C ([ orI₁ ∘ reify A , orI₂ ∘ reify B ] ∘ f) !}
  reify (A ∧ B) (a , b) = iAndI (reify A a) (reify B b)
  reify (A ⇒ B) ⟦f⟧     = iImpI (reify B (⟦f⟧ (weak id≤) (reflect A (iHyp top))))

-- Semantic paste

paste : ∀ A {Γ f} (C : Cover Γ) (tr : ∀{Δ} (e : Δ ∈ C) → T⟦ A ⟧ Δ (f ∘ E⦅ e ⦆)) → T⟦ A ⟧ Γ f
paste (Atom P) = {! paste' !}
paste True C f = _
paste False C f = transE C f
paste (A ∨ B) C f = transC C (proj₁ ∘ f) , λ e → let _ , e₁ , e₂ = split∈ C (proj₁ ∘ f) e in {! f e₁ .proj₂ e₂ !}
paste (A ∧ B) C f = paste A C (proj₁ ∘ f) , paste B C (proj₂ ∘ f)
paste (A ⇒ B) C f τ a = paste B (monC τ C) λ {Δ} e → let Ψ , e' , σ  = mon∈ C τ e in {! f e' σ (monT A (coverWk e) a) !}

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
-- A lemma for the falseE case

falseElim : ∀{Γ A f} (C : Cover Γ) (tr : ∀{Δ} → Δ ∈ C → ⊥) → T⟦ A ⟧ Γ f
falseElim {Γ} {A} C tr = paste A C (⊥-elim ∘ tr)

-- The fundamental theorem

fund :  ∀{Γ A} (t : Γ ⊢ A) {Δ ρ} (γ : G⟦ Γ ⟧ Δ ρ) → T⟦ A ⟧ Δ (D⦅ t ⦆ ∘ ρ)
fund (hyp x) = fundH x
fund (impI t) γ τ a = fund t (monG τ γ , a)
fund (impE t u) γ = fund t γ id≤ (fund u γ)
fund (andI t u) γ = fund t γ , fund u γ
fund (andE₁ t) = proj₁ ∘ fund t
fund (andE₂ t) = proj₂ ∘ fund t
fund (orI₁ t) γ = {! idc , inj₁ ∘ λ{ here → fund t γ } !}
fund (orI₂ t) γ = {! idc , inj₂ ∘ λ{ here → fund t γ } !}
fund (orE t u v) γ = uncurry {! orElim !} (fund t γ)
  (λ τ a → fund u (monG τ γ , a))
  (λ τ b → fund v (monG τ γ , b))
fund {A = A} (falseE t) γ = uncurry (falseElim {A = A}) (fund t γ)
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
