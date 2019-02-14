{-# OPTIONS --postfix-projections #-}
module PresheavesAndSheaves where

open import Library hiding (refl; trans; _∈_)

open import Level
import Relation.Binary.Core as Eq
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.PropositionalEquality.Core as Eq
open import Function.Inverse using (_↔_; module Inverse)
open import Function.Equality using (_⟨$⟩_)

module _ {A : Set} {B : Set} (e : A ↔ B) where
  open Inverse e

  –> : A → B
  –> a = to ⟨$⟩ a

  <– : B → A
  <– b = from ⟨$⟩ b

record Poset : Set₁ where
  field
    A : Set
    _≤_ : (x y : A) → Set
    refl : {x : A} → x ≤ x
    trans : {x y z : A} (p : x ≤ y) (q : y ≤ z) → x ≤ z

record Poset₁ : Set₂ where
  field
    A : Set₁
    _≤_ : (x y : A) → Set
    refl : {x : A} → x ≤ x
    trans : {x y z : A} (p : x ≤ y) (q : y ≤ z) → x ≤ z

module _ {P : Poset} where
  open Poset P

  record IsMeet (x y z : A) : Set where
    field
      π₁ : z ≤ x
      π₂ : z ≤ y
      univ : (a : A) (e₁ : a ≤ x) (e₂ : a ≤ y) → a ≤ z

record Coverage (P : Poset) : Set₁ where
  open Poset P

  field
    Cover : A → Set
    _∈_ : {a : A} (b : A) (C : Cover a) → Set
    ∈-≤ : {a b : A} {C : Cover a} → b ∈ C → b ≤ a

    weaken : {a b : A} (σ : b ≤ a) (C : Cover a) → Cover b
    weaken-ext : {a b : A} {σ : b ≤ a} {C : Cover a} → Σ A (λ x → x ∈ C) ↔ Σ A (λ y → y ∈ weaken σ C)
    weaken-ext-meet : {a b : A} {σ : b ≤ a} {C : Cover a} {x : A} {e : x ∈ C} → IsMeet {P} a x (proj₁ (–> (weaken-ext {σ = σ}) (x , e)))

    singleton : {a : A} → Cover a
    singleton-ext : {a b : A} → b ∈ singleton {a} ↔ b Eq.≡ a

    paste : {a : A} (C : Cover a) (D : (b : A) → b ∈ C → Cover b) → Cover a
    paste-ext : {a : A} {C : Cover a} {D : (b : A) → b ∈ C → Cover b} {c : A} → c ∈ paste C D ↔ ∃ λ b → Σ (b ∈ C) (λ e → c ∈ D b e)

record Presheaf (P : Poset) : Set₁ where
  open Poset P

  field
    ⟦_⟧ : A → Set
    ⟦_⟧-hom : {a b : A} (p : b ≤ a) → ⟦ a ⟧ → ⟦ b ⟧

module _ {P : Poset} where
  open Poset P

  PresheafPoset : Poset₁
  PresheafPoset .Poset₁.A = Presheaf P
  PresheafPoset .Poset₁._≤_ F G = {a : A} → F.⟦ a ⟧ → G.⟦ a ⟧ where
    module F = Presheaf F
    module G = Presheaf G
  PresheafPoset .Poset₁.refl = Library.id
  PresheafPoset .Poset₁.trans f g = g ∘ f

  open Poset₁ PresheafPoset using () renaming (refl to reflᵖ; trans to transᵖ) public
  infix 4 _≤ᵖ_
  _≤ᵖ_ = Poset₁._≤_ PresheafPoset

module PresheafFormers {P : Poset} where
  open Poset P
  open Presheaf

  True : Presheaf P
  True .⟦_⟧ a = ⊤
  ⟦ True ⟧-hom p ⊤.tt = ⊤.tt

  True-in : {H : Presheaf P} → H ≤ᵖ True
  True-in _ = ⊤.tt

  False : Presheaf P
  False .⟦_⟧ a = ⊥
  ⟦ False ⟧-hom p ()

  False-out : {H : Presheaf P} → False ≤ᵖ H
  False-out = ⊥-elim

  module _ (F G : Presheaf P) where
    private module F = Presheaf F
    private module G = Presheaf G

    infix 10 _∧_

    _∧_ : Presheaf P
    _∧_ .⟦_⟧ a = F.⟦ a ⟧ × G.⟦ a ⟧
    _∧_ .⟦_⟧-hom p = map-× (F.⟦_⟧-hom p) (G.⟦_⟧-hom p)

  ∧-in : ∀ {F G H} → H ≤ᵖ F → H ≤ᵖ G → H ≤ᵖ F ∧ G
  ∧-in u v x = (u x , v x)

  ∧-out₁ : ∀ {F G} → F ∧ G ≤ᵖ F
  ∧-out₁ = proj₁

  ∧-out₂ : ∀ {F G} → F ∧ G ≤ᵖ G
  ∧-out₂ = proj₂

  module _ (F G : Presheaf P) where
    private module F = Presheaf F
    private module G = Presheaf G

    infix 9 _∨_

    _∨_ : Presheaf P
    _∨_ .⟦_⟧ a = F.⟦ a ⟧ ⊎ G.⟦ a ⟧
    _∨_ .⟦_⟧-hom p = map-⊎ (F.⟦_⟧-hom p) (G.⟦_⟧-hom p)

  ∨-in₁ : ∀ {F G} → F ≤ᵖ F ∨ G
  ∨-in₁ = inj₁

  ∨-in₂ : ∀ {F G} → G ≤ᵖ F ∨ G
  ∨-in₂ = inj₂

  ∨-out : ∀ {F G H} → F ≤ᵖ H → G ≤ᵖ H → F ∨ G  ≤ᵖ H
  ∨-out u v = [ u , v ]

  module _ (F G : Presheaf P) where
    private module F = Presheaf F
    private module G = Presheaf G

    infix 8 _⇒_

    _⇒_ : Presheaf P
    _⇒_ .⟦_⟧ a = (a' : A) (p : a' ≤ a) (x : F.⟦ a' ⟧) → G.⟦ a' ⟧
    _⇒_ .⟦_⟧-hom {a} {b} p fa b' q y = fa b' (trans q p) y

  ⇒-in : ∀ {F G H} → H ∧ F ≤ᵖ G → H ≤ᵖ F ⇒ G
  ⇒-in {H = H} u x a' p y = u (H.⟦ p ⟧-hom x , y) where
    module H = Presheaf H

  ⇒-out : ∀ {F G H} → H ≤ᵖ F ⇒ G → H ∧ F ≤ᵖ G
  ⇒-out f (x , y) = f x _ refl y

  module Fund (H : Presheaf P) where
    private module H = Presheaf H

    trueI : H ≤ᵖ True
    trueI x = ⊤.tt

    falseE : ∀ {M} → False ≤ᵖ M
    falseE = ⊥-elim

    andE₁ : ∀ {F G} → H ≤ᵖ F ∧ G → H ≤ᵖ F
    andE₁ t x = proj₁ (t x)

    andE₂ : ∀ {F G} → H ≤ᵖ F ∧ G → H ≤ᵖ G
    andE₂ t x = proj₂ (t x)

    orI₁ : ∀ {F G} → H ≤ᵖ F → H ≤ᵖ F ∨ G
    orI₁ t x = inj₁ (t x)

    orI₂ : ∀ {F G} → H ≤ᵖ G → H ≤ᵖ F ∨ G
    orI₂ t x = inj₂ (t x)

    impI : ∀ {F G} → H ∧ F ≤ᵖ G → H ≤ᵖ F ⇒ G
    impI u x a' p y = u (H.⟦ p ⟧-hom x , y)

    impE : ∀ {F G} → H ≤ᵖ F ⇒ G → H ≤ᵖ F → H ≤ᵖ G
    impE f u x = f x _ refl (u x)

module _ {P : Poset} where
  open Poset P

  module _ where
    open Presheaf

    yoneda : A → Presheaf P
    yoneda a .⟦_⟧ b = b ≤ a
    yoneda a .⟦_⟧-hom = trans

  record Sheaf (coverage : Coverage P) : Set₁ where
    open Coverage coverage

    field
      presheaf : Presheaf P
    open Presheaf presheaf public
    field
      glue : {a : A} (C : Cover a) → ({b : A} → b ∈ C → ⟦ b ⟧) → ⟦ a ⟧

  infix 20 _ᵖ

  _ᵖ : {coverage : Coverage P} → Sheaf coverage → Presheaf P
  _ᵖ = Sheaf.presheaf

  module _ {coverage : Coverage P} where
    open Coverage coverage

    SheafPoset : Poset₁
    SheafPoset .Poset₁.A = Sheaf coverage
    SheafPoset .Poset₁._≤_ F G = F ᵖ ≤ᵖ G ᵖ
    SheafPoset .Poset₁.refl {F} = reflᵖ {P} {F ᵖ}
    SheafPoset .Poset₁.trans {F} {G} {H} = transᵖ {P} {F ᵖ} {G ᵖ} {H ᵖ}

    open Poset₁ SheafPoset using () renaming (refl to reflˢ; trans to transˢ) public
    infix 4 _≤ˢ_
    _≤ˢ_ = Poset₁._≤_ SheafPoset

  module Sheafification {coverage : Coverage P} where
    open Coverage coverage

    module _ where
      open Sheaf

      sheafify : Presheaf P → Sheaf coverage
      sheafify F = G where
        private module F = Presheaf F
        open Presheaf

        G : Sheaf coverage
        G .presheaf .⟦_⟧ a = Σ (Cover a) λ C → {x : A} (e : x ∈ C) → F.⟦ x ⟧
        -- I don't like to use 'with'
        G .presheaf .⟦_⟧-hom p (C , h) = (weaken p C , help) where
          help : {x' : A} (e' : x' ∈ weaken p C) → F.⟦ x' ⟧
          help {x'} e' = F.⟦ q ⟧-hom (h e) where
            open Σ (<– weaken-ext (x' , e')) renaming (proj₁ to x; proj₂ to e)

            q : x' ≤ x
            q = Eq.subst (λ z → z .proj₁ ≤ x) (Inverse.right-inverse-of weaken-ext (x' , e')) (weaken-ext-meet {e = e} .IsMeet.π₂)
        G .glue C h .proj₁ = paste C λ b e → h e .proj₁
        -- I don't like to use 'with'
        G .glue C h .proj₂ e = h e' .proj₂ q where
          open Σ (–> paste-ext e) renaming (proj₁ to b; proj₂ to e',q)
          open Σ e',q renaming (proj₁ to e'; proj₂ to q)

    η : {F : Presheaf P} → F ≤ᵖ sheafify F ᵖ
    η x .proj₁ = singleton
    η {F} x .proj₂ e = Eq.subst ⟦_⟧ (Eq.sym (–> singleton-ext e)) x where
      open Presheaf F

    univ-prop : {F : Presheaf P} {G : Sheaf coverage} (u : F ≤ᵖ G ᵖ) → sheafify F ᵖ ≤ᵖ G ᵖ
    univ-prop {F} {G} u (C , h) = glue C (u ∘ h) where
      open Sheaf G
      module F = Presheaf F
      module G = Presheaf presheaf

  module SheafFormers {coverage : Coverage P} where
    open Coverage coverage
    open Sheaf

    module PF = PresheafFormers
    open Sheafification {coverage = coverage}

    True : Sheaf coverage
    True .presheaf = PF.True
    True .glue _ _ = ⊤.tt

    True-in : {H : Sheaf coverage} → H ≤ˢ True
    True-in _ = ⊤.tt

    False : Sheaf coverage
    False = sheafify PF.False

    False-out : {H : Sheaf coverage} → False ≤ˢ H
    False-out {H} = univ-prop {F = PF.False} {G = H} (PF.False-out {H = H ᵖ})

    module _ (F G : Sheaf coverage) where
      private module F = Sheaf F
      private module G = Sheaf G

      infix 10 _∧_

      _∧_ : Sheaf coverage
      _∧_ .presheaf = F.presheaf PF.∧ G.presheaf
      _∧_ .glue C h = (F.glue C (proj₁ ∘ h) , G.glue C (proj₂ ∘ h))

    ∧-in : ∀ {F G H} → H ≤ˢ F → H ≤ˢ G → H ≤ˢ F ∧ G
    ∧-in {F} {G} {H} = PF.∧-in {F = F ᵖ} {G = G ᵖ} {H = H ᵖ}

    ∧-out₁ : ∀ {F G} → F ∧ G ≤ˢ F
    ∧-out₁ {F} {G} = PF.∧-out₁ {F = F ᵖ} {G = G ᵖ}

    ∧-out₂ : ∀ {F G} → F ∧ G ≤ˢ G
    ∧-out₂ {F} {G} = PF.∧-out₂ {F = F ᵖ} {G = G ᵖ}

    module _ (F G : Sheaf coverage) where
      private module F = Sheaf F
      private module G = Sheaf G

      infix 9 _∨_

      _∨_ : Sheaf coverage
      _∨_ = sheafify (F.presheaf PF.∨ G.presheaf)

    ∨-in₁ : ∀ {F G} → F ≤ˢ F ∨ G
    ∨-in₁ {F} {G} = transᵖ {x = F ᵖ} {y = F ᵖ PF.∨ G ᵖ} {z = (F ∨ G) ᵖ} (PF.∨-in₁ {F = F ᵖ} {G = G ᵖ}) (η {F = F ᵖ PF.∨ G ᵖ})

    ∨-in₂ : ∀ {F G} → G ≤ˢ F ∨ G
    ∨-in₂ {F} {G} = transᵖ {x = G ᵖ} {y = F ᵖ PF.∨ G ᵖ} {z = (F ∨ G) ᵖ} (PF.∨-in₂ {F = F ᵖ} {G = G ᵖ}) (η {F = F ᵖ PF.∨ G ᵖ})

    ∨-out : ∀ {F G H} → F ≤ˢ H → G ≤ˢ H → F ∨ G ≤ˢ H
    ∨-out {F} {G} {H} u v = univ-prop {F = F ᵖ PF.∨ G ᵖ} {G = H} (PF.∨-out {F = F ᵖ} {G = G ᵖ} {H = H ᵖ} u v)

    module _ (F G : Sheaf coverage) where
      private module F = Sheaf F
      private module G = Sheaf G

      infix 8 _⇒_

      _⇒_ : Sheaf coverage
      _⇒_ .presheaf = F.presheaf PF.⇒ G.presheaf
      _⇒_ .glue {a} C h a' p x = G.glue (weaken p C) help where
        help : {b' : A} → b' ∈ weaken p C → G.⟦ b' ⟧
        help {b'} e' = k (F.⟦ ∈-≤ e' ⟧-hom x) where
          open Σ (<– weaken-ext (b' , e')) renaming (proj₁ to b; proj₂ to e)

          k : F.⟦ b' ⟧ → G.⟦ b' ⟧
          k = h e b' (Eq.subst (λ z → z .proj₁ ≤ b) (Inverse.right-inverse-of weaken-ext (b' , e')) (weaken-ext-meet {σ = p} {C = C} {x = b} {e = e} .IsMeet.π₂))

    ⇒-in : ∀ {F G H} → H ∧ F ≤ˢ G → H ≤ˢ F ⇒ G
    ⇒-in {F} {G} {H} = PF.⇒-in {F = F ᵖ} {G = G ᵖ} {H = H ᵖ}

    ⇒-out : ∀ {F G H} → H ≤ˢ F ⇒ G → H ∧ F ≤ˢ G
    ⇒-out {F} {G} {H} = PF.⇒-out {F = F ᵖ} {G = G ᵖ} {H = H ᵖ}
