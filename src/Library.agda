{-# OPTIONS --rewriting #-}

-- Interface to the standard library.
-- Place to add own auxiliary definitions.

module Library where

open import Data.Unit    public using (⊤)
open import Data.Empty   public using (⊥; ⊥-elim)
open import Data.Product public using (Σ; ∃; _×_; _,_; proj₁; proj₂; <_,_>; curry; uncurry) renaming (map to map-×)
open import Data.Sum     public using (_⊎_; inj₁; inj₂; [_,_]) renaming (map to map-⊎)
open import Function     public using (_∘_; id)

open import Relation.Binary.PropositionalEquality public using (_≡_; refl; sym; trans; cong; cong₂; subst; Extensionality)
{-# BUILTIN REWRITE _≡_ #-}

postulate funExt : ∀{a b} → Extensionality a b

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {a a' b b' c c'} → a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

_×̇_ : ∀{A B C D : Set} → (A → C) → (B → D) → A × B → C × D
(f ×̇ g) (x , y) = f x , g y

-- Application (S-combinator)

apply : ∀{A B C : Set} (f : C → A → B) (d : C → A) → C → B
apply f a = λ c → f c (a c)

caseof : ∀{A B C D : Set} (f : C → A ⊎ B) (g : C × A → D) (h : C × B → D) → C → D
caseof f g h = λ c → [ curry g c , curry h c ] (f c)
