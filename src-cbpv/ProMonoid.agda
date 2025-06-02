{-# OPTIONS --without-K #-}

module ProMonoid where

open import Level
open import Algebra.Core using (Op₂)
open import Algebra.Definitions using (Congruent₂)
open import Algebra.Structures
open import Algebra.Bundles
open import Relation.Binary

-- Pre-ordered monoids, additively written

record ProMonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≼_
  infixl 7 _∙_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.

    _≼_        : Rel Carrier ℓ₂  -- The relation.
    isPreorder : IsPreorder _≈_ _≼_

    _∙_        : Op₂ Carrier     -- The monoid operations.
    ε          : Carrier
    isMonoid   : IsMonoid _≈_ _∙_ ε

    ∙-mon      : Congruent₂ _≼_ _∙_

  open IsPreorder isPreorder public
    hiding (module Eq)

  module Eq where
    setoid : Setoid c ℓ₁
    setoid = record { isEquivalence = isEquivalence }

    open Setoid setoid public

  monoid : Monoid c ℓ₁
  monoid = record { isMonoid = isMonoid }

  open IsMonoid isMonoid public -- using (∙-cong)
    hiding (reflexive; refl)
