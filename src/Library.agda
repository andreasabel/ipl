-- Interface to the standard library.
-- Place to add own auxiliary definitions.

module Library where

open import Data.Unit    public using (⊤)
open import Data.Empty   public using (⊥; ⊥-elim)
open import Data.Product public using (Σ; ∃; _×_; _,_; proj₁; proj₂; <_,_>; curry; uncurry)
open import Data.Sum     public using (_⊎_; inj₁; inj₂; [_,_]) renaming (map to map-⊎)
open import Function     public using (_∘_; id)
