{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Loop.Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  where
  
open import Algebra.Core


LeftBol : Op₂ A → Set _
LeftBol _∙_ = ∀ x y z → (x ∙ (y ∙ (x ∙ z))) ≈ ((x ∙ (y ∙ z)) ∙ z )

RightBol : Op₂ A → Set _
RightBol _∙_ = ∀ x y z → (((z ∙ x) ∙ y) ∙ x) ≈ (z ∙ ((x ∙ y) ∙ x))
