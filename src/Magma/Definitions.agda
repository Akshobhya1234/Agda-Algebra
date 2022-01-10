{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Magma.Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  where

open import Algebra.Core
open import Data.Product

Alternativeˡ : Op₂ A → Set _
Alternativeˡ _∙_ = ∀ x y  →  ((x ∙ x) ∙ y) ≈ (x ∙ (y ∙ y))

Alternativeʳ : Op₂ A → Set _
Alternativeʳ _∙_ = ∀ x y → (x ∙ (y ∙ y)) ≈ ((x ∙ y) ∙ y)

Alternative : Op₂ A → Set _
Alternative _∙_ = (Alternativeˡ _∙_ ) × ( Alternativeʳ _∙_)

Flexible : Op₂ A → Set _
Flexible _∙_ = ∀ x y → ((x ∙ y) ∙ x) ≈ (x ∙ (y ∙ x))

Medial : Op₂ A → Set _
Medial _∙_ = ∀ x y u z → ((x ∙ y) ∙ (u ∙ z)) ≈ ((x ∙ u) ∙ (y ∙ z))

LeftSemimedial : Op₂ A → Set _
LeftSemimedial _∙_ = ∀ x y z → ((x ∙ x) ∙ (y ∙ z)) ≈ ((x ∙ y) ∙ (x ∙ z))

RightSemimedial : Op₂ A → Set _
RightSemimedial _∙_ = ∀ x y z → ((y ∙ z) ∙ (x ∙ x)) ≈ ((y ∙ x) ∙ (z ∙ x))

Semimedial : Op₂ A → Set _
Semimedial _∙_ = (LeftSemimedial _∙_) × (RightSemimedial _∙_)
