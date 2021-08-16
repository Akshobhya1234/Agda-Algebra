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
