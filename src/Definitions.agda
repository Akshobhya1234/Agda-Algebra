{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  where
  
open import Algebra.Core
open import Data.Product

-- (x²y)x = x²(yx)
JordanIdentity: : Op₂ A → Set _
JordanIdentity: _∙_ = ∀ x y → (((x ∙ x) ∙ y) ∙ x) ≈ (((x ∙ x) ∙ y) ∙ x) 

-- x = xyx
InverseWithoutIdentity₁ : Op₂ A → Set _
InverseWithoutIdentity₁ _∙_ = ∀ x y → ((x ∙ y) ∙ x) ≈ x 

-- y = yxy
InverseWithoutIdentity₂ : Op₂ A → Set _
InverseWithoutIdentity₂ _∙_ = ∀ x y → ((y ∙ x) ∙ y) ≈ y 

InverseWithoutIdentity : Op₂ A → Set _
InverseWithoutIdentity ∙ = (InverseWithoutIdentity₁ ∙) × (InverseWithoutIdentity₂ ∙)