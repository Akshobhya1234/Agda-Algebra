{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Loop.Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  where
  
open import Algebra.Core
open import Data.Product

LeftBol : Op₂ A → Set _
LeftBol _∙_ = ∀ x y z → (x ∙ (y ∙ (x ∙ z))) ≈ ((x ∙ (y ∙ z)) ∙ z )

RightBol : Op₂ A → Set _
RightBol _∙_ = ∀ x y z → (((z ∙ x) ∙ y) ∙ x) ≈ (z ∙ ((x ∙ y) ∙ x))

MoufangIdentity₁ : Op₂ A → Set _
MoufangIdentity₁  _∙_  = ∀ x y z → (z ∙ (x ∙ (z ∙ y))) ≈ (((z ∙ x) ∙ z) ∙ y)

MoufangIdentity₂ : Op₂ A → Set _
MoufangIdentity₂ _∙_ = ∀ x y z → (x ∙ (z ∙ (y ∙ z))) ≈ (((x ∙ z) ∙ y) ∙ z)

MoufangIdentity₃ : Op₂ A → Set _
MoufangIdentity₃ _∙_ = ∀ x y z → ((z ∙ x) ∙ (y ∙ z)) ≈ ((z ∙ (x ∙ y)) ∙ z)

MoufangIdentity₄ : Op₂ A → Set _
MoufangIdentity₄ _∙_ = ∀ x y z → ((z ∙ x) ∙ (y ∙ z)) ≈ (z ∙ ((x ∙ y) ∙ z))

MoufangIdentity : Op₂ A → Set _
MoufangIdentity _∙_ = (MoufangIdentity₁ _∙_) × (MoufangIdentity₂ _∙_) × (MoufangIdentity₃ _∙_) × (MoufangIdentity₄ _∙_)
