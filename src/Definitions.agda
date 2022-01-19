{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  where

open import Algebra.Core
open import Data.Product
open import Algebra.Definitions

-- (x²y)x = x²(yx)
JordanIdentity: : Op₂ A → Set _
JordanIdentity: _∙_ = ∀ x y → (((x ∙ x) ∙ y) ∙ x) ≈ (((x ∙ x) ∙ y) ∙ x)

-- x = xyx
PesudoInverse₁ : Op₂ A → Set _
PesudoInverse₁ _∙_ = ∀ x y → ((x ∙ y) ∙ x) ≈ x

-- y = yxy
PseudoInverse₂ : Op₂ A → Set _
PseudoInverse₂ _∙_ = ∀ x y → ((y ∙ x) ∙ y) ≈ y

PseudoInverse : Op₂ A → Set _
PseudoInverse ∙ = (PesudoInverse₁ ∙) × (PseudoInverse₂ ∙)

-- JacobiIdentity is (x ∙ (y ∙ z)) + ((y ∙ (z ∙ x)) + (z ∙ (x ∙ y))) = 0
-- Using the antisymmetry property Jacobi identity may be rewritten as a modification of the associative property

JacobiIdentity : Op₂ A → Op₂ A → Set _
JacobiIdentity _∙_  _-_ = ∀ x y z → (x ∙ (y ∙ z)) ≈ ((y ∙ (z ∙ x)) - (z ∙ (x ∙ y)))
