{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  where

open import Algebra.Core
open import Data.Product
open import Algebra.Definitions

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

LatinSquare₁ : Op₂ A → Set _
LatinSquare₁ _*_ = ∀ a b x  → (a * x) ≈ b

LatinSquare₂ : Op₂ A → Set _
LatinSquare₂ _*_ = ∀ a b y → (y * a) ≈ b

LatinSquare : Op₂ A → Set _
LatinSquare _*_ = (LatinSquare₁ _*_) × (LatinSquare₂ _*_)

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
