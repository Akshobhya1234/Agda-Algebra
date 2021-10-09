{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Quasigroup.Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  where
  
open import Algebra.Core
open import Data.Product

_LeftDivisionˡ_ : Op₂ A → Op₂ A → Set _
_*_ LeftDivisionˡ _\\_ = ∀ x y → (x * (x \\ y)) ≈ y

_LeftDivisionʳ_ : Op₂ A → Op₂ A → Set _
_*_ LeftDivisionʳ _\\_ = ∀ x y → (x \\ (x * y)) ≈ y

_RightDivisionˡ_ : Op₂ A → Op₂ A → Set _
_*_ RightDivisionˡ _//_ = ∀ x y → ((y // x) * x) ≈ y

_RightDivisionʳ_ : Op₂ A → Op₂ A → Set _
_*_ RightDivisionʳ _//_ = ∀ x y → ((y * x) // x) ≈ y

LatinSquareProperty₁ : Op₂ A → Set _
LatinSquareProperty₁ _*_ = ∀ a b x  → (a * x) ≈ b 

LatinSquareProperty₂ : Op₂ A → Set _
LatinSquareProperty₂ _*_ = ∀ a b y → (y * a) ≈ b

LatinSquareProperty : Op₂ A → Set _
LatinSquareProperty _*_ = (LatinSquareProperty₁ _*_) × (LatinSquareProperty₂ _*_)
