{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Quasigroup.Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  where

open import Algebra.Core
open import Data.Product

LatinSquareProperty₁ : Op₂ A → Set _
LatinSquareProperty₁ _*_ = ∀ a b x  → (a * x) ≈ b

LatinSquareProperty₂ : Op₂ A → Set _
LatinSquareProperty₂ _*_ = ∀ a b y → (y * a) ≈ b

LatinSquareProperty : Op₂ A → Set _
LatinSquareProperty _*_ = (LatinSquareProperty₁ _*_) × (LatinSquareProperty₂ _*_)
