{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Quasigroup.Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  where

open import Algebra.Core
open import Data.Product

LatinSquare₁ : Op₂ A → Set _
LatinSquare₁ _*_ = ∀ a b x  → (a * x) ≈ b

LatinSquare₂ : Op₂ A → Set _
LatinSquare₂ _*_ = ∀ a b y → (y * a) ≈ b

LatinSquare : Op₂ A → Set _
LatinSquare _*_ = (LatinSquare₁ _*_) × (LatinSquare₂ _*_)
