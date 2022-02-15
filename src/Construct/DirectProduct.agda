{-# OPTIONS --without-K --safe #-}

open import Algebra.Construct.DirectProduct

module Construct.DirectProduct where

open import Algebra.Bundles
import Algebra.Construct.DirectProduct as DirectProduct
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Level using (Level; _⊔_)

private
  variable
    a b ℓ₁ ℓ₂ : Level

