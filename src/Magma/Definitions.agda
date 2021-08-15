{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Magma.Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  where
  
open import Algebra.Core
open import Data.Product

_Alternativeˡ_ : Op₂ A → Op₂ A → Set _
_*_ Alternativeˡ _+_ = ∀ x y  →  ((x + x) * y) ≈ (x * (y + y))

_Alternativeʳ_ : Op₂ A → Op₂ A → Set _
_*_ Alternativeʳ _+_ = ∀ x y → (x * (y + y)) ≈ ((x + y) * y)

_Alternative_ : Op₂ A → Op₂ A → Set _
* Alternative + = (* Alternativeˡ +) × (* Alternativeʳ +)
