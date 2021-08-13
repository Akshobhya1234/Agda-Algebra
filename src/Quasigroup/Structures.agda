{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid; IsEquivalence)
module Quasigroup.Structures
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Algebra.Core
open import Level using (_⊔_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_

record IsPique (_∙_ : Op₂ A) (ε : A) (⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isQuasigroup : IsQuasigroup _∙_  ε ⁻¹
    idem         : Idempotent _∙_
