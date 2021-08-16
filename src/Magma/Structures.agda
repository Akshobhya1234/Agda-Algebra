{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid; IsEquivalence)
module Magma.Structures
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Algebra.Core
open import Level using (_⊔_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_
open import Magma.Definitions  _≈_

record IsIdempotentMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    idem    : Idempotent ∙

  open IsMagma isMagma public

record IsAlternateMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma  : IsMagma ∙ 
    alter    : Alternative ∙

  open IsMagma isMagma public

record IsFlexibleMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma  : IsMagma ∙ 
    flex     : Flexible ∙

  open IsMagma isMagma public
