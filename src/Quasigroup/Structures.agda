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
open import Quasigroup.Definitions _≈_

record IsPique (_∙_ : Op₂ A) (ε : A) (⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isQuasigroup : IsQuasigroup _∙_  ε ⁻¹
    idem         : Idempotent _∙_

  open IsQuasigroup isQuasigroup public 

record IsQuasiGroup (* |ᵇ |ᶠ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isEquivalence            : IsEquivalence _≈_
    *-quasigroupIdentity₁-|ᵇ : * QuasigroupIdentity₁ |ᵇ
    *-quasigroupIdentity₂-|ᵇ : * QuasigroupIdentity₂ |ᵇ
    *-quasigroupIdentity₃-|ᶠ : * QuasigroupIdentity₃ |ᶠ
    *-quasigroupIdentity₄-|ᶠ : * QuasigroupIdentity₄ |ᶠ

  open IsEquivalence isEquivalence public
