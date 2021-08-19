{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Morphism.Structure where

open import Algebra.Core
open import Algebra.Bundles
import Algebra.Morphism.Definitions as MorphismDefinitions
open import Level using (Level; _⊔_)
import Function.Definitions as FunctionDefinitions
open import Relation.Binary.Morphism.Structures
open import Quasigroup.Bundles

private
  variable
    a b ℓ₁ ℓ₂ : Level

module QuasigroupMorphisms (Q₁ : RawQuasigroup a ℓ₁) (Q₂ : RawQuasigroup b ℓ₂) where

  open RawQuasigroup Q₁ renaming (Carrier to A; _≈_ to _≈₁_; _∙_ to _∙_)
  open RawQuasigroup Q₂ renaming (Carrier to B; _≈_ to _≈₂_; _∙_ to _◦_)
  open MorphismDefinitions A B _≈₂_
  open FunctionDefinitions _≈₁_ _≈₂_

  record IsQuasigroupHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
      homo              : Homomorphic₂ ⟦_⟧ _∙_ _◦_

    open IsRelHomomorphism isRelHomomorphism public
      renaming (cong to ⟦⟧-cong)
