{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Morphism.Structures where

open import Algebra
import Algebra.Morphism.Definitions as MorphismDefinitions
open import Level using (Level; _⊔_)
import Function.Definitions as FunctionDefinitions
open import Relation.Binary.Morphism.Structures
open import Quasigroup
open import Loop
open import Algebra.Morphism.Structures hiding (IsMagmaHomomorphism)

private
  variable
    a b ℓ₁ ℓ₂ : Level

module QuasigroupMorphisms (Q₁ : RawQuasigroup a ℓ₁) (Q₂ : RawQuasigroup b ℓ₂) where

  open RawQuasigroup Q₁ renaming (Carrier to A; _≈_ to _≈₁_; _∙_ to _∙_; _⁻¹ to _⁻¹₁; ε to ε₁)
  open RawQuasigroup Q₂ renaming (Carrier to B; _≈_ to _≈₂_; _∙_ to _◦_; _⁻¹ to _⁻¹₂; ε to ε₂)
  open MorphismDefinitions A B _≈₂_
  open FunctionDefinitions _≈₁_ _≈₂_
  open MagmaMorphisms  (RawQuasigroup.rawMagma  Q₁) (RawQuasigroup.rawMagma  Q₂)

  record IsQuasigroupHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMagmaHomomorphism : IsMagmaHomomorphism ⟦_⟧
      ⁻¹-homo              : Homomorphic₁ ⟦_⟧ _⁻¹₁ _⁻¹₂

    open IsMagmaHomomorphism isMagmaHomomorphism public

module LoopMorphisms (L₁ : RawLoop a ℓ₁) (L₂ : RawLoop b ℓ₂) where

  open RawLoop L₁ renaming (Carrier to A; _≈_ to _≈₁_; _∙_ to _∙_; _⁻¹ to _⁻¹₁; ε to ε₁)
  open RawLoop L₂ renaming (Carrier to B; _≈_ to _≈₂_; _∙_ to _◦_; _⁻¹ to _⁻¹₂; ε to ε₂)
  open MorphismDefinitions A B _≈₂_
  open FunctionDefinitions _≈₁_ _≈₂_
  open MagmaMorphisms  (RawLoop.rawMagma  L₁) (RawLoop.rawMagma  L₂)

  record IsLoopHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMagmaHomomorphism : IsMagmaHomomorphism ⟦_⟧
      ⁻¹-homo              : Homomorphic₁ ⟦_⟧ _⁻¹₁ _⁻¹₂

    open IsMagmaHomomorphism isMagmaHomomorphism public
