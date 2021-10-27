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

module QuasiGroupMorphisms (Q₁ : RawQuasiGroup a ℓ₁) (Q₂ : RawQuasiGroup b ℓ₂) where

  open RawQuasiGroup Q₁ renaming (Carrier to A; ∙-rawMagma to ∙-rawMagma₁; \\-rawMagma to \\-rawMagma₁; //-rawMagma to //-rawMagma₁;
                                   _≈_ to _≈₁_; _∙_ to _∙₁_; _\\_ to _\\₁_; _//_ to _//₁_)
  open RawQuasiGroup Q₂ renaming (Carrier to B; ∙-rawMagma to ∙-rawMagma₂; \\-rawMagma to \\-rawMagma₂; //-rawMagma to //-rawMagma₂;  
                                  _≈_ to _≈₂_; _∙_ to _∙₂_; _\\_ to _\\₂_; _//_ to _//₂_)

  module ∙ = MagmaMorphisms ∙-rawMagma₁ ∙-rawMagma₂
  module \\ = MagmaMorphisms \\-rawMagma₁ \\-rawMagma₂
  module // = MagmaMorphisms //-rawMagma₁ //-rawMagma₂

  open MorphismDefinitions A B _≈₂_
  open FunctionDefinitions _≈₁_ _≈₂_
 
  record IsQuasiGroupHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
      *-homo            : Homomorphic₂ ⟦_⟧ _∙₁_ _∙₂_   
      \\-homo           : Homomorphic₂ ⟦_⟧ _\\₁_ _\\₂_
      //-homo           : Homomorphic₂ ⟦_⟧ _//₁_ _//₂_

    open IsRelHomomorphism isRelHomomorphism public
      renaming (cong to ⟦⟧-cong)
    
    ∙-isMagmaHomomorphism : ∙.IsMagmaHomomorphism ⟦_⟧
    ∙-isMagmaHomomorphism = record
      { isRelHomomorphism = isRelHomomorphism
      ; homo = *-homo
      }

    \\-isMagmaHomomorphism : \\.IsMagmaHomomorphism ⟦_⟧
    \\-isMagmaHomomorphism = record
      { isRelHomomorphism = isRelHomomorphism
      ; homo = \\-homo
      }
       
    //-isMagmaHomomorphism : //.IsMagmaHomomorphism ⟦_⟧
    //-isMagmaHomomorphism = record
      { isRelHomomorphism = isRelHomomorphism
      ; homo = //-homo
      }

  record IsQuasiGroupMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isQuasiGroupHomomorphism : IsQuasiGroupHomomorphism ⟦_⟧
      injective             : Injective ⟦_⟧

    open IsQuasiGroupHomomorphism isQuasiGroupHomomorphism public


    ∙-isMagmaMonomorphism : ∙.IsMagmaMonomorphism ⟦_⟧
    ∙-isMagmaMonomorphism = record
      { isMagmaHomomorphism = ∙-isMagmaHomomorphism
      ; injective           = injective
      }

    \\-isMagmaMonomorphism : \\.IsMagmaMonomorphism ⟦_⟧
    \\-isMagmaMonomorphism = record
      { isMagmaHomomorphism = \\-isMagmaHomomorphism
      ; injective           = injective
      }
       
    //-isMagmaMonomorphism : //.IsMagmaMonomorphism ⟦_⟧
    //-isMagmaMonomorphism = record
      { isMagmaHomomorphism = //-isMagmaHomomorphism
      ; injective           = injective
      }
  
    open //.IsMagmaMonomorphism //-isMagmaMonomorphism public
      using (isRelMonomorphism)

  
  record IsQuasiGroupIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isQuasiGroupMonomorphism : IsQuasiGroupMonomorphism ⟦_⟧
      surjective            : Surjective ⟦_⟧

    open IsQuasiGroupMonomorphism isQuasiGroupMonomorphism public

    ∙-isMagmaIsomorphism : ∙.IsMagmaIsomorphism ⟦_⟧
    ∙-isMagmaIsomorphism    = record
      { isMagmaMonomorphism = ∙-isMagmaMonomorphism
      ; surjective          = surjective
      }

    \\-isMagmaIsomorphism : \\.IsMagmaIsomorphism ⟦_⟧
    \\-isMagmaIsomorphism   = record
      { isMagmaMonomorphism = \\-isMagmaMonomorphism
      ; surjective          = surjective
      }
       
    //-isMagmaIsomorphism : //.IsMagmaIsomorphism ⟦_⟧
    //-isMagmaIsomorphism   = record
      { isMagmaMonomorphism = //-isMagmaMonomorphism
      ; surjective          = surjective
      }

    open //.IsMagmaIsomorphism //-isMagmaIsomorphism public
      using (isRelIsomorphism)

module LoopMorphisms (L₁ : RawLoop a ℓ₁) (L₂ : RawLoop b ℓ₂) where

  open RawLoop L₁ renaming (Carrier to A; ∙-rawMagma to ∙-rawMagma₁; \\-rawMagma to \\-rawMagma₁; //-rawMagma to //-rawMagma₁;
                                   _≈_ to _≈₁_; _∙_ to _∙₁_; _\\_ to _\\₁_; _//_ to _//₁_; ε to ε₁)
  open RawLoop L₂ renaming (Carrier to B; ∙-rawMagma to ∙-rawMagma₂; \\-rawMagma to \\-rawMagma₂; //-rawMagma to //-rawMagma₂;  
                                  _≈_ to _≈₂_; _∙_ to _∙₂_; _\\_ to _\\₂_; _//_ to _//₂_ ; ε to ε₂)
  open MorphismDefinitions A B _≈₂_
  open FunctionDefinitions _≈₁_ _≈₂_

  open QuasiGroupMorphisms (RawLoop.rawQuasiGroup L₁) (RawLoop.rawQuasiGroup L₂)

  record IsLoopHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isQuasiGroupHomomorphism : IsQuasiGroupHomomorphism ⟦_⟧
      ε-homo                   : Homomorphic₀ ⟦_⟧ ε₁ ε₂

    open IsQuasiGroupHomomorphism isQuasiGroupHomomorphism public

  record IsLoopMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isLoopHomomorphism   : IsLoopHomomorphism ⟦_⟧
      injective            : Injective ⟦_⟧

    open IsLoopHomomorphism isLoopHomomorphism public

  record IsLoopIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isLoopMonomorphism   : IsLoopMonomorphism ⟦_⟧
      surjective           : Surjective ⟦_⟧

    open IsLoopMonomorphism isLoopMonomorphism public

open QuasiGroupMorphisms public
open LoopMorphisms public
