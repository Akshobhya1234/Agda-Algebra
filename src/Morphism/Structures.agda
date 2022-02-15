{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Morphism.Structures where

open import Algebra
import Algebra.Morphism.Definitions as MorphismDefinitions
open import Level using (Level; _⊔_)
import Function.Definitions as FunctionDefinitions
open import Relation.Binary.Morphism.Structures
open import Algebra.Morphism.Structures

private
  variable
    a b ℓ₁ ℓ₂ : Level
