{-# OPTIONS --without-K --safe #-}


module Quasigroup.Bundles where
  
open import Algebra.Core
open import Quasigroup.Structures
open import Relation.Binary
open import Level

record Pique c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    ε       : Carrier
    _⁻¹     : Op₁ Carrier
    isPique : IsPique _≈_ _∙_ ε _⁻¹

  open IsPique isPique public
