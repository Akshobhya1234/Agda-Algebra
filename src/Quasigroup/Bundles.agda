{-# OPTIONS --without-K --safe #-}


module Quasigroup.Bundles where

open import Algebra.Core
open import Quasigroup.Structures
open import Relation.Binary
open import Level
open import Algebra.Bundles
open import Algebra.Structures

record Pique c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infixl 7 _\\_
  infixl 7 _//_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    _\\_    : Op₂ Carrier
    _//_    : Op₂ Carrier
    ε       : Carrier
    isPique : IsPique _≈_ _∙_ _\\_ _//_ ε

  open IsPique isPique public

record LatinQuasigroup c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isLatinQuasigroup : IsLatinQuasigroup _≈_ _∙_

  open IsLatinQuasigroup isLatinQuasigroup public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (_≉_; rawMagma)

