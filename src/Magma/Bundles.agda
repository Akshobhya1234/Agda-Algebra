{-# OPTIONS --without-K --safe #-}


module Magma.Bundles where

open import Algebra.Bundles
open import Algebra.Core
open import Magma.Structures
open import Relation.Binary
open import Level


record IdempotentMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isIdempotentMagma  : IsIdempotentMagma _≈_ _∙_

  open IsIdempotentMagma isIdempotentMagma public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (rawMagma)
