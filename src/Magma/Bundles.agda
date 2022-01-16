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

record AlternateMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isAlternateMagma  : IsAlternateMagma _≈_ _∙_

  open IsAlternateMagma isAlternateMagma public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (rawMagma)

record FlexibleMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isFlexibleMagma  : IsFlexibleMagma _≈_ _∙_

  open IsFlexibleMagma isFlexibleMagma public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (rawMagma)

record MedialMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isMedialMagma  : IsMedialMagma _≈_ _∙_

  open IsMedialMagma isMedialMagma public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (rawMagma)

record SemimedialMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isSemimedialMagma  : IsSemimedialMagma _≈_ _∙_

  open IsSemimedialMagma isSemimedialMagma public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (rawMagma)

record LeftUnitalMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier  : Set c
    _≈_      : Rel Carrier ℓ
    _∙_      : Op₂ Carrier
    ε        : Carrier
    isLeftUnitalMagma  : IsLeftUnitalMagma _≈_ _∙_ ε

  open IsLeftUnitalMagma isLeftUnitalMagma public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (rawMagma)

record RightUnitalMagma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier  : Set c
    _≈_      : Rel Carrier ℓ
    _∙_      : Op₂ Carrier
    ε        : Carrier
    isRightUnitalMagma  : IsRightUnitalMagma _≈_ _∙_ ε

  open IsRightUnitalMagma isRightUnitalMagma public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (rawMagma)
