{-# OPTIONS --without-K --safe #-}

module Bundles where

open import Algebra.Core
open import Relation.Binary
open import Level
open import Algebra.Bundles
open import Algebra.Structures
open import Structures

------------------------------------------------------------------------
-- Bundles with 1 binary operation
------------------------------------------------------------------------

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

record InverseSemigroup c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier            : Set c
    _≈_                : Rel Carrier ℓ
    _∙_                : Op₂ Carrier
    isInverseSemigroup : IsInverseSemigroup _≈_ _∙_

  open IsInverseSemigroup isInverseSemigroup public

  magma : Magma c ℓ
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (_≉_; rawMagma)

------------------------------------------------------------------------
-- Bundles with 1 binary operation and 1 element
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Bundles with 2 binary operations, 1 unary operation & 1 element
------------------------------------------------------------------------

record NonAssociativeRing c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier               : Set c
    _≈_                   : Rel Carrier ℓ
    _+_                   : Op₂ Carrier
    _*_                   : Op₂ Carrier
    -_                    : Op₁ Carrier
    0#                    : Carrier
    1#                    : Carrier
    isNonAssociativeRing  : IsNonAssociativeRing _≈_ _+_ _*_ -_ 0# 1#

  open IsNonAssociativeRing isNonAssociativeRing public

  +-abelianGroup : AbelianGroup _ _
  +-abelianGroup = record { isAbelianGroup = +-isAbelianGroup }

  open AbelianGroup +-abelianGroup public
    using () renaming (group to +-group; invertibleMagma to +-invertibleMagma; invertibleUnitalMagma to +-invertibleUnitalMagma)

------------------------------------------------------------------------
-- Bundles with 2 binary operation and 2 elements
------------------------------------------------------------------------

record Quasiring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    _+_           : Op₂ Carrier
    _*_           : Op₂ Carrier
    0#            : Carrier
    1#            : Carrier
    isQuasiring   : IsQuasiring _≈_ _+_ _*_ 0# 1#

  open IsQuasiring isQuasiring public

  +-monoid : Monoid _ _
  +-monoid = record { isMonoid = +-isMonoid }

  open Monoid +-monoid public
    using (_≉_) renaming
    ( rawMagma    to  +-rawMagma
    ; magma       to  +-magma
    ; semigroup   to  +-semigroup
    ; unitalMagma to  +-unitalMagma
    ; rawMonoid   to  +-rawMonoid
    )

  *-monoid : Monoid _ _
  *-monoid = record { isMonoid = *-isMonoid }

  open Monoid *-monoid public
    using () renaming
    ( rawMagma  to *-rawMagma
    ; magma     to *-magma
    ; semigroup to *-semigroup
    ; rawMonoid to *-rawMonoid
    )

------------------------------------------------------------------------
-- Bundles with 3 binary operation and 1 element
------------------------------------------------------------------------

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

record LeftBolLoop c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    _\\_    : Op₂ Carrier
    _//_    : Op₂ Carrier
    ε       : Carrier
    isLeftBolLoop : IsLeftBolLoop  _≈_ _∙_ _\\_ _//_ ε

  open IsLeftBolLoop isLeftBolLoop public

  loop : Loop _ _
  loop = record { isLoop = isLoop }

  open Loop loop public
    using (quasigroup)

record RightBolLoop c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    _\\_    : Op₂ Carrier
    _//_    : Op₂ Carrier
    ε       : Carrier
    isRightBolLoop : IsRightBolLoop  _≈_ _∙_ _\\_ _//_ ε

  open IsRightBolLoop isRightBolLoop public

  loop : Loop _ _
  loop = record { isLoop = isLoop }

  open Loop loop public
    using (quasigroup)

record MoufangLoop c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    _\\_    : Op₂ Carrier
    _//_    : Op₂ Carrier
    ε       : Carrier
    isMoufangLoop : IsMoufangLoop  _≈_ _∙_ _\\_ _//_ ε

  open IsMoufangLoop isMoufangLoop public

  loop : Loop _ _
  loop = record { isLoop = isLoop }

  open Loop loop public
    using (quasigroup)
