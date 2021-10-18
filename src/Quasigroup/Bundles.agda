{-# OPTIONS --without-K --safe #-}


module Quasigroup.Bundles where
  
open import Algebra.Core
open import Quasigroup.Structures
open import Relation.Binary
open import Level
open import Algebra.Bundles
open import Algebra.Structures

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


------------------------------------------------------------------------
-- Structures with 3 binary operations
------------------------------------------------------------------------

--Note this QuasiGroup is different from Algebra.Bundles Quasigroup in stdlib
--Here QuasiGroup (Q, ∗, \, /) is a type (2,2,2) algebra
-- TODO add fixity.

record RawQuasiGroup c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_      : Op₂ Carrier
    _\\_      : Op₂ Carrier
    _//_      : Op₂ Carrier

  ∙-rawMagma : RawMagma c ℓ
  ∙-rawMagma = record
    { _≈_ = _≈_
    ; _∙_ = _∙_
    }

  \\-rawMagma : RawMagma c ℓ
  \\-rawMagma = record
    { _≈_ = _≈_
    ; _∙_ = _\\_
    }

  //-rawMagma : RawMagma c ℓ
  //-rawMagma = record
    { _≈_ = _≈_
    ; _∙_ = _//_
    }

record QuasiGroup c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    _\\_    : Op₂ Carrier
    _//_    : Op₂ Carrier
    isQuasiGroup : IsQuasiGroup  _≈_ _∙_ _\\_ _//_
    
  open IsQuasiGroup isQuasiGroup public

  rawQuasiGroup : RawQuasiGroup c ℓ
  rawQuasiGroup = record
    { _≈_  = _≈_
    ; _∙_  = _∙_
    ; _\\_  = _\\_
    ; _//_  = _//_ 
    }

  open RawQuasiGroup rawQuasiGroup public
    using (//-rawMagma; \\-rawMagma; ∙-rawMagma)

  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }

  open Setoid setoid public
    using (_≉_)

