{-# OPTIONS --without-K --safe #-}


module Loop.Bundles where

open import Algebra.Bundles
open import Algebra.Core
open import Relation.Binary
open import Level
open import Loop.Structures
open import Quasigroup.Bundles

record RawLoop c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    ε       : Carrier
    _⁻¹     : Op₁ Carrier

  rawQuasigroup : RawQuasigroup c ℓ
  rawQuasigroup = record
    { _≈_ = _≈_
    ; _∙_ = _∙_
    ; ε   = ε
    ; _⁻¹ =  _⁻¹
    }

  open RawQuasigroup rawQuasigroup public
    using (_≉_; rawMagma)

record LeftBolLoop c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    ε       : Carrier
    _⁻¹     : Op₁ Carrier
    isLeftBolLoop : IsLeftBolLoop _≈_ _∙_ ε _⁻¹

  open IsLeftBolLoop isLeftBolLoop public

  loop : Loop _ _
  loop = record { isLoop = isLoop }

  open Loop loop public
    using (_≉_; rawMagma; magma; quasigroup)

record RightBolLoop c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    ε       : Carrier
    _⁻¹     : Op₁ Carrier
    isRightBolLoop : IsRightBolLoop _≈_ _∙_ ε _⁻¹

  open IsRightBolLoop isRightBolLoop public

  loop : Loop _ _
  loop = record { isLoop = isLoop }

  open Loop loop public
    using (_≉_; rawMagma; magma; quasigroup)

record MoufangLoop c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    ε       : Carrier
    _⁻¹     : Op₁ Carrier
    isMoufangLoop : IsMoufangLoop _≈_ _∙_ ε _⁻¹

  open IsMoufangLoop isMoufangLoop public

  loop : Loop _ _
  loop = record { isLoop = isLoop }

  open Loop loop public
    using (_≉_; rawMagma; magma; quasigroup)
