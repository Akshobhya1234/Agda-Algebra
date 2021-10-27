{-# OPTIONS --without-K --safe #-}


module Loop.Bundles where

open import Algebra.Core
open import Relation.Binary
open import Level
open import Loop.Structures
open import Quasigroup.Bundles
open import Quasigroup.Structures

record RawLoop  c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    _\\_    : Op₂ Carrier
    _//_    : Op₂ Carrier
    ε       : Carrier

  rawQuasiGroup : RawQuasiGroup c ℓ
  rawQuasiGroup = record
    { _≈_ = _≈_
    ; _∙_ = _∙_
    ; _\\_ = _\\_
    ; _//_ = _//_
    }

  open RawQuasiGroup rawQuasiGroup public
    using (_≈_ ; ∙-rawMagma; \\-rawMagma; //-rawMagma)

record Loop  c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    _\\_    : Op₂ Carrier
    _//_    : Op₂ Carrier
    ε       : Carrier
    isLoop : IsLoop  _≈_ _∙_ _\\_ _//_ ε 
    
  open IsLoop isLoop public

  quasigroup : QuasiGroup _ _
  quasigroup = record { isQuasiGroup = isQuasiGroup }

  open QuasiGroup quasigroup public
    using (_≉_)
  

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
    using (_≉_; quasigroup)

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
    using (_≉_; quasigroup)

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
    using (_≉_; quasigroup)
