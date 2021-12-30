module Bundles where
  
open import Algebra.Core
open import Quasigroup.Structures
open import Relation.Binary
open import Level
open import Algebra.Bundles
open import Algebra.Structures
open import Structures

record Rng c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    isRng  : IsRng _≈_ _+_ _*_ -_ 0#

  open IsRng isRng public

  +-abelianGroup : AbelianGroup _ _
  +-abelianGroup = record { isAbelianGroup = +-isAbelianGroup }

  *-semigroup : Semigroup _ _
  *-semigroup = record { isSemigroup = *-isSemigroup }

  open AbelianGroup +-abelianGroup public
    using () renaming (group to +-group; invertibleMagma to +-invertibleMagma; invertibleUnitalMagma to +-invertibleUnitalMagma)
    
  open Semigroup *-semigroup public
    using () renaming
    ( rawMagma to *-rawMagma
    ; magma    to *-magma
    )