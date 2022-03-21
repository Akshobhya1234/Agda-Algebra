{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid; IsEquivalence)
module Structures
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Algebra.Core
open import Level using (_⊔_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_
open import Definitions _≈_

------------------------------------------------------------------------
-- Structures with 1 binary operation
------------------------------------------------------------------------

record IsLatinQuasigroup (∙ : Op₂ A ) : Set (a ⊔ ℓ) where
  field
    isMagma     : IsMagma ∙
    latinSquare : LatinSquare ∙

  open IsMagma isMagma public

  latinSquare₁ : LatinSquare₁ ∙
  latinSquare₁ = proj₁ latinSquare

  latinSquare₂ : LatinSquare₂ ∙
  latinSquare₂ = proj₂ latinSquare

record IsIdempotentMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    idem    : Idempotent ∙

  open IsMagma isMagma public

record IsAlternateMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma  : IsMagma ∙
    alter    : Alternative ∙

  open IsMagma isMagma public

record IsFlexibleMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma  : IsMagma ∙
    flex     : Flexible ∙

  open IsMagma isMagma public

record IsMedialMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    medial  : Medial ∙

  open IsMagma isMagma public

record IsSemimedialMagma (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma : IsMagma ∙
    semiMedial  : Semimedial ∙

  open IsMagma isMagma public

record IsInverseSemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isSemigroup     : IsSemigroup ∙
    pseudoInverse   : PseudoInverse ∙

  open IsSemigroup isSemigroup public

------------------------------------------------------------------------
-- Structures with 1 binary operation and 1 element
------------------------------------------------------------------------

record IsLeftUnitalMagma (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isMagma  : IsMagma ∙
    identity : LeftIdentity ε ∙

  open IsMagma isMagma public

record IsRightUnitalMagma (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isMagma  : IsMagma ∙
    identity : RightIdentity ε ∙

  open IsMagma isMagma public

------------------------------------------------------------------------
-- Structures with 2 binary operations, 1 unary operation & 1 element
------------------------------------------------------------------------

record IsNonAssociativeRing (+ * : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    +-isAbelianGroup : IsAbelianGroup + 0# -_
    *-cong           : Congruent₂ *
    identity         : Identity 1# *
    distrib          : * DistributesOver +
    zero             : Zero 0# *

  open IsAbelianGroup +-isAbelianGroup public
    renaming
    ( assoc                   to +-assoc
    ; ∙-cong                  to +-cong
    ; ∙-congˡ                 to +-congˡ
    ; ∙-congʳ                 to +-congʳ
    ; identity                to +-identity
    ; identityˡ               to +-identityˡ
    ; identityʳ               to +-identityʳ
    ; inverse                 to -‿inverse
    ; inverseˡ                to -‿inverseˡ
    ; inverseʳ                to -‿inverseʳ
    ; ⁻¹-cong                 to -‿cong
    ; comm                    to +-comm
    ; isMagma                 to +-isMagma
    ; isSemigroup             to +-isSemigroup
    ; isMonoid                to +-isMonoid
    ; isUnitalMagma           to +-isUnitalMagma
    ; isCommutativeMagma      to +-isCommutativeMagma
    ; isCommutativeMonoid     to +-isCommutativeMonoid
    ; isCommutativeSemigroup  to +-isCommutativeSemigroup
    ; isInvertibleMagma       to +-isInvertibleMagma
    ; isInvertibleUnitalMagma to +-isInvertibleUnitalMagma
    ; isGroup                 to +-isGroup
    )

  *-isMagma : IsMagma *
  *-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong        = *-cong
    }

  *-identityˡ : LeftIdentity 1# *
  *-identityˡ = proj₁ identity

  *-identityʳ : RightIdentity 1# *
  *-identityʳ = proj₂ identity

------------------------------------------------------------------------
-- Structures with 3 binary operation and 1 element
------------------------------------------------------------------------

record IsLeftBolLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isLoop  : IsLoop ∙ \\ //  ε
    leftBol : LeftBol ∙

  open IsLoop isLoop public

record IsRightBolLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isLoop   : IsLoop ∙ \\ //  ε
    rightBol : RightBol ∙

  open IsLoop isLoop public

record IsMoufangLoop (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isLoop           : IsLoop ∙ \\ // ε
    moufangIdentity  : MoufangIdentity₁ ∙
    moufangIdentity₂ : MoufangIdentity₂ ∙
    moufangIdentity₃ : MoufangIdentity₃ ∙
    moufangIdentity₄ : MoufangIdentity₄ ∙

  open IsLoop isLoop public

record IsPique (∙ \\ // : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  field
    isQuasigroup : IsQuasigroup ∙ \\ //
    idem         : Idempotent ∙

  open IsQuasigroup isQuasigroup public
