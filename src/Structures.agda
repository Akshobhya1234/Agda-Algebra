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

record IsInverseSemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isSemigroup     : IsSemigroup ∙
    pseudoInverse   : PseudoInverse ∙

  open IsSemigroup isSemigroup public

record IsRng (+ * : Op₂ A) (-_ : Op₁ A) (0# : A) : Set (a ⊔ ℓ) where
  field
    +-isAbelianGroup : IsAbelianGroup + 0# -_
    *-isSemigroup    : IsSemigroup *
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

  open IsSemigroup *-isSemigroup public
    using ()
    renaming
    ( assoc    to *-assoc
    ; ∙-cong   to *-cong
    ; ∙-congˡ  to *-congˡ
    ; ∙-congʳ  to *-congʳ
    ; isMagma  to *-isMagma
    )

record IsNonAssociativeRing (+ * : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  field
    +-isAbelianGroup : IsAbelianGroup + 0# -_
    *-isUnitalMagma  : IsUnitalMagma * 1#
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
  open IsUnitalMagma *-isUnitalMagma public
    using ()
    renaming
    ( ∙-cong   to *-cong
    ; ∙-congˡ  to *-congˡ
    ; ∙-congʳ  to *-congʳ
    ; isMagma  to *-isMagma
    )
