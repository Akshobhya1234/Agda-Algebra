{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid; IsEquivalence)
module Loop.Structures
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Algebra.Core
open import Level using (_⊔_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Algebra.Definitions _≈_
open import Loop.Definitions _≈_
open import Algebra.Structures _≈_

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
