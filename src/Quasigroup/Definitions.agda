{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Quasigroup.Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  where
  
open import Algebra.Core

_QuasigroupIdentity₁_ : Op₂ A → Op₂ A → Set _
_*_ QuasigroupIdentity₁ _|ᵇ_ = ∀ x y → (x *(x |ᵇ y)) ≈ y

_QuasigroupIdentity₂_ : Op₂ A → Op₂ A → Set _
_*_ QuasigroupIdentity₂ _|ᵇ_ = ∀ x y → (x |ᵇ(x * y)) ≈ y

_QuasigroupIdentity₃_ : Op₂ A → Op₂ A → Set _
_*_ QuasigroupIdentity₃ _|ᶠ_ = ∀ x y → ((y |ᶠ x)* x) ≈ y

_QuasigroupIdentity₄_ : Op₂ A → Op₂ A → Set _
_*_ QuasigroupIdentity₄ _|ᶠ_ = ∀ x y → ((y * x)|ᶠ x) ≈ y
