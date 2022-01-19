{-# OPTIONS --without-K --safe #-}

open import Algebra.Construct.DirectProduct

module Construct.DirectProduct where

open import Algebra
import Algebra.Construct.DirectProduct as DirectProduct
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Level using (Level; _⊔_)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Raw bundles

rawQuasigroup : RawQuasigroup a ℓ₁ → RawQuasigroup b ℓ₂ → RawQuasigroup (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
rawQuasigroup M N = record
  { Carrier = M.Carrier × N.Carrier
  ; _≈_     = Pointwise M._≈_ N._≈_
  ; _∙_     = zip M._∙_ N._∙_
  ; _\\_    = zip M._\\_ N._\\_
  ; _//_    = zip M._//_ N._//_
  } where module M = RawQuasigroup M; module N = RawQuasigroup N

rawLoop : RawLoop a ℓ₁ → RawLoop b ℓ₂ → RawLoop (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
rawLoop M N = record
  { Carrier = M.Carrier × N.Carrier
  ; _≈_     = Pointwise M._≈_ N._≈_
  ; _∙_     = zip M._∙_ N._∙_
  ; _\\_    = zip M._\\_ N._\\_
  ; _//_    = zip M._//_ N._//_
  ; ε       = M.ε , N.ε
  } where module M = RawLoop M; module N = RawLoop N

------------------------------------------------------------------------
-- Bundles

unitalMagma : UnitalMagma a ℓ₁ → UnitalMagma b ℓ₂ → UnitalMagma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
unitalMagma M N = record
  { ε = M.ε , N.ε
  ; isUnitalMagma = record
    { isMagma = Magma.isMagma (magma M.magma N.magma)
    ; identity = (M.identityˡ , N.identityˡ <*>_)
               , (M.identityʳ , N.identityʳ <*>_)
    }
  } where module M = UnitalMagma M; module N = UnitalMagma N

invertibleMagma : InvertibleMagma a ℓ₁ → InvertibleMagma b ℓ₂ → InvertibleMagma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
invertibleMagma M N = record
  { _⁻¹ = map M._⁻¹ N._⁻¹
  ; isInvertibleMagma = record
    { isMagma = Magma.isMagma (magma M.magma N.magma)
    ; inverse = (λ x → (M.inverseˡ , N.inverseˡ) <*> x)
                , (λ x → (M.inverseʳ , N.inverseʳ) <*> x)
    }
  } where module M = InvertibleMagma M; module N = InvertibleMagma N

invertibleUnitalMagma : InvertibleUnitalMagma a ℓ₁ → InvertibleUnitalMagma b ℓ₂ → InvertibleUnitalMagma (a ⊔ b) (ℓ₁ ⊔ ℓ₂)
invertibleUnitalMagma M N = record
  { ε = M.ε , N.ε
  ; isInvertibleUnitalMagma = record
    { isInvertibleMagma = InvertibleMagma.isInvertibleMagma (invertibleMagma M.invertibleMagma N.invertibleMagma)
    ; identity = (M.identityˡ , N.identityˡ <*>_)
               , (M.identityʳ , N.identityʳ <*>_)
    }
  } where module M = InvertibleUnitalMagma M; module N = InvertibleUnitalMagma N

