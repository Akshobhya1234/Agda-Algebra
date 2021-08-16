{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Quasigroup.Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  where
