{-# OPTIONS --without-K --safe #-}

open import Algebra

module Loop.Properties
  {a ℓ} (L : Loop a ℓ) where

open Loop L
open import Function
open import Relation.Binary.Reasoning.Setoid setoid