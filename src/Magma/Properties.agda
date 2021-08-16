{-# OPTIONS --without-K --safe #-}

open import Algebra

module Magma.Properties
  {a ℓ} (M : Magma a ℓ) where

open Magma M
open import Function
open import Relation.Binary.Reasoning.Setoid setoid
