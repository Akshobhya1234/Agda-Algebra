{-# OPTIONS --without-K --safe #-}

open import Algebra

module Quasigroup.Properties
  {a ℓ} (Q : Quasigroup a ℓ) where

open Quasigroup Q
open import Function
open import Relation.Binary.Reasoning.Setoid setoid
