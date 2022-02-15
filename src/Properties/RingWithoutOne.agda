{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Bundles
open import Structures

module Properties.RingWithoutOne {r₁ r₂} (R : RingWithoutOne r₁ r₂) where

open RingWithoutOne R

import Algebra.Properties.AbelianGroup as AbelianGroupProperties
open import Function.Base using (_$_)
open import Relation.Binary.Reasoning.Setoid setoid
