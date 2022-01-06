{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Semiring)

module Definitions.Semiring {α α≈} (R : Semiring α α≈)
  where
  open Semiring R

  record NonZero (x : Carrier) : Set α≈ where
     constructor mkNonZero
     field
        nonZero : x ≉ 0#
