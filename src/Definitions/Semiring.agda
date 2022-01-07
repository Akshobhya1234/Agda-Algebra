{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Semiring)

-- Credit: This definition is taken from the stdlib issue #1175
-- As given by @MatthewDaggitt and @mechvel

module Definitions.Semiring {α α≈} (R : Semiring α α≈)
  where
  open Semiring R

  record NonZero (x : Carrier) : Set α≈ where
     constructor mkNonZero
     field
        nonZero : x ≉ 0#
