/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Primitive

/-!
# Chosen pure-state representatives of primitive-spectrum points

Each actual primitive point stores the existence of a pure-state GNS kernel.
This module exposes one chosen representative and its exact kernel carrier.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace PrimitiveSpectrum

/-- The pure-state GNS representative stored by an actual primitive point. -/
def pureStateRepresentative (P : PrimitiveSpectrum A) : NonUnitalPureState A :=
  P.property.choose

@[simp]
theorem kernelIdeal_pureStateRepresentative (P : PrimitiveSpectrum A) :
    NonUnitalCStarRepresentation.kernelIdeal P.pureStateRepresentative.gnsRepresentation =
      P.toTwoSidedIdeal := rfl

@[simp]
theorem coe_kernelIdeal_pureStateRepresentative (P : PrimitiveSpectrum A) :
    (NonUnitalCStarRepresentation.kernelIdeal
      P.pureStateRepresentative.gnsRepresentation : Set A) = P.val := by
  rw [kernelIdeal_pureStateRepresentative, coe_toTwoSidedIdeal]

end PrimitiveSpectrum

end MathlibAnnex.Analysis.CStarAlgebra
