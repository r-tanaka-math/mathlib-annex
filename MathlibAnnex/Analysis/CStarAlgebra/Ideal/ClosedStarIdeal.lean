/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Concrete norm-closed two-sided C-star ideals
The structure and its named instance are exact R34 MAIN author blocks.
No compact-representation or decomposition hypothesis is part of these data.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Set Module
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A concrete norm-closed two-sided C-star ideal, represented without adding
an ambient unit.  The carrier is a `NonUnitalStarSubalgebra`; the two absorption
laws record exactly the ideal property. -/
structure ClosedStarIdeal (A : Type u) [NonUnitalCStarAlgebra A] where
  toNonUnitalStarSubalgebra : NonUnitalStarSubalgebra ℂ A
  isClosed_carrier : IsClosed (toNonUnitalStarSubalgebra : Set A)
  mul_mem_left : ∀ (a : A) {x : A}, x ∈ toNonUnitalStarSubalgebra →
    a * x ∈ toNonUnitalStarSubalgebra
  mul_mem_right : ∀ {x : A} (a : A), x ∈ toNonUnitalStarSubalgebra →
    x * a ∈ toNonUnitalStarSubalgebra

namespace ClosedStarIdeal

instance instNonUnitalCStarAlgebra (I : ClosedStarIdeal A) :
    NonUnitalCStarAlgebra I.toNonUnitalStarSubalgebra :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra I.toNonUnitalStarSubalgebra
    (h_closed := I.isClosed_carrier)

end ClosedStarIdeal

end MathlibAnnex.Analysis.CStarAlgebra
