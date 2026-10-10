/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.C0DirectSum
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorAlgebra

/-!
# The c₀-direct sum of compact-operator algebras

This module specializes the general dependent `C0DirectSum` to compact-operator
C-star algebras.  The generic construction and its coordinate/truncation API
remain in `DirectSum.C0DirectSum`.
-/

set_option autoImplicit false
noncomputable section

open Filter Set Topology
open scoped BigOperators CStarAlgebra ENNReal

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uι uA uH

/-- The dependent c₀-direct sum of compact-operator C-star algebras. -/
abbrev CompactOperatorC0Sum {ι : Type uι} (H : ι → Type uH)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)] :=
  C0DirectSum
    (fun i => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i))

end MathlibAnnex.Analysis.CStarAlgebra
