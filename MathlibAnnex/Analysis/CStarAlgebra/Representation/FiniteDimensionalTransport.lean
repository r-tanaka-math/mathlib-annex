/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Representatives
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Finite dimension transported by unitary equivalence

The numerical condition is paired with actual finite dimensionality.
Pure GNS representatives transfer the condition to any acting Hilbert universe.
No compact-range, faithful, separable, or singleton assumption is used.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- An actual unitary intertwiner preserves finite dimension together with any
predicate on its numerical value. Finiteness is not inferred from `finrank = 0`. -/
theorem UnitaryEquivalent.finiteDimensional_finrank_iff
    {pi : NonUnitalCStarRepresentation A H} {rho : NonUnitalCStarRepresentation A K}
    (h : pi.UnitaryEquivalent rho) (P : ℕ → Prop) :
    (FiniteDimensional ℂ H ∧ P (Module.finrank ℂ H)) ↔
      (FiniteDimensional ℂ K ∧ P (Module.finrank ℂ K)) := by
  obtain ⟨U, _hU⟩ := h
  constructor
  · rintro ⟨hH, hP⟩
    letI : FiniteDimensional ℂ H := hH
    refine ⟨U.toLinearEquiv.finiteDimensional, ?_⟩
    rwa [← U.toLinearEquiv.finrank_eq]
  · rintro ⟨hK, hP⟩
    letI : FiniteDimensional ℂ K := hK
    refine ⟨U.symm.toLinearEquiv.finiteDimensional, ?_⟩
    rwa [U.toLinearEquiv.finrank_eq]

/-- Pure GNS tests in the algebra universe control every separately specified
Hilbert universe, through the actual unitary representative theorem. -/
theorem finiteDimensional_finrank_of_forall_pure_state
    [PartialOrder A] [StarOrderedRing A] (P : ℕ → Prop)
    (h : ∀ phi : NonUnitalPureState A,
      FiniteDimensional ℂ phi.GNS ∧ P (Module.finrank ℂ phi.GNS))
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    FiniteDimensional ℂ H ∧ P (Module.finrank ℂ H) := by
  obtain ⟨phi, hU⟩ := pi.exists_pureState_unitaryEquivalent_gnsRepresentation hpi
  exact (hU.finiteDimensional_finrank_iff P).2 (h phi)

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
