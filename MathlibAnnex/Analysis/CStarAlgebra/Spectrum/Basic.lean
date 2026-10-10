/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.NonUnitalStateGNS
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.RepresentationEquivalence

/-!
# A small space of irreducible representation classes

The representatives are actual pure continuous positive functionals on A.
The equivalence relation uses their actual canonical-extension GNS actions,
restricted to A, and an actual surjective linear isometry intertwining them.
It is NOT equality of kernels. No topology is inherited from the pure-state
space here: the spectrum topology is defined later through the kernel map.
The construction is meaningful even when the pure-state type is empty.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Actual pure norm-one positive functionals, in the universe of A. -/
abbrev NonUnitalPureState := {phi : StrongDual ℂ A // IsPureNonUnitalState A phi}

namespace NonUnitalPureState
variable {A}

/-- The genuine Hilbert-space GNS construction of the canonical state extension. -/
abbrev GNS (phi : NonUnitalPureState A) := NonUnitalStateGNS.Space phi.val phi.property.1

/-- Its representation of the ORIGINAL algebra, not just its formal unitization. -/
def gnsRepresentation (phi : NonUnitalPureState A) : NonUnitalCStarRepresentation A phi.GNS :=
  NonUnitalStateGNS.representation phi.val phi.property.1

theorem isIrreducible_gnsRepresentation (phi : NonUnitalPureState A) :
    phi.gnsRepresentation.IsIrreducible :=
  NonUnitalStateGNS.isIrreducible_representation phi.val phi.property.1 phi.property

/-- The distinguished vector belongs to the actual extension GNS Hilbert space. -/
abbrev gnsVector (phi : NonUnitalPureState A) : phi.GNS :=
  NonUnitalStateGNS.vector phi.val phi.property.1

theorem norm_gnsVector (phi : NonUnitalPureState A) : ‖phi.gnsVector‖ = 1 :=
  NonUnitalStateGNS.norm_vector phi.val phi.property.1

theorem gnsVector_ne_zero (phi : NonUnitalPureState A) : phi.gnsVector ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [phi.norm_gnsVector]; exact one_ne_zero)

/-- Canonical pointed coefficient recovery in the original algebra. -/
theorem matrixCoefficient_gnsRepresentation (phi : NonUnitalPureState A) :
    NonUnitalCStarRepresentation.matrixCoefficient phi.gnsRepresentation
      (NonUnitalStateGNS.vector phi.val phi.property.1)
      (NonUnitalStateGNS.vector phi.val phi.property.1) = phi.val :=
  NonUnitalStateGNS.matrixCoefficient_representation phi.val phi.property.1

end NonUnitalPureState

/-- Equivalence of actual GNS representations, with no kernel identification. -/
def pureStateGNSSetoid : Setoid (NonUnitalPureState A) where
  r phi psi := phi.gnsRepresentation.UnitaryEquivalent psi.gnsRepresentation
  iseqv :=
    ⟨fun phi => NonUnitalCStarRepresentation.unitaryEquivalent_refl phi.gnsRepresentation,
      fun h => h.symm, fun h k => h.trans k⟩

/-- The small irreducible spectrum: pure states modulo GNS unitary equivalence.
Its topology is specified in `Spectrum.Topology`, not by a state-space quotient. -/
def IrreducibleSpectrum := Quotient (pureStateGNSSetoid A)

namespace IrreducibleSpectrum
variable {A}

/-- Send an actual pure state to its representation class. -/
def ofPureState (phi : NonUnitalPureState A) : IrreducibleSpectrum A :=
  Quotient.mk (pureStateGNSSetoid A) phi

theorem ofPureState_eq_iff (phi psi : NonUnitalPureState A) :
    ofPureState phi = ofPureState psi ↔
      phi.gnsRepresentation.UnitaryEquivalent psi.gnsRepresentation :=
  Quotient.eq

theorem ofPureState_surjective : Function.Surjective (ofPureState (A := A)) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro phi
  exact ⟨phi, rfl⟩

end IrreducibleSpectrum
end MathlibAnnex.Analysis.CStarAlgebra
