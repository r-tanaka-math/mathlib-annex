/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Basic
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Kernel
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CoefficientPair
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.CoefficientTranslate
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Arbitrary-Hilbert-universe coverage by actual pure-state GNS models

The model is small but the represented Hilbert space is in an independent
universe. Purity of a unit vector state, actual GNS coefficient recovery and
the already proved separation of inequivalent coefficient kernels construct
the equivalence. Equality of representation kernels is never a premise for
unitary equivalence. No separability, faithfulness or unit in A is required.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every nonzero irreducible representation, in ANY Hilbert universe, has an
actual pure-state GNS representative in the universe controlled by A. -/
theorem exists_pureState_unitaryEquivalent_gnsRepresentation
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    ∃ phi : NonUnitalPureState A, pi.UnitaryEquivalent phi.gnsRepresentation := by
  letI : Nontrivial A := nontrivial_algebra_of_isNonzero pi hpi.1
  letI : Nontrivial H := nontrivial_of_isNonzero pi hpi.1
  obtain ⟨z, hz⟩ := exists_ne (0 : H)
  let x : H := NormedSpace.normalize z
  have hx1 : ‖x‖ = 1 := NormedSpace.norm_normalize hz
  have hx : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hx1]; exact one_ne_zero)
  let phi : NonUnitalPureState A :=
    ⟨matrixCoefficient pi x x,
      isPureNonUnitalState_matrixCoefficient_self_of_isIrreducible pi hpi x hx1⟩
  let xi := NonUnitalStateGNS.vector phi.val phi.property.1
  have hxi : xi ≠ 0 := norm_ne_zero_iff.mp (by
    rw [NonUnitalStateGNS.norm_vector]; exact one_ne_zero)
  have hpoint : matrixCoefficientKernel pi hpi x x hx hx =
      matrixCoefficientKernel phi.gnsRepresentation phi.isIrreducible_gnsRepresentation
        xi xi hxi hxi := by
    apply Subtype.ext
    change ((matrixCoefficient pi x x).ker : Set A) =
      ((matrixCoefficient phi.gnsRepresentation xi xi).ker : Set A)
    rw [show matrixCoefficient phi.gnsRepresentation xi xi = phi.val from
      phi.matrixCoefficient_gnsRepresentation]
  exact ⟨phi, unitaryEquivalent_of_linked_matrixCoefficientKernel
    pi phi.gnsRepresentation hpi phi.isIrreducible_gnsRepresentation
    x x xi xi hx hx hxi hxi (Or.inl hpoint)⟩

/-- In particular, the small GNS list contains exactly the actual kernels
of arbitrary-universe nonzero irreducible representations. -/
theorem exists_pureState_kernelIdeal_eq
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    ∃ phi : NonUnitalPureState A, kernelIdeal pi = kernelIdeal phi.gnsRepresentation := by
  obtain ⟨phi, hphi⟩ := exists_pureState_unitaryEquivalent_gnsRepresentation pi hpi
  exact ⟨phi, hphi.kernelIdeal_eq⟩

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

namespace MathlibAnnex.Analysis.CStarAlgebra.IrreducibleSpectrum

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
open NonUnitalCStarRepresentation

/-- The small spectrum point represented by an arbitrary-universe irreducible action. -/
def ofRepresentation (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    IrreducibleSpectrum A :=
  ofPureState (exists_pureState_unitaryEquivalent_gnsRepresentation pi hpi).choose

/-- The chosen pure-state representative records precisely unitary equivalence. -/
theorem ofRepresentation_eq_ofPureState_iff (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsIrreducible) (phi : NonUnitalPureState A) :
    ofRepresentation pi hpi = ofPureState phi ↔ pi.UnitaryEquivalent phi.gnsRepresentation := by
  rw [ofRepresentation, ofPureState_eq_iff]
  have h := (exists_pureState_unitaryEquivalent_gnsRepresentation pi hpi).choose_spec
  exact ⟨fun k => h.trans k, fun k => h.symm.trans k⟩

/-- Different Hilbert universes are permitted on both sides. In particular,
equal representation kernels cannot collapse inequivalent spectrum points. -/
theorem ofRepresentation_eq_iff (pi : NonUnitalCStarRepresentation A H)
    (sigma : NonUnitalCStarRepresentation A K) (hpi : pi.IsIrreducible)
    (hsigma : sigma.IsIrreducible) :
    ofRepresentation pi hpi = ofRepresentation sigma hsigma ↔ pi.UnitaryEquivalent sigma := by
  simp only [ofRepresentation, ofPureState_eq_iff]
  have h := (exists_pureState_unitaryEquivalent_gnsRepresentation pi hpi).choose_spec
  have k := (exists_pureState_unitaryEquivalent_gnsRepresentation sigma hsigma).choose_spec
  exact ⟨fun l => h.trans (l.trans k.symm), fun l => h.symm.trans (l.trans k)⟩

end MathlibAnnex.Analysis.CStarAlgebra.IrreducibleSpectrum
