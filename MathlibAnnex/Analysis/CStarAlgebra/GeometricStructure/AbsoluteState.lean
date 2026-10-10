/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.NonUnitalStateGNS
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.RepresentationComponents
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.PureStateKernel

/-!
# Absolute pure states, their GNS representations, and components

`extremeAbsoluteState` is the positive state singled out by the already proved
unitary-translate existence and uniqueness. It is not an arbitrary norming state
or a definition of the component relation. Its representation below is literally
the GNS representation of its canonical extension restricted to the original A.
The kernel of a functional and the kernel of a representation remain distinct.

The component statements use the received `Related`, the whole coefficient
family, and the existing gamma. No topological comparison with an irreducible
spectrum, self-adjoint-part assertion, or zero-algebra extension is claimed here.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]

private def absoluteStateContinuousMap {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : NonUnitalCStarRepresentation A H) : A →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := pi, map_add' := map_add pi, map_smul' := map_smul pi }
    1 (fun a => by
      change ‖pi a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le pi a)

/-- The unique positive pure state in an extreme functional's unitary decomposition.
Only the state is made into a definition; translating unitaries need not be unique. -/
def extremeAbsoluteState (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    StrongDual ℂ A :=
  (exists_pureState_unitaryTranslate_of_mem_extremePoints_dual_closedBall rho.property).choose

theorem isPureNonUnitalState_extremeAbsoluteState
    (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    IsPureNonUnitalState A (extremeAbsoluteState rho) :=
  (exists_pureState_unitaryTranslate_of_mem_extremePoints_dual_closedBall rho.property).choose_spec.1

/-- Existence of a translating unitary and the exact inverse formula. -/
theorem exists_unitaryTranslate_eq_extremeAbsoluteState
    (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    ∃ u : unitary (Unitization ℂ A),
      unitaryTranslate u rho.val = extremeAbsoluteState rho ∧
        rho.val = unitaryTranslate (star u) (extremeAbsoluteState rho) :=
  (exists_pureState_unitaryTranslate_of_mem_extremePoints_dual_closedBall rho.property).choose_spec.2

/-- Any positive pure translate is this state. This uses the received uniqueness
proof, rather than choosing one unitary and claiming it to be unique. -/
theorem eq_extremeAbsoluteState_of_unitaryTranslate_eq
    (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ)
    (phi : StrongDual ℂ A) (hpure : IsPureNonUnitalState A phi)
    (u : unitary (Unitization ℂ A)) (hu : unitaryTranslate u rho.val = phi) :
    phi = extremeAbsoluteState rho := by
  obtain ⟨v, hv, -⟩ := exists_unitaryTranslate_eq_extremeAbsoluteState rho
  have hnonneg : ∀ a : A, 0 ≤ a → 0 ≤ unitaryTranslate u rho.val a := by
    intro a ha
    rw [hu]
    exact hpure.1.1 a ha
  have hnonneg' : ∀ a : A, 0 ≤ a → 0 ≤ unitaryTranslate v rho.val a := by
    intro a ha
    rw [hv]
    exact (isPureNonUnitalState_extremeAbsoluteState rho).1.1 a ha
  exact hu.symm.trans ((unitaryTranslate_eq_of_nonneg_of_mem_extremePoints_dual_closedBall
    rho.property u v hnonneg hnonneg').trans hv)

/-- The actual canonical-extension GNS space of the absolute state. -/
abbrev ExtremeGNSHilbertSpace
    (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :=
  NonUnitalStateGNS.Space (extremeAbsoluteState rho)
    (isPureNonUnitalState_extremeAbsoluteState rho).1

/-- The actual absolute-state GNS action of the original algebra. -/
def extremeGNSRepresentation
    (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    NonUnitalCStarRepresentation A (ExtremeGNSHilbertSpace rho) :=
  NonUnitalStateGNS.representation (extremeAbsoluteState rho)
    (isPureNonUnitalState_extremeAbsoluteState rho).1

theorem isIrreducible_extremeGNSRepresentation
    (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    (extremeGNSRepresentation rho).IsIrreducible :=
  NonUnitalStateGNS.isIrreducible_representation (extremeAbsoluteState rho)
    (isPureNonUnitalState_extremeAbsoluteState rho).1
    (isPureNonUnitalState_extremeAbsoluteState rho)

/-- An arbitrary extreme functional is recovered by unit vectors in the GNS
of its absolute state, not merely in an auxiliary cyclic coefficient model. -/
theorem exists_unit_vectors_matrixCoefficient_extremeGNSRepresentation_eq
    (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    ∃ x y : ExtremeGNSHilbertSpace rho, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      NonUnitalCStarRepresentation.matrixCoefficient (extremeGNSRepresentation rho) x y = rho.val := by
  obtain ⟨u, -, hrep⟩ := exists_unitaryTranslate_eq_extremeAbsoluteState rho
  obtain ⟨x, y, hx, hy, hcoeff⟩ :=
    NonUnitalStateGNS.exists_unit_vectors_matrixCoefficient_eq_unitaryTranslate
      (extremeAbsoluteState rho) (isPureNonUnitalState_extremeAbsoluteState rho).1
      (isPureNonUnitalState_extremeAbsoluteState rho) (star u)
  exact ⟨x, y, hx, hy, hcoeff.trans hrep.symm⟩

/-- The corresponding equality of actual GSS points. -/
theorem exists_matrixCoefficientKernel_extremeGNSRepresentation_eq
    (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    ∃ (x y : ExtremeGNSHilbertSpace rho) (hx : x ≠ 0) (hy : y ≠ 0),
      NonUnitalCStarRepresentation.matrixCoefficientKernel (extremeGNSRepresentation rho)
        (isIrreducible_extremeGNSRepresentation rho) x y hx hy = extremeKernel rho := by
  obtain ⟨x, y, hx, hy, hcoeff⟩ := exists_unit_vectors_matrixCoefficient_extremeGNSRepresentation_eq rho
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hx]; exact one_ne_zero)
  have hy0 : y ≠ 0 := norm_ne_zero_iff.mp (by rw [hy]; exact one_ne_zero)
  refine ⟨x, y, hx0, hy0, ?_⟩
  apply Subtype.ext
  change ((NonUnitalCStarRepresentation.matrixCoefficient (extremeGNSRepresentation rho) x y).ker : Set A) = _
  rw [hcoeff]
  rfl

/-- The auxiliary representation, or any other irreducible coefficient realization
of a kernel, is equivalent to the actual GNS of the absolute state. The equality
branch is justified by the proved inequivalent-kernel separation. -/
theorem unitaryEquivalent_extremeGNSRepresentation_of_matrixCoefficientKernel_eq
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0)
    (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ)
    (hker : NonUnitalCStarRepresentation.matrixCoefficientKernel pi hpi x y hx hy = extremeKernel rho) :
    pi.UnitaryEquivalent (extremeGNSRepresentation rho) := by
  obtain ⟨z, w, hz, hw, hpoint⟩ := exists_matrixCoefficientKernel_extremeGNSRepresentation_eq rho
  exact NonUnitalCStarRepresentation.unitaryEquivalent_of_linked_matrixCoefficientKernel
    pi (extremeGNSRepresentation rho) hpi (isIrreducible_extremeGNSRepresentation rho)
    x y z w hx hy hz hw (Or.inl (hker.trans hpoint.symm))

/-- Paper 5.8 in its absolute-state GNS form, using the original component relation. -/
theorem related_extremeKernel_iff_unitaryEquivalent_extremeGNSRepresentation
    (rho tau : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    (NormedSpace.geometricStructureClosure ℂ A).Related (extremeKernel rho) (extremeKernel tau) ↔
      (extremeGNSRepresentation rho).UnitaryEquivalent (extremeGNSRepresentation tau) := by
  obtain ⟨x, y, hx, hy, hrho⟩ := exists_matrixCoefficientKernel_extremeGNSRepresentation_eq rho
  obtain ⟨z, w, hz, hw, htau⟩ := exists_matrixCoefficientKernel_extremeGNSRepresentation_eq tau
  rw [← hrho, ← htau]
  exact NonUnitalCStarRepresentation.related_matrixCoefficientKernel_iff_unitaryEquivalent
    (extremeGNSRepresentation rho) (extremeGNSRepresentation tau)
    (isIrreducible_extremeGNSRepresentation rho) (isIrreducible_extremeGNSRepresentation tau)
    x y z w hx hy hz hw

/-- Paper 5.9: ker(rho) and ker(abs(rho)) lie in the same actual component. -/
theorem related_extremeKernel_extremeAbsoluteState
    (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    (NormedSpace.geometricStructureClosure ℂ A).Related (extremeKernel rho)
      (extremeKernel ⟨extremeAbsoluteState rho,
        mem_extremePoints_dual_closedBall_of_isPureNonUnitalState _
          (isPureNonUnitalState_extremeAbsoluteState rho)⟩) := by
  obtain ⟨x, y, hx, hy, hpoint⟩ := exists_matrixCoefficientKernel_extremeGNSRepresentation_eq rho
  let phi := extremeAbsoluteState rho
  have hpure : IsPureNonUnitalState A phi := isPureNonUnitalState_extremeAbsoluteState rho
  let xi := NonUnitalStateGNS.vector phi hpure.1
  have hxi : xi ≠ 0 := norm_ne_zero_iff.mp (by rw [NonUnitalStateGNS.norm_vector]; exact one_ne_zero)
  have hstate : NonUnitalCStarRepresentation.matrixCoefficientKernel
      (extremeGNSRepresentation rho) (isIrreducible_extremeGNSRepresentation rho) xi xi hxi hxi =
        extremeKernel ⟨extremeAbsoluteState rho,
          mem_extremePoints_dual_closedBall_of_isPureNonUnitalState _ hpure⟩ := by
    apply Subtype.ext
    change ((NonUnitalCStarRepresentation.matrixCoefficient
      (NonUnitalStateGNS.representation phi hpure.1) xi xi).ker : Set A) = (phi.ker : Set A)
    rw [NonUnitalStateGNS.matrixCoefficient_representation]
  rw [← hpoint, ← hstate]
  exact NonUnitalCStarRepresentation.related_matrixCoefficientKernel
    (extremeGNSRepresentation rho) (isIrreducible_extremeGNSRepresentation rho)
    x y xi xi hx hy hxi hxi

/-- Paper 5.10: the WHOLE component is the family of absolute-state GNS coefficient kernels. -/
theorem component_extremeKernel_eq_matrixCoefficientKernelFamily
    (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    (NormedSpace.geometricStructureClosure ℂ A).component (extremeKernel rho) =
      NonUnitalCStarRepresentation.matrixCoefficientKernelFamily (extremeGNSRepresentation rho)
        (isIrreducible_extremeGNSRepresentation rho) := by
  obtain ⟨x, y, hx, hy, hpoint⟩ := exists_matrixCoefficientKernel_extremeGNSRepresentation_eq rho
  rw [← hpoint]
  exact NonUnitalCStarRepresentation.component_matrixCoefficientKernel_eq_family
    (extremeGNSRepresentation rho) (isIrreducible_extremeGNSRepresentation rho) x y hx hy

/-- The component intersection on the received geometric spectrum is the actual
representation kernel of the absolute-state GNS action. -/
theorem geometricSpectrumKernel_toGeometricSpectrum_extremeKernel
    (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    NormedSpace.geometricSpectrumKernel ℂ A (NormedSpace.toGeometricSpectrum ℂ A (extremeKernel rho)) =
      ((absoluteStateContinuousMap (extremeGNSRepresentation rho)).ker : Set A) := by
  obtain ⟨x, y, hx, hy, hpoint⟩ := exists_matrixCoefficientKernel_extremeGNSRepresentation_eq rho
  rw [← hpoint]
  exact NonUnitalCStarRepresentation.geometricSpectrumKernel_toGeometricSpectrum_matrixCoefficientKernel
    (extremeGNSRepresentation rho) (isIrreducible_extremeGNSRepresentation rho) x y hx hy

/-- Literal gamma interface for subsequent spectral-topology work; no injectivity
of gamma and no comparison topology are concluded from this equality. -/
theorem geometricSpectrumToPrimitive_toGeometricSpectrum_extremeKernel_val
    (rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    (NormedSpace.geometricSpectrumToPrimitive ℂ A
      (NormedSpace.toGeometricSpectrum ℂ A (extremeKernel rho))).val =
      ((absoluteStateContinuousMap (extremeGNSRepresentation rho)).ker : Set A) := by
  rw [NormedSpace.geometricSpectrumToPrimitive_val]
  exact geometricSpectrumKernel_toGeometricSpectrum_extremeKernel rho

/-- Every actual geometric-spectrum point has an extreme kernel representative. -/
theorem exists_toGeometricSpectrum_extremeKernel_eq (C : NormedSpace.GeometricSpectrum ℂ A) :
    ∃ rho : (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ,
      NormedSpace.toGeometricSpectrum ℂ A (extremeKernel rho) = C := by
  obtain ⟨I, rfl⟩ := NormedSpace.toGeometricSpectrum_surjective ℂ A C
  obtain ⟨rho, rfl⟩ := extremeKernel_surjective I
  exact ⟨rho, rfl⟩

/-- A pure state is its own absolute state; translation by the unit gives the
positive translate to which the proved uniqueness applies. -/
theorem extremeAbsoluteState_eq_of_isPureNonUnitalState
    (phi : StrongDual ℂ A) (hpure : IsPureNonUnitalState A phi) :
    extremeAbsoluteState ⟨phi, mem_extremePoints_dual_closedBall_of_isPureNonUnitalState phi hpure⟩ = phi := by
  symm
  apply eq_extremeAbsoluteState_of_unitaryTranslate_eq _ phi hpure 1
  exact unitaryTranslate_one phi

/-- The final assertion of Paper 5.9, stated with the correct type: every
geometric-spectrum component contains a PURE-STATE KERNEL point of S(A). -/
theorem exists_pureState_kernel_mem_geometricSpectrum (C : NormedSpace.GeometricSpectrum ℂ A) :
    ∃ (phi : StrongDual ℂ A) (hpure : IsPureNonUnitalState A phi),
      extremeKernel ⟨phi, mem_extremePoints_dual_closedBall_of_isPureNonUnitalState phi hpure⟩ ∈ C.val := by
  obtain ⟨rho, rfl⟩ := exists_toGeometricSpectrum_extremeKernel_eq C
  exact ⟨extremeAbsoluteState rho, isPureNonUnitalState_extremeAbsoluteState rho,
    related_extremeKernel_extremeAbsoluteState rho⟩

/-- Paper 5.10 specialized literally to a pure state and its actual GNS
representation, not to a second chosen state having an equal component. -/
theorem component_pureStateKernel_eq_matrixCoefficientKernelFamily
    (phi : StrongDual ℂ A) (hpure : IsPureNonUnitalState A phi) :
    (NormedSpace.geometricStructureClosure ℂ A).component
      (extremeKernel ⟨phi, mem_extremePoints_dual_closedBall_of_isPureNonUnitalState phi hpure⟩) =
      NonUnitalCStarRepresentation.matrixCoefficientKernelFamily
        (NonUnitalStateGNS.representation phi hpure.1)
        (NonUnitalStateGNS.isIrreducible_representation phi hpure.1 hpure) := by
  let xi := NonUnitalStateGNS.vector phi hpure.1
  have hxi : xi ≠ 0 := norm_ne_zero_iff.mp (by rw [NonUnitalStateGNS.norm_vector]; exact one_ne_zero)
  have hk : NonUnitalCStarRepresentation.matrixCoefficientKernel
      (NonUnitalStateGNS.representation phi hpure.1)
      (NonUnitalStateGNS.isIrreducible_representation phi hpure.1 hpure) xi xi hxi hxi =
        extremeKernel ⟨phi, mem_extremePoints_dual_closedBall_of_isPureNonUnitalState phi hpure⟩ := by
    apply Subtype.ext
    change ((NonUnitalCStarRepresentation.matrixCoefficient
      (NonUnitalStateGNS.representation phi hpure.1) xi xi).ker : Set A) = (phi.ker : Set A)
    rw [NonUnitalStateGNS.matrixCoefficient_representation]
  rw [← hk]
  exact NonUnitalCStarRepresentation.component_matrixCoefficientKernel_eq_family
    (NonUnitalStateGNS.representation phi hpure.1)
    (NonUnitalStateGNS.isIrreducible_representation phi hpure.1 hpure) xi xi hxi hxi

/-- The unit-vector version of the whole component formula in Paper 5.10. -/
theorem component_pureStateKernel_eq_setOf_exists_unit_vectors
    (phi : StrongDual ℂ A) (hpure : IsPureNonUnitalState A phi) :
    (NormedSpace.geometricStructureClosure ℂ A).component
      (extremeKernel ⟨phi, mem_extremePoints_dual_closedBall_of_isPureNonUnitalState phi hpure⟩) =
      {I : NormedSpace.GeometricStructureSpace ℂ A |
        ∃ x y : NonUnitalStateGNS.Space phi hpure.1, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
          ((NonUnitalCStarRepresentation.matrixCoefficient
            (NonUnitalStateGNS.representation phi hpure.1) x y).ker : Set A) = I.val} := by
  rw [component_pureStateKernel_eq_matrixCoefficientKernelFamily phi hpure]
  ext I
  exact NonUnitalCStarRepresentation.mem_matrixCoefficientKernelFamily_iff_exists_unit_vectors
    (NonUnitalStateGNS.representation phi hpure.1)
    (NonUnitalStateGNS.isIrreducible_representation phi hpure.1 hpure) I

/-- The pure-state form of J_C = ker(pi_phi) on the received gamma map. -/
theorem geometricSpectrumToPrimitive_toGeometricSpectrum_pureStateKernel_val
    (phi : StrongDual ℂ A) (hpure : IsPureNonUnitalState A phi) :
    (NormedSpace.geometricSpectrumToPrimitive ℂ A
      (NormedSpace.toGeometricSpectrum ℂ A
        (extremeKernel ⟨phi, mem_extremePoints_dual_closedBall_of_isPureNonUnitalState phi hpure⟩))).val =
      ((absoluteStateContinuousMap (NonUnitalStateGNS.representation phi hpure.1)).ker : Set A) := by
  change {a : A | ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
    I ∈ (NormedSpace.geometricStructureClosure ℂ A).component
      (extremeKernel ⟨phi, mem_extremePoints_dual_closedBall_of_isPureNonUnitalState phi hpure⟩) →
        a ∈ I.val} = _
  rw [component_pureStateKernel_eq_matrixCoefficientKernelFamily phi hpure]
  exact NonUnitalCStarRepresentation.setOf_forall_mem_matrixCoefficientKernelFamily_eq_ker
    (NonUnitalStateGNS.representation phi hpure.1)
    (NonUnitalStateGNS.isIrreducible_representation phi hpure.1 hpure)

end MathlibAnnex.Analysis.CStarAlgebra
