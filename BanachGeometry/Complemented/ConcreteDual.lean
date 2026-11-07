import BanachGeometry.SequenceSpaces.C0Dual
import BanachGeometry.SequenceSpaces.C0Adapters
import BanachGeometry.HilbertSums.L2Separable
import BanachGeometry.WeakSequences.CountableExclusion
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Concrete dual separability at the frozen common boundary. These are
constructed proofs, not extra hypotheses of QuantitativeHilbertData.
Execution evidence is recorded in the external receipts. -/
noncomputable section
open TopologicalSpace
namespace BanachGeometry
namespace DualTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

def precompose (T : F →L[ℝ] E) : (E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) :=
  ({ toFun := fun f => f.comp T
     map_add' := by intro f g; ext x; rfl
     map_smul' := by intro r f; ext x; rfl } : (E →L[ℝ] ℝ) →ₗ[ℝ] (F →L[ℝ] ℝ)).mkContinuous ‖T‖
    (fun f => (f.opNorm_comp_le T).trans_eq (mul_comm _ _))

def congr (e : E ≃L[ℝ] F) : (E →L[ℝ] ℝ) ≃L[ℝ] (F →L[ℝ] ℝ) where
  toLinearEquiv := {
    toFun := precompose e.symm.toContinuousLinearMap
    invFun := precompose e.toContinuousLinearMap
    left_inv := by intro f; ext x; change f (e.symm (e x)) = f x; rw [e.symm_apply_apply]
    right_inv := by intro f; ext x; change f (e (e.symm x)) = f x; rw [e.apply_symm_apply]
    map_add' := (precompose e.symm.toContinuousLinearMap).map_add
    map_smul' := (precompose e.symm.toContinuousLinearMap).map_smul }
  continuous_toFun := (precompose e.symm.toContinuousLinearMap).continuous
  continuous_invFun := (precompose e.toContinuousLinearMap).continuous

theorem separable_of_equiv (e : E ≃L[ℝ] F) [SeparableSpace (E →L[ℝ] ℝ)] :
    SeparableSpace (F →L[ℝ] ℝ) :=
  (congr e).surjective.denseRange.separableSpace (congr e).continuous

theorem separable_of_split (J : E →L[ℝ] F) (P : F →L[ℝ] E)
    (hPJ : P.comp J = ContinuousLinearMap.id ℝ E) [SeparableSpace (F →L[ℝ] ℝ)] :
    SeparableSpace (E →L[ℝ] ℝ) := by
  have hs : Function.Surjective (precompose J) := by
    intro f
    refine ⟨f.comp P, ?_⟩
    ext x
    have hx := congrArg (fun T : E →L[ℝ] E => T x) hPJ
    exact congrArg f hx
  exact hs.denseRange.separableSpace (precompose J).continuous

theorem separableSpace_dual_submodule (p : Submodule ℝ E) [SeparableSpace (E →L[ℝ] ℝ)] :
    SeparableSpace (p →L[ℝ] ℝ) := by
  have hs : Function.Surjective (precompose p.subtypeL) := by
    intro f
    obtain ⟨g, hg, hnorm⟩ := exists_extension_norm_eq p f
    refine ⟨g, ?_⟩
    ext x
    exact hg x
  exact hs.denseRange.separableSpace (precompose p.subtypeL).continuous

theorem separableSpace_dual_hilbert (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [CompleteSpace W] [SeparableSpace W] : SeparableSpace (W →L[ℝ] ℝ) :=
  (InnerProductSpace.toDual ℝ W).surjective.denseRange.separableSpace (InnerProductSpace.toDual ℝ W).continuous

end DualTransport

theorem separableSpace_dual_scalarC0 : SeparableSpace (ScalarC0 →L[ℝ] ℝ) := by
  letI : SeparableSpace (ℝ →L[ℝ] ℝ) := DualTransport.separableSpace_dual_hilbert ℝ
  letI : SeparableSpace (C0Dual.Dual (fun _ : ℕ => ℝ)) := C0Dual.separableSpace_dual _
  exact DualTransport.separable_of_equiv (C0Sum.homogeneousLinearIsometryEquiv ℝ).toContinuousLinearEquiv

theorem separableSpace_dual_c0L2 : SeparableSpace (C0L2 →L[ℝ] ℝ) := by
  letI : SeparableSpace ScalarL2 := HilbertSums.lp_two_separable
  letI : SeparableSpace (ScalarL2 →L[ℝ] ℝ) := DualTransport.separableSpace_dual_hilbert ScalarL2
  letI : SeparableSpace (C0Dual.Dual (fun _ : ℕ => ScalarL2)) := C0Dual.separableSpace_dual _
  exact DualTransport.separable_of_equiv (C0Sum.homogeneousLinearIsometryEquiv ScalarL2).toContinuousLinearEquiv

namespace AlmostIsometricFamily
theorem countable_noCopy_of_finite_exclusion (d : AlmostIsometricFamily) (h4 : d.ExcludesFiniteSumCopy) (indices : ℕ → ℕ) :
    ¬ ContainsLinearCopy C0L2 (L1Sum (fun i => (d.Y (indices i)).Carrier)) :=
  d.countable_noCopy h4 separableSpace_dual_c0L2 indices
end AlmostIsometricFamily

end BanachGeometry
