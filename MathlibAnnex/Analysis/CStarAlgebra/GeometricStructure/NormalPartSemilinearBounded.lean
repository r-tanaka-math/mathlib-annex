/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartSemilinearRegularity
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Tactic.Linarith

/-!
# Continuous and bounded bundles for the same selected normal-part lifts

Continuity fields are filled only by the preceding regularity application.
The underlying functions AND inverse functions remain literally the selected
semilinear maps from `NormalPartSemilinearRealization`. Real-linear bundles
permit explicit operator-norm bounds without presupposing that the two complex
scalar maps agree. Identity and conjugation alternatives are also bundled
individually, still retaining the four possible pairs of scalar types.

The all-point and literal-kernel formulas below remain tied to the original e
with one global direct/swap orientation and its matching inverse.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped ComplexConjugate

namespace MathlibAnnex.Analysis.CStarAlgebra

local instance (σ : ℂ ≃+* ℂ) : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ
local instance (σ : ℂ ≃+* ℂ) : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [IsClosed (S : Set (H →L[ℂ] H))] [IsClosed (T : Set (K →L[ℂ] K))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
variable (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
variable (e : ClosureSpace.FiniteHomeomorph
  ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
  ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)))

variable (hdim : 3 ≤ Module.rank ℂ H)
variable (hH : ¬ FiniteDimensional ℂ H)
variable (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
  ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)

include hH hcont

/-- The SAME selected first lift, now with its proved two continuity fields. -/
def normalPartFirstContinuousSemilinearEquiv :
    ContinuousLinearEquiv (normalPartFirstScalarEquiv S T hS hT e hdim).toRingHom
      (σ' := (normalPartFirstScalarEquiv S T hS hT e hdim).symm.toRingHom) H K where
  toLinearEquiv := normalPartFirstSemilinearEquiv S T hS hT e hdim
  continuous_toFun := continuous_normalPartFirstSemilinearEquiv S T hS hT e hdim hH hcont
  continuous_invFun := continuous_symm_normalPartFirstSemilinearEquiv S T hS hT e hdim hH hcont

@[simp]
theorem normalPartFirstContinuousSemilinearEquiv_apply (x : H) :
    normalPartFirstContinuousSemilinearEquiv S T hS hT e hdim hH hcont x =
      normalPartFirstSemilinearEquiv S T hS hT e hdim x := rfl

@[simp]
theorem normalPartFirstContinuousSemilinearEquiv_symm_apply (z : K) :
    (normalPartFirstContinuousSemilinearEquiv S T hS hT e hdim hH hcont).symm z =
      (normalPartFirstSemilinearEquiv S T hS hT e hdim).symm z := rfl

/-- Real linearization of the SAME selected first map. It changes neither
function; the already proved scalar continuity is used to fix real scalars. -/
def normalPartFirstRealContinuousLinearEquiv : H ≃L[ℝ] K where
  toLinearEquiv := LinearEquiv.realLinearEquivOfContinuousRingEquiv
    (normalPartFirstSemilinearEquiv S T hS hT e hdim)
    (continuous_normalPartFirstScalarEquiv S T hS hT e hdim hH hcont)
  continuous_toFun := continuous_normalPartFirstSemilinearEquiv S T hS hT e hdim hH hcont
  continuous_invFun := continuous_symm_normalPartFirstSemilinearEquiv S T hS hT e hdim hH hcont

@[simp]
theorem normalPartFirstRealContinuousLinearEquiv_apply (x : H) :
    normalPartFirstRealContinuousLinearEquiv S T hS hT e hdim hH hcont x =
      normalPartFirstSemilinearEquiv S T hS hT e hdim x := rfl

@[simp]
theorem normalPartFirstRealContinuousLinearEquiv_symm_apply (z : K) :
    (normalPartFirstRealContinuousLinearEquiv S T hS hT e hdim hH hcont).symm z =
      (normalPartFirstSemilinearEquiv S T hS hT e hdim).symm z := rfl

/-- Genuine complex-linear or conjugate-linear continuous bundles for the same
first selected function, with its same inverse. No new lift is chosen. -/
theorem exists_continuousLinearEquiv_or_conj_eq_normalPartFirstSemilinearEquiv :
    let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
    (∃ f : H ≃L[ℂ] K, (f : H → K) = U ∧ (f.symm : K → H) = U.symm) ∨
    (∃ f : ContinuousLinearEquiv (starRingAut (R := ℂ)).toRingHom
        (σ' := (starRingAut (R := ℂ)).symm.toRingHom) H K,
      (f : H → K) = U ∧ (f.symm : K → H) = U.symm) := by
  let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
  rcases normalPartFirstScalarEquiv_eq_refl_or_star
      S T hS hT e hdim hH hcont with hs | hs
  · left
    let f : H ≃L[ℂ] K :=
      { toFun := U
        invFun := U.symm
        left_inv := U.symm_apply_apply
        right_inv := U.apply_symm_apply
        map_add' := U.map_add
        map_smul' := by
          intro a x
          change U (a • x) = a • U x
          rw [U.map_smulₛₗ]
          change normalPartFirstScalarEquiv S T hS hT e hdim a • U x = a • U x
          have ha : normalPartFirstScalarEquiv S T hS hT e hdim a = a :=
            congrArg (fun ρ : ℂ ≃+* ℂ => ρ a) hs
          rw [ha]
        continuous_toFun := continuous_normalPartFirstSemilinearEquiv
          S T hS hT e hdim hH hcont
        continuous_invFun := continuous_symm_normalPartFirstSemilinearEquiv
          S T hS hT e hdim hH hcont }
    exact ⟨f, rfl, rfl⟩
  · right
    let f : ContinuousLinearEquiv (starRingAut (R := ℂ)).toRingHom
        (σ' := (starRingAut (R := ℂ)).symm.toRingHom) H K :=
      { toFun := U
        invFun := U.symm
        left_inv := U.symm_apply_apply
        right_inv := U.apply_symm_apply
        map_add' := U.map_add
        map_smul' := by
          intro a x
          change U (a • x) = star a • U x
          rw [U.map_smulₛₗ]
          change normalPartFirstScalarEquiv S T hS hT e hdim a • U x = star a • U x
          have ha : normalPartFirstScalarEquiv S T hS hT e hdim a = star a :=
            congrArg (fun ρ : ℂ ≃+* ℂ => ρ a) hs
          rw [ha]
        continuous_toFun := continuous_normalPartFirstSemilinearEquiv
          S T hS hT e hdim hH hcont
        continuous_invFun := continuous_symm_normalPartFirstSemilinearEquiv
          S T hS hT e hdim hH hcont }
    exact ⟨f, rfl, rfl⟩

/-- The SAME selected second lift, now with its proved two continuity fields. -/
def normalPartSecondContinuousSemilinearEquiv :
    ContinuousLinearEquiv (normalPartSecondScalarEquiv S T hS hT e hdim).toRingHom
      (σ' := (normalPartSecondScalarEquiv S T hS hT e hdim).symm.toRingHom) H K where
  toLinearEquiv := normalPartSecondSemilinearEquiv S T hS hT e hdim
  continuous_toFun := continuous_normalPartSecondSemilinearEquiv S T hS hT e hdim hH hcont
  continuous_invFun := continuous_symm_normalPartSecondSemilinearEquiv S T hS hT e hdim hH hcont

@[simp]
theorem normalPartSecondContinuousSemilinearEquiv_apply (x : H) :
    normalPartSecondContinuousSemilinearEquiv S T hS hT e hdim hH hcont x =
      normalPartSecondSemilinearEquiv S T hS hT e hdim x := rfl

@[simp]
theorem normalPartSecondContinuousSemilinearEquiv_symm_apply (z : K) :
    (normalPartSecondContinuousSemilinearEquiv S T hS hT e hdim hH hcont).symm z =
      (normalPartSecondSemilinearEquiv S T hS hT e hdim).symm z := rfl

/-- Real linearization of the SAME selected second map. It changes neither
function; the already proved scalar continuity is used to fix real scalars. -/
def normalPartSecondRealContinuousLinearEquiv : H ≃L[ℝ] K where
  toLinearEquiv := LinearEquiv.realLinearEquivOfContinuousRingEquiv
    (normalPartSecondSemilinearEquiv S T hS hT e hdim)
    (continuous_normalPartSecondScalarEquiv S T hS hT e hdim hH hcont)
  continuous_toFun := continuous_normalPartSecondSemilinearEquiv S T hS hT e hdim hH hcont
  continuous_invFun := continuous_symm_normalPartSecondSemilinearEquiv S T hS hT e hdim hH hcont

@[simp]
theorem normalPartSecondRealContinuousLinearEquiv_apply (x : H) :
    normalPartSecondRealContinuousLinearEquiv S T hS hT e hdim hH hcont x =
      normalPartSecondSemilinearEquiv S T hS hT e hdim x := rfl

@[simp]
theorem normalPartSecondRealContinuousLinearEquiv_symm_apply (z : K) :
    (normalPartSecondRealContinuousLinearEquiv S T hS hT e hdim hH hcont).symm z =
      (normalPartSecondSemilinearEquiv S T hS hT e hdim).symm z := rfl

/-- Genuine complex-linear or conjugate-linear continuous bundles for the same
second selected function, with its same inverse. No new lift is chosen. -/
theorem exists_continuousLinearEquiv_or_conj_eq_normalPartSecondSemilinearEquiv :
    let U := normalPartSecondSemilinearEquiv S T hS hT e hdim
    (∃ f : H ≃L[ℂ] K, (f : H → K) = U ∧ (f.symm : K → H) = U.symm) ∨
    (∃ f : ContinuousLinearEquiv (starRingAut (R := ℂ)).toRingHom
        (σ' := (starRingAut (R := ℂ)).symm.toRingHom) H K,
      (f : H → K) = U ∧ (f.symm : K → H) = U.symm) := by
  let U := normalPartSecondSemilinearEquiv S T hS hT e hdim
  rcases normalPartSecondScalarEquiv_eq_refl_or_star
      S T hS hT e hdim hH hcont with hs | hs
  · left
    let f : H ≃L[ℂ] K :=
      { toFun := U
        invFun := U.symm
        left_inv := U.symm_apply_apply
        right_inv := U.apply_symm_apply
        map_add' := U.map_add
        map_smul' := by
          intro a x
          change U (a • x) = a • U x
          rw [U.map_smulₛₗ]
          change normalPartSecondScalarEquiv S T hS hT e hdim a • U x = a • U x
          have ha : normalPartSecondScalarEquiv S T hS hT e hdim a = a :=
            congrArg (fun ρ : ℂ ≃+* ℂ => ρ a) hs
          rw [ha]
        continuous_toFun := continuous_normalPartSecondSemilinearEquiv
          S T hS hT e hdim hH hcont
        continuous_invFun := continuous_symm_normalPartSecondSemilinearEquiv
          S T hS hT e hdim hH hcont }
    exact ⟨f, rfl, rfl⟩
  · right
    let f : ContinuousLinearEquiv (starRingAut (R := ℂ)).toRingHom
        (σ' := (starRingAut (R := ℂ)).symm.toRingHom) H K :=
      { toFun := U
        invFun := U.symm
        left_inv := U.symm_apply_apply
        right_inv := U.apply_symm_apply
        map_add' := U.map_add
        map_smul' := by
          intro a x
          change U (a • x) = star a • U x
          rw [U.map_smulₛₗ]
          change normalPartSecondScalarEquiv S T hS hT e hdim a • U x = star a • U x
          have ha : normalPartSecondScalarEquiv S T hS hT e hdim a = star a :=
            congrArg (fun ρ : ℂ ≃+* ℂ => ρ a) hs
          rw [ha]
        continuous_toFun := continuous_normalPartSecondSemilinearEquiv
          S T hS hT e hdim hH hcont
        continuous_invFun := continuous_symm_normalPartSecondSemilinearEquiv
          S T hS hT e hdim hH hcont }
    exact ⟨f, rfl, rfl⟩

/-- One explicit positive real constant bounds both selected maps and both
inverses. Operator norms here are those of the proved REAL linear bundles. -/
def normalPartSemilinearNormBound : ℝ :=
  let U := normalPartFirstRealContinuousLinearEquiv S T hS hT e hdim hH hcont
  let V := normalPartSecondRealContinuousLinearEquiv S T hS hT e hdim hH hcont
  ‖U.toContinuousLinearMap‖ + ‖U.symm.toContinuousLinearMap‖ +
    ‖V.toContinuousLinearMap‖ + ‖V.symm.toContinuousLinearMap‖ + 1

/-- Positivity is proved for the actual selected constant, not assumed. -/
theorem normalPartSemilinearNormBound_pos :
    0 < normalPartSemilinearNormBound S T hS hT e hdim hH hcont := by
  let U := normalPartFirstRealContinuousLinearEquiv S T hS hT e hdim hH hcont
  let V := normalPartSecondRealContinuousLinearEquiv S T hS hT e hdim hH hcont
  change 0 < ‖U.toContinuousLinearMap‖ + ‖U.symm.toContinuousLinearMap‖ +
    ‖V.toContinuousLinearMap‖ + ‖V.symm.toContinuousLinearMap‖ + 1
  linarith [norm_nonneg U.toContinuousLinearMap, norm_nonneg U.symm.toContinuousLinearMap,
    norm_nonneg V.toContinuousLinearMap, norm_nonneg V.symm.toContinuousLinearMap]

/-- Explicit estimates for the original selected functions in all four directions. -/
theorem normalPart_semilinear_factors_norm_le :
    let C := normalPartSemilinearNormBound S T hS hT e hdim hH hcont
    let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
    let V := normalPartSecondSemilinearEquiv S T hS hT e hdim
    (∀ x, ‖U x‖ ≤ C * ‖x‖) ∧ (∀ z, ‖U.symm z‖ ≤ C * ‖z‖) ∧
      (∀ x, ‖V x‖ ≤ C * ‖x‖) ∧ (∀ z, ‖V.symm z‖ ≤ C * ‖z‖) := by
  let U := normalPartFirstRealContinuousLinearEquiv S T hS hT e hdim hH hcont
  let V := normalPartSecondRealContinuousLinearEquiv S T hS hT e hdim hH hcont
  let C := normalPartSemilinearNormBound S T hS hT e hdim hH hcont
  have hC : C = ‖U.toContinuousLinearMap‖ + ‖U.symm.toContinuousLinearMap‖ +
      ‖V.toContinuousLinearMap‖ + ‖V.symm.toContinuousLinearMap‖ + 1 := rfl
  have h₁ : ‖U.toContinuousLinearMap‖ ≤ C := by
    linarith [norm_nonneg U.symm.toContinuousLinearMap, norm_nonneg V.toContinuousLinearMap,
      norm_nonneg V.symm.toContinuousLinearMap]
  have h₂ : ‖U.symm.toContinuousLinearMap‖ ≤ C := by
    linarith [norm_nonneg U.toContinuousLinearMap, norm_nonneg V.toContinuousLinearMap,
      norm_nonneg V.symm.toContinuousLinearMap]
  have h₃ : ‖V.toContinuousLinearMap‖ ≤ C := by
    linarith [norm_nonneg U.toContinuousLinearMap, norm_nonneg U.symm.toContinuousLinearMap,
      norm_nonneg V.symm.toContinuousLinearMap]
  have h₄ : ‖V.symm.toContinuousLinearMap‖ ≤ C := by
    linarith [norm_nonneg U.toContinuousLinearMap, norm_nonneg U.symm.toContinuousLinearMap,
      norm_nonneg V.toContinuousLinearMap]
  refine ⟨fun x => ?_, fun z => ?_, fun x => ?_, fun z => ?_⟩
  · exact (U.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right h₁ (norm_nonneg x))
  · exact (U.symm.toContinuousLinearMap.le_opNorm z).trans
      (mul_le_mul_of_nonneg_right h₂ (norm_nonneg z))
  · exact (V.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right h₃ (norm_nonneg x))
  · exact (V.symm.toContinuousLinearMap.le_opNorm z).trans
      (mul_le_mul_of_nonneg_right h₄ (norm_nonneg z))

/-- The inverse estimates give lower bounds for the SAME selected maps. -/
theorem norm_le_mul_normalPart_semilinear_factors :
    let C := normalPartSemilinearNormBound S T hS hT e hdim hH hcont
    let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
    let V := normalPartSecondSemilinearEquiv S T hS hT e hdim
    (∀ x, ‖x‖ ≤ C * ‖U x‖) ∧ (∀ x, ‖x‖ ≤ C * ‖V x‖) := by
  let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
  let V := normalPartSecondSemilinearEquiv S T hS hT e hdim
  have h := normalPart_semilinear_factors_norm_le S T hS hT e hdim hH hcont
  constructor
  · intro x
    simpa only [U, LinearEquiv.symm_apply_apply] using h.2.1 (U x)
  · intro x
    simpa only [V, LinearEquiv.symm_apply_apply] using h.2.2.2 (V x)

/-- All-point evaluation and its inverse in the SAME global orientation, after continuous packaging. -/
theorem normalPart_continuous_semilinear_factors_evaluation :
    let U := normalPartFirstContinuousSemilinearEquiv S T hS hT e hdim hH hcont
    let V := normalPartSecondContinuousSemilinearEquiv S T hS hT e hdim hH hcont
    ((∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
      e.toEquiv (normalPartPoint S hS x y hx hy) =
        normalPartPoint T hT (U x) (V y)
          (by simpa only [map_zero] using U.injective.ne hx)
          (by simpa only [map_zero] using V.injective.ne hy)) ∧
     (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
      e.toEquiv.symm (normalPartPoint T hT z w hz hw) =
        normalPartPoint S hS (U.symm z) (V.symm w)
          (by simpa only [map_zero] using U.symm.injective.ne hz)
          (by simpa only [map_zero] using V.symm.injective.ne hw))) ∨
    ((∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
      e.toEquiv (normalPartPoint S hS x y hx hy) =
        normalPartPoint T hT (V y) (U x)
          (by simpa only [map_zero] using V.injective.ne hy)
          (by simpa only [map_zero] using U.injective.ne hx)) ∧
     (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
      e.toEquiv.symm (normalPartPoint T hT z w hz hw) =
        normalPartPoint S hS (U.symm w) (V.symm z)
          (by simpa only [map_zero] using U.symm.injective.ne hw)
          (by simpa only [map_zero] using V.symm.injective.ne hz))) := by
  simpa only [normalPartFirstContinuousSemilinearEquiv_apply,
    normalPartSecondContinuousSemilinearEquiv_apply,
    normalPartFirstContinuousSemilinearEquiv_symm_apply,
    normalPartSecondContinuousSemilinearEquiv_symm_apply] using
    normalPart_semilinear_factors_evaluation S T hS hT e hdim

/-- Literal underlying kernel formulas are unchanged by the continuous packaging. -/
theorem normalPart_continuous_semilinear_factors_kernel_evaluation :
    let U := normalPartFirstContinuousSemilinearEquiv S T hS hT e hdim hH hcont
    let V := normalPartSecondContinuousSemilinearEquiv S T hS hT e hdim hH hcont
    ((∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
      (e.toEquiv (normalPartPoint S hS x y hx hy)).val.val =
        {b : T | inner ℂ (V y) ((b : K →L[ℂ] K) (U x)) = 0}) ∧
     (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
      (e.toEquiv.symm (normalPartPoint T hT z w hz hw)).val.val =
        {a : S | inner ℂ (V.symm w) ((a : H →L[ℂ] H) (U.symm z)) = 0})) ∨
    ((∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
      (e.toEquiv (normalPartPoint S hS x y hx hy)).val.val =
        {b : T | inner ℂ (U x) ((b : K →L[ℂ] K) (V y)) = 0}) ∧
     (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
      (e.toEquiv.symm (normalPartPoint T hT z w hz hw)).val.val =
        {a : S | inner ℂ (V.symm z) ((a : H →L[ℂ] H) (U.symm w)) = 0})) := by
  simpa only [normalPartFirstContinuousSemilinearEquiv_apply,
    normalPartSecondContinuousSemilinearEquiv_apply,
    normalPartFirstContinuousSemilinearEquiv_symm_apply,
    normalPartSecondContinuousSemilinearEquiv_symm_apply] using
    normalPart_semilinear_factors_kernel_evaluation S T hS hT e hdim

/-- A source-infinite-dimensional entry point: the rank proof is supplied by the
actual dimension comparison, and all four bounds use the already selected lifts. -/
theorem exists_bounds_normalPart_semilinear_factors_of_not_finiteDimensional :
    let hd := (three_le_rank_of_normalPart_finiteHomeomorph S T hS hT e hH).1
    let U := normalPartFirstSemilinearEquiv S T hS hT e hd
    let V := normalPartSecondSemilinearEquiv S T hS hT e hd
    ∃ C : ℝ, 0 < C ∧
      (∀ x, ‖U x‖ ≤ C * ‖x‖) ∧ (∀ z, ‖U.symm z‖ ≤ C * ‖z‖) ∧
      (∀ x, ‖V x‖ ≤ C * ‖x‖) ∧ (∀ z, ‖V.symm z‖ ≤ C * ‖z‖) := by
  let hd := (three_le_rank_of_normalPart_finiteHomeomorph S T hS hT e hH).1
  exact ⟨normalPartSemilinearNormBound S T hS hT e hd hH hcont,
    normalPartSemilinearNormBound_pos S T hS hT e hd hH hcont,
    normalPart_semilinear_factors_norm_le S T hS hT e hd hH hcont⟩

end MathlibAnnex.Analysis.CStarAlgebra
