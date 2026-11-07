import BanachGeometry.SequenceSpaces.ScalarBasis
import BanachGeometry.Complemented.ConcreteDual
import BanachGeometry.SequenceSpaces.C0Linear
import Mathlib.Analysis.InnerProductSpace.Orthonormal

open scoped ENNReal

/-! Standard basis, column inclusions and a concrete scalar c₀ copy along
unit vectors. Source-level support for the no-c₀ graph argument. -/
noncomputable section
open Filter
namespace BanachGeometry
namespace CanonicalSequences

def l2Basis (k : ℕ) : ScalarL2 := lp.single 2 k (1 : ℝ)
@[simp] theorem norm_l2Basis (k : ℕ) : ‖l2Basis k‖ = 1 := by simp [l2Basis]

theorem orthonormal_l2Basis : Orthonormal ℝ l2Basis := by
  apply orthonormal_iff_ite.mpr
  intro j k
  simp [l2Basis, lp.inner_single_left, lp.single_apply, Pi.single_apply]

theorem weakNull_l2Basis : WeakNull l2Basis := by
  intro f
  let x := (InnerProductSpace.toDual ℝ ScalarL2).symm f
  have hx (k : ℕ) : f (l2Basis k) = x k := by
    rw [← InnerProductSpace.toDual_symm_apply]
    change inner ℝ x (lp.single 2 k (1 : ℝ)) = x k
    simp [lp.inner_single_right]
  simp_rw [hx]
  have hs : Summable (fun k => ‖x k‖ ^ 2) := by
    simpa using (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x).summable
  have ht := hs.tendsto_atTop_zero
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (ε^2) (sq_pos_of_pos hε)
  refine ⟨N, ?_⟩
  intro k hk
  have he := hN k hk
  rw [dist_zero_right, Real.norm_of_nonneg (sq_nonneg _)] at he
  rw [dist_zero_right]
  nlinarith [norm_nonneg (x k)]

def column (n : ℕ) : ScalarL2 →ₗᵢ[ℝ] C0L2 :=
  (C0Sum.homogeneousLinearIsometryEquiv ScalarL2).toLinearIsometry.comp
    (C0Sum.singleLinearIsometry (E := fun _ : ℕ => ScalarL2) n)

def multiply (v : ScalarL2) : ℝ →L[ℝ] ScalarL2 :=
  ({ toFun := fun r => r • v
     map_add' := by intro r s; exact add_smul r s v
     map_smul' := by intro r s; exact (smul_smul r s v).symm } : ℝ →ₗ[ℝ] ScalarL2).mkContinuous ‖v‖
    (by intro r; change ‖r • v‖ ≤ ‖v‖ * ‖r‖; rw [norm_smul]; exact le_of_eq (mul_comm _ _))

private theorem multiply_unit_opNorm_le (v : ScalarL2) (hv : ‖v‖ = 1) : ‖multiply v‖ ≤ 1 := by
  apply (multiply v).opNorm_le_bound zero_le_one
  intro r
  change ‖r • v‖ ≤ 1 * ‖r‖
  rw [norm_smul, hv, mul_one, one_mul]

def scalarCopy (t : ℕ → ScalarL2) (ht : ∀ j, ‖t j‖ = 1) : ScalarC0 →L[ℝ] C0L2 :=
  (C0Sum.homogeneousLinearIsometryEquiv ScalarL2).toLinearIsometry.toContinuousLinearMap.comp
    ((C0Linear.continuousLinearMap (fun j => multiply (t j)) 1 zero_le_one
      (fun j => multiply_unit_opNorm_le (t j) (ht j))).comp
      (C0Sum.homogeneousLinearIsometryEquiv ℝ).symm.toLinearIsometry.toContinuousLinearMap)

theorem norm_scalarCopy (t : ℕ → ScalarL2) (ht : ∀ j, ‖t j‖ = 1) (a : ScalarC0) :
    ‖scalarCopy t ht a‖ = ‖a‖ := by
  let x := (C0Sum.homogeneousLinearIsometryEquiv ℝ).symm a
  change ‖(C0Sum.homogeneousLinearIsometryEquiv ScalarL2)
    (C0Linear.continuousLinearMap (fun j => multiply (t j)) 1 zero_le_one
      (fun j => multiply_unit_opNorm_le (t j) (ht j)) x)‖ = _
  rw [LinearIsometryEquiv.norm_map]
  have hnorm : ‖C0Linear.continuousLinearMap (fun j => multiply (t j)) 1 zero_le_one
      (fun j => multiply_unit_opNorm_le (t j) (ht j)) x‖ = ‖x‖ := by
    rw [C0Sum.norm_eq_iSup, C0Sum.norm_eq_iSup]
    congr 1; funext j
    change ‖x j • t j‖ = ‖x j‖
    rw [norm_smul, ht j, mul_one]
  rw [hnorm]
  exact (C0Sum.homogeneousLinearIsometryEquiv ℝ).symm.norm_map a

theorem scalarCopy_single (t : ℕ → ScalarL2) (ht : ∀ j, ‖t j‖ = 1) (n : ℕ) (r : ℝ) :
    scalarCopy t ht ((C0Sum.homogeneousLinearIsometryEquiv ℝ) (C0Sum.single n r)) = r • column n (t n) := by
  have heval : C0Sum.singleLinearIsometry (E := fun _ : ℕ => ScalarL2) n (t n) =
      C0Sum.single n (t n) := rfl
  apply (C0Sum.homogeneousLinearIsometryEquiv ScalarL2).symm.injective
  apply C0Sum.ext
  intro j
  by_cases hj : j = n
  · subst j; simp [scalarCopy, column, multiply, heval]
  · simp [scalarCopy, column, multiply, heval, C0Sum.single_apply_ne (E := fun _ : ℕ => ℝ) n r hj,
      C0Sum.single_apply_ne (E := fun _ : ℕ => ScalarL2) n (t n) hj]

theorem scalarCopy_head (t : ℕ → ScalarL2) (ht : ∀ j, ‖t j‖ = 1) (n : ℕ) (a : ScalarC0) :
    scalarCopy t ht (scalarHead n a) = ∑ j ∈ Finset.range n, a j • column j (t j) := by
  change scalarCopy t ht ((C0Sum.homogeneousLinearIsometryEquiv ℝ)
    (C0Sum.head _ n _)) = _
  rw [C0Sum.head, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact scalarCopy_single t ht j (a j)

theorem norm_comp_scalarCopy_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (O : C0L2 →L[ℝ] F) (t : ℕ → ScalarL2) (ht : ∀ j, ‖t j‖ = 1)
    (η : ℕ → ℝ) (hη : ∀ j, 0 ≤ η j) (hs : Summable η)
    (hsmall : ∀ j, ‖O (column j (t j))‖ ≤ η j) (a : ScalarC0) :
    ‖O (scalarCopy t ht a)‖ ≤ (∑' j, η j) * ‖a‖ := by
  have hfin (n : ℕ) : ‖O (scalarCopy t ht (scalarHead n a))‖ ≤ (∑' j, η j) * ‖a‖ := by
    rw [scalarCopy_head, map_sum]
    apply (norm_sum_le _ _).trans
    calc
      (∑ j ∈ Finset.range n, ‖O (a j • column j (t j))‖) ≤ ∑ j ∈ Finset.range n, η j * ‖a‖ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [map_smul, norm_smul]
        exact (mul_le_mul (norm_apply_scalar_le a j) (hsmall j) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)
      _ = (∑ j ∈ Finset.range n, η j) * ‖a‖ := by rw [Finset.sum_mul]
      _ ≤ (∑' j, η j) * ‖a‖ := mul_le_mul_of_nonneg_right
        (hs.sum_le_tsum _ (fun j hj => hη j)) (norm_nonneg _)
  have hlim := ((O.comp (scalarCopy t ht)).continuous.tendsto a).comp (tendsto_scalarHead a)
  exact le_of_tendsto hlim.norm (Filter.Eventually.of_forall hfin)

end CanonicalSequences
end BanachGeometry
