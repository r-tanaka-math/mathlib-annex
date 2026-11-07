import BanachGeometry.SequenceSpaces.L1Map

/-! Uniformly bounded coordinate linear maps on the actual heterogeneous ℓ₁
model, with the stated operator-norm bounds and coordinate evaluation formulas.
Local execution evidence is recorded in the external qualification receipts. -/

noncomputable section
open scoped ENNReal
namespace BanachGeometry
namespace L1Linear

universe u v w
variable {ι : Type u} {E : ι → Type v} {F : ι → Type w}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, NormedSpace ℝ (F i)]

theorem summable_image (T : ∀ i, E i →L[ℝ] F i) (C : ℝ)
    (hT : ∀ i, ‖T i‖ ≤ C) (x : L1Sum E) : Summable (fun i => ‖T i (x i)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
  · intro i
    exact ((T i).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))
  · exact (l1_summable x).mul_left C

def map (T : ∀ i, E i →L[ℝ] F i) (C : ℝ) (hT : ∀ i, ‖T i‖ ≤ C)
    (x : L1Sum E) : L1Sum F :=
  ⟨fun i => T i (x i), by
    apply (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).2
    simpa using summable_image T C hT x⟩

@[simp] theorem map_apply (T : ∀ i, E i →L[ℝ] F i) (C : ℝ)
    (hT : ∀ i, ‖T i‖ ≤ C) (x : L1Sum E) (i : ι) : map T C hT x i = T i (x i) := rfl

theorem norm_map_le (T : ∀ i, E i →L[ℝ] F i) (C : ℝ)
    (hT : ∀ i, ‖T i‖ ≤ C) (x : L1Sum E) : ‖map T C hT x‖ ≤ C * ‖x‖ := by
  rw [l1_norm_eq_tsum, l1_norm_eq_tsum]
  calc
    (∑' i, ‖map T C hT x i‖) ≤ ∑' i, C * ‖x i‖ := by
      apply Summable.tsum_le_tsum
      · intro i
        exact ((T i).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))
      · exact summable_image T C hT x
      · exact (l1_summable x).mul_left C
    _ = C * ∑' i, ‖x i‖ := by rw [tsum_mul_left]

def continuousLinearMap (T : ∀ i, E i →L[ℝ] F i) (C : ℝ)
    (hT : ∀ i, ‖T i‖ ≤ C) : L1Sum E →L[ℝ] L1Sum F :=
  ({ toFun := map T C hT
     map_add' := by intro x y; apply lp.ext; funext i; exact (T i).map_add _ _
     map_smul' := by intro a x; apply lp.ext; funext i; exact (T i).map_smul _ _ }
    : L1Sum E →ₗ[ℝ] L1Sum F).mkContinuous C (norm_map_le T C hT)

@[simp] theorem continuousLinearMap_apply (T : ∀ i, E i →L[ℝ] F i) (C : ℝ)
    (hT : ∀ i, ‖T i‖ ≤ C) (x : L1Sum E) (i : ι) :
    continuousLinearMap T C hT x i = T i (x i) := rfl

theorem norm_continuousLinearMap_le (T : ∀ i, E i →L[ℝ] F i) (C : ℝ)
    (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) : ‖continuousLinearMap T C hT‖ ≤ C :=
  (continuousLinearMap T C hT).opNorm_le_bound hC (norm_map_le T C hT)

theorem norm_map_eq (T : ∀ i, E i →L[ℝ] F i) (C : ℝ)
    (hT : ∀ i, ‖T i‖ ≤ C) (hiso : ∀ i x, ‖T i x‖ = ‖x‖) (x : L1Sum E) :
    ‖continuousLinearMap T C hT x‖ = ‖x‖ := by
  rw [l1_norm_eq_tsum, l1_norm_eq_tsum]
  apply tsum_congr
  intro i
  exact hiso i (x i)

end L1Linear
end BanachGeometry
