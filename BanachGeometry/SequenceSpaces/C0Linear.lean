import BanachGeometry.SequenceSpaces.C0Sum

/-! Uniform bounded linear coordinate maps on the retained heterogeneous c₀
model, with norm-null membership proved explicitly.
Execution evidence is recorded in the external receipts. -/

noncomputable section
open Filter
namespace BanachGeometry
namespace C0Linear
variable {ι : Type*} {A B : ι → Type*}
    [∀ i, NormedAddCommGroup (A i)] [∀ i, NormedSpace ℝ (A i)]
    [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℝ (B i)]

def map (T : ∀ i, A i →L[ℝ] B i) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (x : C0Sum A) : C0Sum B :=
  C0Sum.ofBound (fun i => T i (x i)) (by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using (x.null.const_mul C))
    · intro i; exact norm_nonneg _
    · intro i
      exact ((T i).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _)))
    (C * ‖x‖) (fun i => ((T i).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (x.norm_apply_le i) hC)))

@[simp] theorem map_apply (T : ∀ i, A i →L[ℝ] B i) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (x : C0Sum A) (i : ι) : map T C hC hT x i = T i (x i) := rfl

theorem norm_map_le (T : ∀ i, A i →L[ℝ] B i) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) (x : C0Sum A) : ‖map T C hC hT x‖ ≤ C * ‖x‖ := by
  apply C0Sum.norm_le (mul_nonneg hC (norm_nonneg _))
  intro i
  exact ((T i).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (x.norm_apply_le i) hC))

def continuousLinearMap (T : ∀ i, A i →L[ℝ] B i) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) : C0Sum A →L[ℝ] C0Sum B :=
  ({ toFun := map T C hC hT
     map_add' := by intro x y; apply C0Sum.ext; intro i; exact (T i).map_add _ _
     map_smul' := by intro a x; apply C0Sum.ext; intro i; exact (T i).map_smul _ _ }
    : C0Sum A →ₗ[ℝ] C0Sum B).mkContinuous C (norm_map_le T C hC hT)

@[simp] theorem continuousLinearMap_apply (T : ∀ i, A i →L[ℝ] B i)
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) (x : C0Sum A) (i : ι) :
    continuousLinearMap T C hC hT x i = T i (x i) := rfl

end C0Linear
end BanachGeometry
