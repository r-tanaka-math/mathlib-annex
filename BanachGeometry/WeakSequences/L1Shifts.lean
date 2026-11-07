import BanachGeometry.WeakSequences.L1Tails

open scoped ENNReal

/-! The shifts act only on a homogeneous ℓ₁ sum. They are never applied to
the heterogeneous outer c₀ coordinates in the localization argument. -/

noncomputable section
namespace BanachGeometry
namespace L1Shifts
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev F := L1Sum (fun _ : ℕ => E)

def rawUp (m : ℕ) (x : F E) (i : ℕ) : E := if i < m then 0 else x (i - m)

theorem rawUp_add (m : ℕ) (x : F E) (i : ℕ) : rawUp E m x (i + m) = x i := by
  simp only [rawUp, if_neg (by omega : ¬ i + m < m), Nat.add_sub_cancel]

theorem summable_rawUp (m : ℕ) (x : F E) : Summable (fun i => ‖rawUp E m x i‖) := by
  apply (summable_nat_add_iff m).1
  simpa only [rawUp_add] using l1_summable x

def up (m : ℕ) (x : F E) : F E := ⟨rawUp E m x, by
  apply (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).2
  simpa only [ENNReal.toReal_one, Real.rpow_one] using summable_rawUp E m x⟩

def down (m : ℕ) (x : F E) : F E := ⟨fun i => x (i + m), by
  apply (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).2
  simpa only [ENNReal.toReal_one, Real.rpow_one] using
    (summable_nat_add_iff m).2 (l1_summable x)⟩

@[simp] theorem up_apply (m : ℕ) (x : F E) (i : ℕ) :
    up E m x i = if i < m then 0 else x (i - m) := rfl
@[simp] theorem down_apply (m : ℕ) (x : F E) (i : ℕ) : down E m x i = x (i + m) := rfl

theorem norm_up (m : ℕ) (x : F E) : ‖up E m x‖ = ‖x‖ := by
  have hs := (summable_rawUp E m x).sum_add_tsum_nat_add m
  have hz : (∑ i ∈ Finset.range m, ‖rawUp E m x i‖) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [rawUp, if_pos (Finset.mem_range.mp hi), norm_zero]
  rw [hz, zero_add] at hs
  rw [l1_norm_eq_tsum, l1_norm_eq_tsum]
  change (∑' i, ‖rawUp E m x i‖) = ∑' i, ‖x i‖
  exact hs.symm.trans (tsum_congr (fun i => congrArg norm (rawUp_add E m x i)))

theorem norm_down_eq_tail (m : ℕ) (x : F E) :
    ‖down E m x‖ = ‖L1Tails.tail (fun _ : ℕ => E) m x‖ := by
  have hs := (l1_summable x).sum_add_tsum_nat_add m
  rw [l1_norm_eq_tsum, L1Tails.norm_tail_eq_sub_sum, l1_norm_eq_tsum]
  change (∑' i, ‖x (i + m)‖) = (∑' i, ‖x i‖) - ∑ i ∈ Finset.range m, ‖x i‖
  linarith

def upCLM (m : ℕ) : F E →L[ℝ] F E :=
  ({ toFun := up E m
     map_add' := by
       intro x y; apply lp.ext; funext i
       simp only [up_apply, lp.coeFn_add, Pi.add_apply]
       split_ifs <;> simp
     map_smul' := by
       intro a x; apply lp.ext; funext i
       simp only [up_apply, lp.coeFn_smul, Pi.smul_apply]
       split_ifs <;> simp } : F E →ₗ[ℝ] F E).mkContinuous 1
    (fun x => by
      change ‖up E m x‖ ≤ 1 * ‖x‖
      simp only [norm_up, one_mul]
      exact le_rfl)

def downCLM (m : ℕ) : F E →L[ℝ] F E :=
  ({ toFun := down E m
     map_add' := by intro x y; apply lp.ext; funext i; rfl
     map_smul' := by intro a x; apply lp.ext; funext i; rfl } : F E →ₗ[ℝ] F E).mkContinuous 1
    (fun x => by
      change ‖down E m x‖ ≤ 1 * ‖x‖
      simpa only [norm_down_eq_tail, one_mul] using
        L1Tails.norm_tail_le (fun _ : ℕ => E) m x)

theorem opNorm_upCLM_le (m : ℕ) : ‖upCLM E m‖ ≤ 1 :=
  (upCLM E m).opNorm_le_bound zero_le_one
    (fun x => by change ‖up E m x‖ ≤ 1 * ‖x‖; simp only [norm_up, one_mul]; exact le_rfl)

theorem down_up (m : ℕ) :
    (downCLM E m).comp (upCLM E m) = ContinuousLinearMap.id ℝ (F E) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext; funext i
  exact rawUp_add E m x i

theorem up_down (m : ℕ) :
    (upCLM E m).comp (downCLM E m) = L1Tails.tail (fun _ : ℕ => E) m := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext; funext i
  change (if i < m then 0 else x (i - m + m)) = _
  rw [L1Tails.tail_apply]
  split_ifs with hi
  · rfl
  · rw [Nat.sub_add_cancel (Nat.le_of_not_gt hi)]

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem norm_down_comp (m : ℕ) (K : D →L[ℝ] F E) :
    ‖(downCLM E m).comp K‖ = ‖(L1Tails.tail (fun _ : ℕ => E) m).comp K‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    change ‖down E m (K x)‖ ≤ _
    rw [norm_down_eq_tail]
    exact ((L1Tails.tail (fun _ : ℕ => E) m).comp K).le_opNorm x
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    change ‖L1Tails.tail (fun _ : ℕ => E) m (K x)‖ ≤ _
    rw [← norm_down_eq_tail]
    exact ((downCLM E m).comp K).le_opNorm x

end L1Shifts
end BanachGeometry
