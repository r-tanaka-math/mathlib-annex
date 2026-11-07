import BanachGeometry.SequenceSpaces.C0Dual
import BanachGeometry.SequenceSpaces.ApproximateNorming

/-! The exact isometric c₀-dual/ℓ₁-dual identification in R6 §2.
Earlier 2/1 estimates are retained; approximate norming improves them
to equality without assuming norm attainment.
Execution evidence is recorded in the external receipts. -/
noncomputable section
namespace BanachGeometry
namespace C0Dual
variable (V : ℕ → Type*) [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]

theorem mul_sum_norm_coefficient_le_norm (f : Dual V) (s : Finset ℕ)
    (α : ℝ) (hα : α < 1) : α * (∑ j ∈ s, ‖coefficient V f j‖) ≤ ‖f‖ := by
  classical
  choose v hv hfv using fun j => UnitBall.exists_scaled_norm_eval (coefficient V f j) α hα
  let u := fun j => C0Sum.single j (v j)
  have hu (j : ℕ) : ‖u j‖ ≤ 1 := by simpa only [u,C0Sum.norm_single] using hv j
  have hd : C0Sum.CoordinateDisjoint V u := by
    intro j k hjk i
    by_cases hi : i = j
    · subst i; exact Or.inr (C0Sum.single_apply_ne k (v k) hjk)
    · exact Or.inl (C0Sum.single_apply_ne j (v j) hi)
  let w := ∑ j ∈ s, u j
  have hw : ‖w‖ ≤ 1 := by
    simpa only [one_smul] using C0Sum.norm_sum_smul_le_one V u hd hu
      (fun _ => 1) (by intro j; norm_num) s
  have heval : (∑ j ∈ s, coefficient V f j (v j)) = f w := by
    simp only [w,u,map_sum,coefficient,ContinuousLinearMap.comp_apply]
    rfl
  calc
    α * (∑ j ∈ s, ‖coefficient V f j‖) = ∑ j ∈ s, α * ‖coefficient V f j‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ s, coefficient V f j (v j) := Finset.sum_le_sum (fun j hj => hfv j)
    _ = f w := heval
    _ ≤ ‖f w‖ := le_abs_self _
    _ ≤ ‖f‖ * ‖w‖ := f.le_opNorm w
    _ ≤ ‖f‖ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hw (norm_nonneg f)

theorem sum_norm_coefficient_le_norm (f : Dual V) (s : Finset ℕ) :
    (∑ j ∈ s, ‖coefficient V f j‖) ≤ ‖f‖ := by
  by_contra hbad
  let S := ∑ j ∈ s, ‖coefficient V f j‖
  have hS : ‖f‖ < S := lt_of_not_ge hbad
  have hSp : 0 < S := lt_of_le_of_lt (norm_nonneg f) hS
  let α := (‖f‖/S+1)/2
  have hα : α < 1 := by
    have hd : ‖f‖/S < 1 := (div_lt_iff₀ hSp).mpr (by simpa only [one_mul] using hS)
    dsimp [α]; linarith
  have hle := mul_sum_norm_coefficient_le_norm V f s α hα
  have heq : α*S = (‖f‖+S)/2 := by
    dsimp [α]
    field_simp [hSp.ne'] <;> ring
  change α*S ≤ ‖f‖ at hle
  rw [heq] at hle
  linarith

theorem norm_coefficients (f : Dual V) : ‖coefficients V f‖ = ‖f‖ := by
  apply le_antisymm
  · rw [l1_norm_eq_tsum]
    exact Real.tsum_le_of_sum_le (fun j => norm_nonneg _) (sum_norm_coefficient_le_norm V f)
  · simpa only [sumEval_coefficients V] using norm_sumEval_le V (coefficients V f)

def linearIsometryEquiv : Dual V ≃ₗᵢ[ℝ] L1Dual V where
  toLinearEquiv := (equiv V).toLinearEquiv
  norm_map' := norm_coefficients V

end C0Dual
end BanachGeometry
