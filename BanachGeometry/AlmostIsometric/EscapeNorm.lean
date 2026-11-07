import BanachGeometry.AlmostIsometric.Escape

/-! The exact heterogeneous two-coordinate norm formula displayed in
R6 Remark 5.4. Complements its already proved separation/subsequence and
Mazur–Ulam observations.
Execution evidence is recorded in the external receipts. -/
noncomputable section
namespace BanachGeometry
namespace C0Sum
variable (V : ℕ → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]

theorem norm_single_sub_single (i j : ℕ) (hij : i ≠ j) (a : V i) (b : V j) :
    ‖single i a-single j b‖ = max ‖a‖ ‖b‖ := by
  apply le_antisymm
  · apply C0Sum.norm_le (le_trans (norm_nonneg _) (le_max_left _ _))
    intro k
    rw [sub_apply]
    by_cases hki : k = i
    · subst k
      rw [single_apply_self,single_apply_ne j b hij,sub_zero]
      exact le_max_left _ _
    · by_cases hkj : k = j
      · subst k
        rw [single_apply_ne i a hij.symm,single_apply_self,zero_sub,norm_neg]
        exact le_max_right _ _
      · rw [single_apply_ne i a hki,single_apply_ne j b hkj,sub_self,norm_zero]
        exact le_trans (norm_nonneg _) (le_max_left _ _)
  · apply max_le
    · have h := (single i a-single j b).norm_apply_le i
      simpa only [sub_apply,single_apply_self,single_apply_ne j b hij,sub_zero] using h
    · have h := (single i a-single j b).norm_apply_le j
      simpa only [sub_apply,single_apply_ne i a hij.symm,single_apply_self,zero_sub,norm_neg] using h

end C0Sum
namespace AlmostIsometricFamily

theorem norm_insertion_images_sub (d : AlmostIsometricFamily) (z : d.ZInfty)
    (N M : ℕ) (hNM : N ≠ M) (C C' : ℝ) (hC : 1 ≤ C) (hC' : 1 ≤ C')
    (hN : ∀ i, N ≤ i → d.bound i ≤ C) (hM : ∀ i, M ≤ i → d.bound i ≤ C') :
    ‖(d.nearEquiv N C hC hN).equiv (z,0)-(d.nearEquiv M C' hC' hM).equiv (z,0)‖ =
      max ‖(d.intoRow N C hC hN).equiv z‖ ‖(d.intoRow M C' hC' hM).equiv z‖ := by
  rw [d.nearEquiv_of_extra,d.nearEquiv_of_extra]
  exact C0Sum.norm_single_sub_single (fun k => d.Z k) N M hNM _ _

end AlmostIsometricFamily
end BanachGeometry
