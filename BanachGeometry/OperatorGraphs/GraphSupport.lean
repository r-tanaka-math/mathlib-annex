import BanachGeometry.OperatorGraphs.GraphAdmissible

/-! Norm tests, finite coordinate inclusions and nontriviality of the exact
weighted graph. The arbitrary maps Q need no uniform operator-norm bound. -/

noncomputable section
namespace BanachGeometry
namespace WeightedGraph
variable (A B : ℕ → Type)
    [∀ j, NormedAddCommGroup (A j)] [∀ j, NormedSpace ℝ (A j)]
    [∀ j, NormedAddCommGroup (B j)] [∀ j, NormedSpace ℝ (B j)]
    (Q : ∀ j, A j →L[ℝ] B j) («λ» : ℕ → ℝ)

theorem sum_weighted_le_norm («hλ» : ∀ j, 0 < «λ» j) (x : Space A B Q «λ») :
    (∑' j, «λ» j * ‖coord A B Q «λ» j x‖) ≤ ‖x‖ := by
  have heq : (∑' j, «λ» j * ‖coord A B Q «λ» j x‖) = ‖x.1.1‖ := by
    rw [l1_norm_eq_tsum]
    exact tsum_congr (fun j => weight_coord_norm A B Q «λ» «hλ» j x)
  rw [heq]
  exact norm_fst_le x.1

theorem norm_image_coord_le («hλ» : ∀ j, 0 < «λ» j) (j : ℕ) (x : Space A B Q «λ») :
    ‖Q j (coord A B Q «λ» j x)‖ ≤ ‖x‖ := by
  rw [coord_output A B Q «λ» «hλ» j x]
  exact (x.1.2.norm_apply_le j).trans (norm_snd_le x.1)

theorem norm_le_of_sum_le_of_images_le («hλ» : ∀ j, 0 < «λ» j) (x : Space A B Q «λ»)
    (C : ℝ) (hs : (∑' j, «λ» j * ‖coord A B Q «λ» j x‖) ≤ C)
    (hi : ∀ j, ‖Q j (coord A B Q «λ» j x)‖ ≤ C) : ‖x‖ ≤ C := by
  rw [norm_formula A B Q «λ» «hλ» x]
  exact max_le hs (ciSup_le hi)

def single (j : ℕ) (a : A j) : Space A B Q «λ» :=
  ⟨(lp.single 1 j («λ» j • a), C0Sum.single j (Q j a)), by
    intro i
    by_cases hi : i = j
    · subst i
      simp only [lp.single_apply_self, C0Sum.single_apply_self, map_smul]
    · rw [lp.single_apply_ne 1 j («λ» j • a) hi, C0Sum.single_apply_ne j (Q j a) hi,
        map_zero, smul_zero]⟩

theorem coord_single («hλ» : ∀ j, 0 < «λ» j) (j : ℕ) (a : A j) :
    coord A B Q «λ» j (single A B Q «λ» j a) = a := by
  change («λ» j)⁻¹ • lp.single 1 j («λ» j • a) j = a
  rw [lp.single_apply_self, smul_smul, inv_mul_cancel₀ («hλ» j).ne', one_smul]

theorem graph_nontrivial («hλ» : ∀ j, 0 < «λ» j) [Nontrivial (A 0)] : Nontrivial (Space A B Q «λ») := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne (A 0)
  refine ⟨⟨single A B Q «λ» 0 a, single A B Q «λ» 0 b, ?_⟩⟩
  intro h
  apply hab
  have heq := congrArg (coord A B Q «λ» 0) h
  simpa only [coord_single A B Q «λ» «hλ»] using heq

end WeightedGraph
end BanachGeometry
