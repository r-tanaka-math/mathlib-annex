import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.SupportMoment
import MathlibAnnex.Analysis.CStarAlgebra.State.VectorApproximation

set_option autoImplicit false
noncomputable section
namespace MathlibAnnex.Analysis.CStarAlgebra

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

def rowMomentTests {n : ℕ} (x : Fin n → A) : Finset A := by
  classical
  exact insert (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x)
    ((Finset.univ.product Finset.univ).image (fun p : Fin n × Fin n => x p.1 * star (x p.2)))

private theorem rowSquare_mem_tests {n : ℕ} (x : Fin n → A) :
    MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x ∈ rowMomentTests x := by
  classical
  simp [rowMomentTests]

private theorem rowMoment_mem_tests {n : ℕ} (x : Fin n → A) (i j : Fin n) :
    x i * star (x j) ∈ rowMomentTests x := by
  classical
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  exact ⟨(i, j), by simp, rfl⟩

theorem Representation.exists_same_zeta_row_moments {n : ℕ}
    (pi : Representation A H) (hpi : pi.HasNoNonzeroCompactImage)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi)
    (hker : ∀ a : A, pi a = 0 → phi a = 0)
    (x : Fin n → A) (xi eta : H)
    {μ : ℝ} (hμ : 0 < μ) :
    ∃ z : H, ‖z‖ = 1 ∧
      (∀ i j : Fin n,
        inner ℂ (pi (star (x i)) z) (pi (star (x j)) xi) = 0) ∧
      (∀ i j : Fin n,
        inner ℂ (pi (star (x i)) z) (pi (star (x j)) eta) = 0) ∧
      (∀ i j : Fin n,
        ‖phi (x i * star (x j)) - inner ℂ z (pi (x i * star (x j)) z)‖ < μ) ∧
      ‖phi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) -
        inner ℂ z (pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) z)‖ < μ := by
  obtain ⟨z, hz, hxi, heta, happrox⟩ :=
    pi.exists_unit_approx_and_transformed_orthogonal hpi phi hphi hpure hker
      x xi eta (rowMomentTests x) hμ
  refine ⟨z, hz, hxi, heta, ?_, ?_⟩
  · intro i j
    exact happrox _ (rowMoment_mem_tests x i j)
  · exact happrox _ (rowSquare_mem_tests x)

end MathlibAnnex.Analysis.CStarAlgebra
