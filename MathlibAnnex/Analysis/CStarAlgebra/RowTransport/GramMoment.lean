import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.GramMomentSupplier

set_option autoImplicit false
namespace MathlibAnnex.Analysis.CStarAlgebra

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem row_gram_eq_vector_moment
    (pi : Representation A H) {n : ℕ} (x : Fin n → A)
    (v : H) (i j : Fin n) :
    inner ℂ (pi (star (x i)) v) (pi (star (x j)) v) =
      inner ℂ v (pi (x i * star (x j)) v) := by
  rw [Representation.inner_map_star_family, Representation.vectorFunctional_apply]

theorem row_gram_base_z_lt
    (pi : Representation A H) (phi : A →L[ℂ] ℂ)
    {n : ℕ} (x : Fin n → A) (xi z : H) {μ : ℝ}
    (hbase : ∀ i j : Fin n,
      phi (x i * star (x j)) = inner ℂ xi (pi (x i * star (x j)) xi))
    (hz : ∀ i j : Fin n,
      ‖phi (x i * star (x j)) - inner ℂ z (pi (x i * star (x j)) z)‖ < μ)
    (i j : Fin n) :
    ‖inner ℂ (pi (star (x i)) xi) (pi (star (x j)) xi) -
      inner ℂ (pi (star (x i)) z) (pi (star (x j)) z)‖ < μ := by
  rw [row_gram_eq_vector_moment pi x xi i j,
    row_gram_eq_vector_moment pi x z i j, ← hbase i j]
  exact hz i j

theorem row_gram_z_eta_lt
    (pi : Representation A H) (phi : A →L[ℂ] ℂ)
    {n : ℕ} (x : Fin n → A) (z eta : H) {μ : ℝ}
    (hz : ∀ i j : Fin n,
      ‖phi (x i * star (x j)) - inner ℂ z (pi (x i * star (x j)) z)‖ < μ)
    (heta : ∀ i j : Fin n,
      ‖phi (x i * star (x j)) - inner ℂ eta (pi (x i * star (x j)) eta)‖ < μ)
    (i j : Fin n) :
    ‖inner ℂ (pi (star (x i)) z) (pi (star (x j)) z) -
      inner ℂ (pi (star (x i)) eta) (pi (star (x j)) eta)‖ < 2 * μ := by
  rw [row_gram_eq_vector_moment pi x z i j,
    row_gram_eq_vector_moment pi x eta i j]
  have htri : ‖inner ℂ z (pi (x i * star (x j)) z) -
      inner ℂ eta (pi (x i * star (x j)) eta)‖ ≤
      ‖inner ℂ z (pi (x i * star (x j)) z) - phi (x i * star (x j))‖ +
        ‖phi (x i * star (x j)) - inner ℂ eta (pi (x i * star (x j)) eta)‖ := by
    calc
      _ = ‖(inner ℂ z (pi (x i * star (x j)) z) - phi (x i * star (x j))) +
          (phi (x i * star (x j)) - inner ℂ eta (pi (x i * star (x j)) eta))‖ := by
        congr 1
        abel
      _ ≤ _ := norm_add_le _ _
  nlinarith [hz i j, heta i j, norm_sub_rev (phi (x i * star (x j)))
    (inner ℂ z (pi (x i * star (x j)) z))]

end MathlibAnnex.Analysis.CStarAlgebra
