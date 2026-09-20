import MathlibAnnex.Analysis.CStarAlgebra.Representation.FullImage
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteRow

/-!
# A concrete finite row in a finite-dimensional full representation

Matrix units give a normalized row whose completely positive row map is
central on every element. The result requires a faithful, surjective
representation on a finite-dimensional Hilbert space. It does not give the
Haagerup mean for arbitrary C-star algebras.
-/

set_option autoImplicit false
noncomputable section

open InnerProductSpace
open Module

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem rankOne_double_sandwich (x y : H) (T : H →L[ℂ] H) :
    rankOne ℂ x y * T * rankOne ℂ y x =
      inner ℂ y (T y) • rankOne ℂ x x := by
  ext v
  simp [ContinuousLinearMap.mul_apply, rankOne_apply, smul_smul,
    inner_smul_right, mul_comm, mul_left_comm, mul_assoc]

private theorem depolarizing_identity {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (T : H →L[ℂ] H) :
    (∑ i : ι, ∑ j : ι,
      rankOne ℂ (b i) (b j) * T * rankOne ℂ (b j) (b i)) =
      (∑ j : ι, inner ℂ (b j) (T (b j))) • (1 : H →L[ℂ] H) := by
  simp_rw [rankOne_double_sandwich]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum]
  rw [b.sum_rankOne_eq_id]
  rw [← Finset.sum_smul]
  rfl

private theorem matrix_row_square {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) :
    (∑ i : ι, ∑ j : ι,
      rankOne ℂ (b i) (b j) * rankOne ℂ (b j) (b i)) =
      (Fintype.card ι : ℂ) • (1 : H →L[ℂ] H) := by
  simpa using depolarizing_identity b (1 : H →L[ℂ] H)

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra.TensorAveraging

private theorem rowSquare_real_smul
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {n : ℕ} (r : ℝ) (y : Fin n → A) :
    rowSquare A (fun i => (r : ℂ) • y i) =
      (r ^ 2 : ℂ) • rowSquare A y := by
  simp [rowSquare, Finset.smul_sum, star_smul, pow_two,
    smul_mul_assoc, mul_smul_comm, mul_smul]

private theorem rowMap_real_smul
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {n : ℕ} (r : ℝ) (y : Fin n → A) (z : A) :
    rowMap A (fun i => (r : ℂ) • y i) z =
      (r ^ 2 : ℂ) • rowMap A y z := by
  simp [rowMap_apply, Finset.smul_sum, star_smul, pow_two,
    smul_mul_assoc, mul_smul_comm, mul_smul]

private theorem exists_unscaled_matrix_row
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ H] [Nontrivial H]
    (pi : Representation A H) (hsurj : Function.Surjective pi) :
    ∃ (n : ℕ) (y : Fin n → A),
      pi (rowSquare A y) =
        (finrank ℂ H : ℂ) • (1 : H →L[ℂ] H) ∧
      ∀ z : A, pi (rowMap A y z) =
        (∑ j : Fin (finrank ℂ H), inner ℂ
          ((stdOrthonormalBasis ℂ H) j) (pi z ((stdOrthonormalBasis ℂ H) j))) •
          (1 : H →L[ℂ] H) := by
  let b := stdOrthonormalBasis ℂ H
  let I := Fin (finrank ℂ H) × Fin (finrank ℂ H)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let c : I → A := fun ij => Classical.choose
    (hsurj (rankOne ℂ (b ij.1) (b ij.2)))
  have hc (ij : I) : pi (c ij) = rankOne ℂ (b ij.1) (b ij.2) :=
    Classical.choose_spec (hsurj (rankOne ℂ (b ij.1) (b ij.2)))
  let y : Fin (Fintype.card I) → A := fun k => c (e k)
  refine ⟨Fintype.card I, y, ?_, ?_⟩
  · simp only [rowSquare, map_sum, map_mul, map_star]
    simp_rw [show ∀ k, pi (y k) = rankOne ℂ (b (e k).1) (b (e k).2) from
      fun k => hc (e k)]
    simp_rw [show ∀ k, star (rankOne ℂ (b (e k).1) (b (e k).2)) =
      rankOne ℂ (b (e k).2) (b (e k).1) from fun k => by
        rw [ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]]
    calc
      (∑ k, rankOne ℂ (b (e k).1) (b (e k).2) *
        rankOne ℂ (b (e k).2) (b (e k).1)) =
          ∑ ij : I, rankOne ℂ (b ij.1) (b ij.2) *
            rankOne ℂ (b ij.2) (b ij.1) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = (finrank ℂ H : ℂ) • 1 := by
        have hprod : (Finset.univ : Finset I) =
            (Finset.univ : Finset (Fin (finrank ℂ H))).product Finset.univ := by
          ext ij
          simp [I]
        rw [hprod]
        exact (Finset.sum_product'
          (Finset.univ : Finset (Fin (finrank ℂ H))) Finset.univ
          (fun i j => rankOne ℂ (b i) (b j) * rankOne ℂ (b j) (b i))).trans
            (by simpa using matrix_row_square b)
  · intro z
    simp only [rowMap_apply, map_sum, map_mul, map_star]
    simp_rw [show ∀ k, pi (y k) = rankOne ℂ (b (e k).1) (b (e k).2) from
      fun k => hc (e k)]
    simp_rw [show ∀ k, star (rankOne ℂ (b (e k).1) (b (e k).2)) =
      rankOne ℂ (b (e k).2) (b (e k).1) from fun k => by
        rw [ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]]
    calc
      (∑ k, rankOne ℂ (b (e k).1) (b (e k).2) * pi z *
        rankOne ℂ (b (e k).2) (b (e k).1)) =
          ∑ ij : I, rankOne ℂ (b ij.1) (b ij.2) * pi z *
            rankOne ℂ (b ij.2) (b ij.1) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := by
        have hprod : (Finset.univ : Finset I) =
            (Finset.univ : Finset (Fin (finrank ℂ H))).product Finset.univ := by
          ext ij
          simp [I]
        rw [hprod]
        exact (Finset.sum_product'
          (Finset.univ : Finset (Fin (finrank ℂ H))) Finset.univ
          (fun i j => rankOne ℂ (b i) (b j) * pi z *
            rankOne ℂ (b j) (b i))).trans
              (by simpa [b] using depolarizing_identity b (pi z))

/-- An actual normalized, exactly central finite row from the full finite
matrix image. This is the finite-dimensional compact-image supplier. -/
theorem exists_normalized_central_matrix_row
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [FiniteDimensional ℂ H] [Nontrivial H]
    (pi : Representation A H) (hinj : Function.Injective pi)
    (hsurj : Function.Surjective pi) :
    ∃ (n : ℕ) (x : Fin n → A),
      rowSquare A x = 1 ∧
      ∀ a z : A, a * rowMap A x z = rowMap A x z * a := by
  obtain ⟨n, y, hqY, hmapY⟩ := exists_unscaled_matrix_row pi hsurj
  let d : ℝ := finrank ℂ H
  have hd : 0 < d := by
    have hdN : 0 < finrank ℂ H := finrank_pos_iff.mpr inferInstance
    dsimp [d]
    exact_mod_cast hdN
  let r : ℝ := 1 / Real.sqrt d
  have hsq : r ^ 2 * d = 1 := by
    dsimp [r]
    rw [div_pow, one_pow, Real.sq_sqrt hd.le]
    field_simp [ne_of_gt hd]
  have hcoeff : (r ^ 2 : ℂ) * (finrank ℂ H : ℂ) = 1 := by
    exact_mod_cast hsq
  let x : Fin n → A := fun i => (r : ℂ) • y i
  refine ⟨n, x, ?_, ?_⟩
  · apply hinj
    change pi (rowSquare A x) = pi (1 : A)
    rw [show rowSquare A x = (r ^ 2 : ℂ) • rowSquare A y from
      rowSquare_real_smul r y, map_smul, hqY, map_one]
    simp [smul_smul, hcoeff]
  · intro a z
    apply hinj
    simp only [map_mul]
    have hxmap : ∃ c : ℂ, pi (rowMap A x z) = c • (1 : H →L[ℂ] H) := by
      refine ⟨(r ^ 2 : ℂ) *
        (∑ j : Fin (finrank ℂ H), inner ℂ
          ((stdOrthonormalBasis ℂ H) j)
          (pi z ((stdOrthonormalBasis ℂ H) j))), ?_⟩
      rw [show rowMap A x z = (r ^ 2 : ℂ) • rowMap A y z from
        rowMap_real_smul r y z, map_smul, hmapY]
      rw [smul_smul]
    rcases hxmap with ⟨c, hc⟩
    rw [hc]
    simp

end MathlibAnnex.CStarAlgebra.TensorAveraging
