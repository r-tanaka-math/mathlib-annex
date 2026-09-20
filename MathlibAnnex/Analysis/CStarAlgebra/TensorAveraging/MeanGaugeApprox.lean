import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedStrongApprox
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.VectorDomination

/-!
# Common concrete gauges for finite represented tests

The accepted finite self-adjoint Kadison approximation already supplies one
operator for all requested vectors.  The explicit vector-gauge formula
transports that result to the strong-star budgets used by bilinear
domination.  This does not approximate arbitrary isometries, and therefore
does not prove the all-test row-convex closure.
-/

set_option autoImplicit false
open scoped InnerProduct CStarAlgebra

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]

/-- One self-adjoint contraction in the represented source controls the
strong-star gauges of every requested vector at once. -/
theorem irreducible_selfAdjoint_contract_finite_gauge_approx
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hTnorm : ‖T‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧
      ∀ i : I, MathlibAnnex.CStarBilinear.strongStarGauge
        (operatorVectorState H (ξ i)) (pi a - T) < δ := by
  obtain ⟨a, ha, haNorm, hboth⟩ :=
    irreducible_selfAdjoint_contract_finite_both_apply_approx
      pi hpi ξ T hT hTnorm (ε := δ / 2) (by linarith)
  refine ⟨a, ha, haNorm, fun i => ?_⟩
  have hforward := (hboth i).1
  have hadjoint : ‖(star (pi a - T)) (ξ i)‖ < δ / 2 := by
    simpa only [star_sub] using (hboth i).2
  have hgauge := strongStarGauge_operatorVectorState_le H (ξ i) (pi a - T)
  linarith

/-- The same single represented contraction also approximates every
requested diagonal value of a finite family of matrix-coefficient bilinear
forms.  The vector norms and the strict gauge budget are fixed before the
source element is selected. -/
theorem irreducible_selfAdjoint_contract_finite_matrixCoefficient_approx
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    {I : Type*} [Fintype I] [DecidableEq I]
    (η ξ : I → H) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hTnorm : ‖T‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧
      ∀ i : I,
        ‖(mulForm (H →L[ℂ] H)
            (operatorMatrixCoefficient H (η i) (ξ i))) (pi a) (pi a) -
          (mulForm (H →L[ℂ] H)
            (operatorMatrixCoefficient H (η i) (ξ i))) T T‖ < ε := by
  classical
  let M : ℝ := ∑ i : I, (‖η i‖ + ‖ξ i‖)
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ =>
    add_nonneg (norm_nonneg (η i)) (norm_nonneg (ξ i))
  have hηM (i : I) : ‖η i‖ ≤ M := by
    calc
      ‖η i‖ ≤ ‖η i‖ + ‖ξ i‖ := le_add_of_nonneg_right (norm_nonneg _)
      _ ≤ M := Finset.single_le_sum
        (fun j _ => add_nonneg (norm_nonneg (η j)) (norm_nonneg (ξ j)))
        (Finset.mem_univ i)
  have hξM (i : I) : ‖ξ i‖ ≤ M := by
    calc
      ‖ξ i‖ ≤ ‖η i‖ + ‖ξ i‖ := le_add_of_nonneg_left (norm_nonneg _)
      _ ≤ M := Finset.single_le_sum
        (fun j _ => add_nonneg (norm_nonneg (η j)) (norm_nonneg (ξ j)))
        (Finset.mem_univ i)
  let δ : ℝ := ε / (4 * (M + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let ζ : Sum I I → H := Sum.elim η ξ
  obtain ⟨a, ha, haNorm, hg⟩ :=
    irreducible_selfAdjoint_contract_finite_gauge_approx
      pi hpi ζ T hT hTnorm hδ
  have hgη (i : I) :
      MathlibAnnex.CStarBilinear.strongStarGauge
        (operatorVectorState H (η i)) (pi a - T) < δ := by
    simpa [ζ] using hg (Sum.inl i)
  have hgξ (i : I) :
      MathlibAnnex.CStarBilinear.strongStarGauge
        (operatorVectorState H (ξ i)) (pi a - T) < δ := by
    simpa [ζ] using hg (Sum.inr i)
  have hpiNorm : ‖pi a‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le pi.toNonUnitalStarAlgHom a).trans haNorm
  have hBound (v : H) (S : H →L[ℂ] H)
      (hS : ‖S‖ ≤ 1) (hv : ‖v‖ ≤ M) :
      MathlibAnnex.CStarBilinear.strongStarGauge
        (operatorVectorState H v) S ≤ 2 * M := by
    have hp : ‖S‖ * ‖v‖ ≤ M := by
      calc
        ‖S‖ * ‖v‖ ≤ 1 * ‖v‖ :=
          mul_le_mul_of_nonneg_right hS (norm_nonneg v)
        _ = ‖v‖ := one_mul _
        _ ≤ M := hv
    have h := strongStarGauge_operatorVectorState_le_two_mul_norm H v S
    nlinarith
  have hBudget : 2 * (1 : ℝ) * δ * (2 * M) < ε := by
    have hden : 0 < 4 * (M + 1) := by positivity
    have hEq : 4 * δ * (M + 1) = ε := by
      dsimp [δ]
      field_simp
    have hlt : 4 * δ * M < 4 * δ * (M + 1) := by
      apply mul_lt_mul_of_pos_left (by linarith : M < M + 1)
      positivity
    nlinarith
  refine ⟨a, ha, haNorm, ?_⟩
  exact finite_matrixCoefficient_strongStar_sub_lt H η ξ
    (δ := δ) (M := 2 * M) (ε := ε)
    hδ.le (by positivity) (by simpa only [mul_one] using hBudget)
    (X := pi a) (X' := T) (Y := pi a) (Y' := T)
    hgη (fun i => hBound (η i) T hTnorm (hηM i))
    hgξ (fun i => hBound (ξ i) (pi a) hpiNorm (hξM i))

end MathlibAnnex.CStarAlgebra.TensorAveraging
