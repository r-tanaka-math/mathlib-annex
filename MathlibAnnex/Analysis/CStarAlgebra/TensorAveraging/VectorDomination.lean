import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.MeanVectorMoment
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Domination
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.Positive
import MathlibAnnex.Analysis.InnerProductSpace.StrongOperator

/-!
# Concrete strong-star control of represented vector-product tests

Unlike the still-missing domination theorem for an arbitrary C-star bilinear
form, a vector-product test has explicit controlling vector functionals.
Both star-square orientations occur in the gauge.  The resulting estimate
uses one common pair of approximants, as required by the mean construction.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped CStarAlgebra InnerProductSpace ComplexOrder

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

open MathlibAnnex.CStarBilinear

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A concrete vector functional is continuous even in the weak operator
topology.  This is an actual represented continuity proof, not an assertion
about every bounded functional on `B(H)`. -/
theorem operatorVectorState_wotContinuous (ξ : H) :
    Continuous (fun X : H →WOT[ℂ] H =>
      operatorVectorState H ξ X.toCLM) := by
  simpa [operatorVectorState] using
    (ContinuousLinearMapWOT.continuous_dual_apply ξ (innerSL ℂ ξ))

theorem operatorMatrixCoefficient_wotContinuous (η ξ : H) :
    Continuous (fun X : H →WOT[ℂ] H =>
      operatorMatrixCoefficient H η ξ X.toCLM) := by
  simpa [operatorMatrixCoefficient] using
    (ContinuousLinearMapWOT.continuous_dual_apply ξ (innerSL ℂ η))

theorem operatorVectorState_nonneg (ξ : H) (X : H →L[ℂ] H)
    (hX : 0 ≤ X) : 0 ≤ operatorVectorState H ξ X := by
  change 0 ≤ inner ℂ ξ (X ξ)
  exact ((ContinuousLinearMap.nonneg_iff_isPositive X).mp hX).inner_nonneg_right ξ

/-- A positive functional on the concrete represented algebra, for any
vector including zero.  Its underlying continuous functional is the one
used by the strong-star gauge and is WOT-continuous above. -/
def operatorVectorPositive (ξ : H) : (H →L[ℂ] H) →ₚ[ℂ] ℂ where
  toLinearMap := (operatorVectorState H ξ).toLinearMap
  monotone' := by
    intro X Y hXY
    apply sub_nonneg.mp
    change 0 ≤ operatorVectorState H ξ Y - operatorVectorState H ξ X
    rw [← map_sub]
    have hDiff : 0 ≤ Y - X :=
      (ContinuousLinearMap.nonneg_iff_isPositive (Y - X)).mpr
        ((ContinuousLinearMap.le_def X Y).mp hXY)
    exact operatorVectorState_nonneg H ξ (Y - X) hDiff

/-- The represented positive vector functional has exactly the squared
vector norm, including the zero-vector case. -/
theorem norm_operatorVectorState (ξ : H) :
    ‖operatorVectorState H ξ‖ = ‖ξ‖ ^ 2 := by
  classical
  rcases subsingleton_or_nontrivial H with hH | hH
  · letI := hH
    have hξ : ξ = 0 := Subsingleton.elim _ _
    rw [hξ]
    simp [operatorVectorState]
  · letI := hH
    apply le_antisymm
    · refine ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _) fun X => ?_
      change ‖inner ℂ ξ (X ξ)‖ ≤ ‖ξ‖ ^ 2 * ‖X‖
      calc
        ‖inner ℂ ξ (X ξ)‖ ≤ ‖ξ‖ * ‖X ξ‖ := norm_inner_le_norm _ _
        _ ≤ ‖ξ‖ * (‖X‖ * ‖ξ‖) :=
          mul_le_mul_of_nonneg_left (X.le_opNorm ξ) (norm_nonneg ξ)
        _ = ‖ξ‖ ^ 2 * ‖X‖ := by ring
    · have h := (operatorVectorState H ξ).le_opNorm (1 : H →L[ℂ] H)
      rw [operatorVectorState_one H ξ, norm_one, mul_one] at h
      simpa [norm_pow] using h

@[simp]
theorem operatorVectorPositive_apply (ξ : H) (X : H →L[ℂ] H) :
    operatorVectorPositive H ξ X = operatorVectorState H ξ X := rfl

theorem operatorVectorState_star_mul_self (ξ : H) (X : H →L[ℂ] H) :
    operatorVectorState H ξ (star X * X) = (‖X ξ‖ ^ 2 : ℂ) := by
  change inner ℂ ξ ((star X * X) ξ) = _
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq_to_K (X ξ)

theorem operatorVectorState_mul_star_self (ξ : H) (X : H →L[ℂ] H) :
    operatorVectorState H ξ (X * star X) = (‖(star X) ξ‖ ^ 2 : ℂ) := by
  simpa only [star_star] using operatorVectorState_star_mul_self H ξ (star X)

/-- On the represented algebra the abstract two-sided gauge is precisely the
Euclidean norm of the operator and adjoint applied to the same vector. -/
theorem strongStarGauge_operatorVectorState (ξ : H) (X : H →L[ℂ] H) :
    strongStarGauge (operatorVectorState H ξ) X =
      Real.sqrt (‖X ξ‖ ^ 2 + ‖(star X) ξ‖ ^ 2) := by
  simp [strongStarGauge, operatorVectorState_star_mul_self,
    operatorVectorState_mul_star_self, norm_pow]

theorem strongStarGauge_operatorVectorState_le (ξ : H) (X : H →L[ℂ] H) :
    strongStarGauge (operatorVectorState H ξ) X ≤
      ‖X ξ‖ + ‖(star X) ξ‖ := by
  rw [strongStarGauge_operatorVectorState]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [mul_nonneg (norm_nonneg (X ξ)) (norm_nonneg ((star X) ξ))]

/-- A uniform operator-norm bound supplies the bounded-set budget for every
represented vector gauge. -/
theorem strongStarGauge_operatorVectorState_le_two_mul_norm
    (ξ : H) (X : H →L[ℂ] H) :
    strongStarGauge (operatorVectorState H ξ) X ≤ 2 * ‖X‖ * ‖ξ‖ := by
  calc
    strongStarGauge (operatorVectorState H ξ) X ≤
        ‖X ξ‖ + ‖(star X) ξ‖ :=
      strongStarGauge_operatorVectorState_le H ξ X
    _ ≤ ‖X‖ * ‖ξ‖ + ‖star X‖ * ‖ξ‖ :=
      add_le_add (X.le_opNorm ξ) ((star X).le_opNorm ξ)
    _ = 2 * ‖X‖ * ‖ξ‖ := by rw [norm_star]; ring

/-- Genuine represented strong-star convergence makes each concrete vector
gauge tend to zero.  Both the operator and its adjoint are required. -/
theorem tendsto_strongStarGauge_zero
    {ι : Type*} {l : Filter ι} (X : ι → H →L[ℂ] H)
    (T : H →L[ℂ] H)
    (hX : ContinuousLinearMap.StronglyConverges X l T)
    (hStar : ContinuousLinearMap.StronglyConverges
      (fun i => star (X i)) l (star T)) (ξ : H) :
    Tendsto (fun i => strongStarGauge (operatorVectorState H ξ) (X i - T))
      l (𝓝 0) := by
  have h₁ : Tendsto (fun i => (X i - T) ξ) l (𝓝 (0 : H)) := by
    simpa [ContinuousLinearMap.sub_apply] using (hX ξ).sub_const (T ξ)
  have h₂ : Tendsto (fun i => (star (X i - T)) ξ) l (𝓝 (0 : H)) := by
    simpa [star_sub, ContinuousLinearMap.sub_apply] using
      (hStar ξ).sub_const ((star T) ξ)
  have hn₁ : Tendsto (fun i => ‖(X i - T) ξ‖) l (𝓝 (0 : ℝ)) := by
    simpa using h₁.norm
  have hn₂ : Tendsto (fun i => ‖(star (X i - T)) ξ‖) l (𝓝 (0 : ℝ)) := by
    simpa using h₂.norm
  have hs := (hn₁.pow 2).add (hn₂.pow 2)
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa [strongStarGauge_operatorVectorState, Function.comp_def] using hr

/-- A finite collection of vector gauges admits one common late strong-star
approximant.  This is a topology-to-budget lemma; it does not manufacture
the strongly-star convergent operator family itself. -/
theorem eventually_all_strongStarGauge_lt
    {ι J : Type*} [Fintype J] {l : Filter ι}
    (X : ι → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hX : ContinuousLinearMap.StronglyConverges X l T)
    (hStar : ContinuousLinearMap.StronglyConverges
      (fun i => star (X i)) l (star T))
    (ξ : J → H) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ i in l, ∀ j, strongStarGauge
      (operatorVectorState H (ξ j)) (X i - T) < δ := by
  classical
  exact Filter.eventually_all.mpr fun j =>
    (tendsto_strongStarGauge_zero H X T hX hStar (ξ j)).eventually
      (eventually_lt_nhds hδ)

theorem norm_apply_le_strongStarGauge (ξ : H) (X : H →L[ℂ] H) :
    ‖X ξ‖ ≤ strongStarGauge (operatorVectorState H ξ) X := by
  apply Real.le_sqrt_of_sq_le
  change ‖X ξ‖ ^ 2 ≤
    ‖operatorVectorState H ξ (star X * X)‖ +
      ‖operatorVectorState H ξ (X * star X)‖
  have h : ‖operatorVectorState H ξ (star X * X)‖ = ‖X ξ‖ ^ 2 := by
    rw [operatorVectorState_star_mul_self]
    simp [norm_pow]
  rw [h]
  exact le_add_of_nonneg_right (norm_nonneg _)

theorem norm_star_apply_le_strongStarGauge (ξ : H) (X : H →L[ℂ] H) :
    ‖(star X) ξ‖ ≤ strongStarGauge (operatorVectorState H ξ) X := by
  apply Real.le_sqrt_of_sq_le
  change ‖(star X) ξ‖ ^ 2 ≤
    ‖operatorVectorState H ξ (star X * X)‖ +
      ‖operatorVectorState H ξ (X * star X)‖
  have h : ‖operatorVectorState H ξ (X * star X)‖ = ‖(star X) ξ‖ ^ 2 := by
    rw [operatorVectorState_mul_star_self]
    simp [norm_pow]
  rw [h]
  exact le_add_of_nonneg_left (norm_nonneg _)

/-- The represented multiplication coefficient is genuinely dominated by
positive vector-square gauges, with constant one. -/
theorem mulForm_matrixCoefficient_dominated (η ξ : H) :
    IsStrongStarDominated
      (mulForm (H →L[ℂ] H) (operatorMatrixCoefficient H η ξ))
      (operatorVectorState H η) (operatorVectorState H ξ) 1 := by
  intro X Y
  have heval :
      (mulForm (H →L[ℂ] H) (operatorMatrixCoefficient H η ξ)) X Y =
        inner ℂ ((star X) η) (Y ξ) := by
    change inner ℂ η ((X * Y) ξ) = _
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  rw [heval, one_mul]
  calc
    ‖inner ℂ ((star X) η) (Y ξ)‖ ≤ ‖(star X) η‖ * ‖Y ξ‖ :=
      norm_inner_le_norm _ _
    _ ≤ strongStarGauge (operatorVectorState H η) X *
        strongStarGauge (operatorVectorState H ξ) Y := by
      exact mul_le_mul
        (norm_star_apply_le_strongStarGauge H η X)
        (norm_apply_le_strongStarGauge H ξ Y)
        (norm_nonneg _) (strongStarGauge_nonneg _ _)

/-- The received telescoping estimate applies to the concrete represented
vector-product test with no hidden positivity or domination assumption. -/
theorem matrixCoefficient_strongStar_sub_le (η ξ : H)
    (X X' Y Y' : H →L[ℂ] H) :
    ‖(mulForm (H →L[ℂ] H) (operatorMatrixCoefficient H η ξ)) X Y -
      (mulForm (H →L[ℂ] H) (operatorMatrixCoefficient H η ξ)) X' Y'‖ ≤
      strongStarGauge (operatorVectorState H η) (X - X') *
        strongStarGauge (operatorVectorState H ξ) Y +
      strongStarGauge (operatorVectorState H η) X' *
        strongStarGauge (operatorVectorState H ξ) (Y - Y') := by
  simpa only [one_mul] using
    norm_sub_le_of_strongStarDominated
      (mulForm_matrixCoefficient_dominated H η ξ) X X' Y Y'

/-- One common pair of bounded strong-star approximants works for a finite
family of represented matrix coefficients.  The requested vectors and error
budget are fixed before either approximant is chosen. -/
theorem finite_matrixCoefficient_strongStar_sub_lt
    {ι : Type*} [Fintype ι] (η ξ : ι → H)
    {δ M ε : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hε : 2 * δ * M < ε)
    {X X' Y Y' : H →L[ℂ] H}
    (hX : ∀ i, strongStarGauge (operatorVectorState H (η i)) (X - X') < δ)
    (hX' : ∀ i, strongStarGauge (operatorVectorState H (η i)) X' ≤ M)
    (hY : ∀ i, strongStarGauge (operatorVectorState H (ξ i)) (Y - Y') < δ)
    (hY' : ∀ i, strongStarGauge (operatorVectorState H (ξ i)) Y ≤ M) :
    ∀ i, ‖(mulForm (H →L[ℂ] H)
                  (operatorMatrixCoefficient H (η i) (ξ i))) X Y -
            (mulForm (H →L[ℂ] H)
                  (operatorMatrixCoefficient H (η i) (ξ i))) X' Y'‖ < ε := by
  exact finite_norm_sub_lt_of_uniform_strongStar
    (fun i => mulForm (H →L[ℂ] H) (operatorMatrixCoefficient H (η i) (ξ i)))
    (fun i => operatorVectorState H (η i))
    (fun i => operatorVectorState H (ξ i))
    (C := 1) (δ := δ) (M := M) (ε := ε)
    (fun i => mulForm_matrixCoefficient_dominated H (η i) (ξ i))
    (by norm_num) hδ hM (by simpa only [mul_one] using hε)
    hX hX' hY hY'

end MathlibAnnex.CStarAlgebra.TensorAveraging
