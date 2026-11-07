import BanachGeometry.OperatorGraphs.WeightedGraph

open scoped ENNReal

/-! The closed scaled graph is exactly the sequence space in R6 (6.1).
Admissibility below contains both weighted summability and norm-null images.
No boundedness assumption is silently substituted for the second condition.
Local execution status is recorded in the external qualification receipts. -/

noncomputable section
open Filter
namespace BanachGeometry

namespace C0Sum
variable (B : ℕ → Type*) [∀ j, NormedAddCommGroup (B j)] [∀ j, NormedSpace ℝ (B j)]

/-- A norm-null sequence is bounded; the proof gives an explicit finite-head
bound and thereby supplies the actual `lp ∞` membership certificate. -/
theorem exists_bound_of_null (b : ∀ j, B j)
    (hb : Tendsto (fun j => ‖b j‖) atTop (nhds 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, ‖b j‖ ≤ C := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hb.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))
  let C : ℝ := 1 + ∑ i ∈ Finset.range N, ‖b i‖
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, ‖b i‖ :=
    Finset.sum_nonneg (fun i hi => norm_nonneg (b i))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro j
  by_cases hj : j < N
  · have hle : ‖b j‖ ≤ ∑ i ∈ Finset.range N, ‖b i‖ :=
      Finset.single_le_sum (fun i hi => norm_nonneg (b i)) (Finset.mem_range.mpr hj)
    dsimp [C]
    linarith
  · have hle := (hN j (Nat.le_of_not_gt hj)).le
    dsimp [C]
    linarith

def ofNull (b : ∀ j, B j) (hb : Tendsto (fun j => ‖b j‖) atTop (nhds 0)) : C0Sum B :=
  let hC := exists_bound_of_null B b hb
  ofBound b (by simpa only [Nat.cofinite_eq_atTop] using hb)
    (Classical.choose hC) (Classical.choose_spec hC).2

@[simp] theorem ofNull_apply (b : ∀ j, B j)
    (hb : Tendsto (fun j => ‖b j‖) atTop (nhds 0)) (j : ℕ) : ofNull B b hb j = b j := rfl

end C0Sum

namespace WeightedGraph
variable (A B : ℕ → Type)
    [∀ j, NormedAddCommGroup (A j)] [∀ j, NormedSpace ℝ (A j)]
    [∀ j, NormedAddCommGroup (B j)] [∀ j, NormedSpace ℝ (B j)]
    (Q : ∀ j, A j →L[ℝ] B j) («λ» : ℕ → ℝ)

def Admissible (a : ∀ j, A j) : Prop :=
  Summable (fun j => «λ» j * ‖a j‖) ∧
    Tendsto (fun j => ‖Q j (a j)‖) atTop (nhds 0)

def ofCoordinates («hλ» : ∀ j, 0 < «λ» j) (a : ∀ j, A j)
    (ha : Admissible A B Q «λ» a) : Space A B Q «λ» := by
  have hscaled (j : ℕ) : ‖«λ» j • a j‖ = «λ» j * ‖a j‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos («hλ» j)]
  let x : L1Sum A := ⟨fun j => «λ» j • a j, by
    apply (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).2
    simpa only [ENNReal.toReal_one, Real.rpow_one, hscaled] using ha.1⟩
  let b : C0Sum B := C0Sum.ofNull B (fun j => Q j (a j)) ha.2
  refine ⟨(x, b), ?_⟩
  intro j
  change Q j («λ» j • a j) = «λ» j • Q j (a j)
  exact (Q j).map_smul _ _

@[simp] theorem coord_ofCoordinates («hλ» : ∀ j, 0 < «λ» j)
    (a : ∀ j, A j) (ha : Admissible A B Q «λ» a) (j : ℕ) :
    coord A B Q «λ» j (ofCoordinates A B Q «λ» «hλ» a ha) = a j := by
  change («λ» j)⁻¹ • («λ» j • a j) = a j
  rw [smul_smul, inv_mul_cancel₀ («hλ» j).ne', one_smul]

theorem coordinates_admissible («hλ» : ∀ j, 0 < «λ» j) (x : Space A B Q «λ») :
    Admissible A B Q «λ» (fun j => coord A B Q «λ» j x) := by
  constructor
  · have hx := l1_summable x.1.1
    simpa only [← weight_coord_norm A B Q «λ» «hλ»] using hx
  · exact coordinate_images_null A B Q «λ» «hλ» x

/-- Set-level comparison with the original sequence definition. The inherited
Banach norm remains the one on the closed scaled graph. -/
def admissibleEquiv («hλ» : ∀ j, 0 < «λ» j) :
    Space A B Q «λ» ≃ {a : ∀ j, A j // Admissible A B Q «λ» a} where
  toFun x := ⟨fun j => coord A B Q «λ» j x, coordinates_admissible A B Q «λ» «hλ» x⟩
  invFun a := ofCoordinates A B Q «λ» «hλ» a.1 a.2
  left_inv x := by
    apply coordinates_injective A B Q «λ» «hλ»
    intro j
    exact coord_ofCoordinates A B Q «λ» «hλ» _ _ j
  right_inv a := by
    apply Subtype.ext
    funext j
    exact coord_ofCoordinates A B Q «λ» «hλ» _ _ j

theorem norm_ofCoordinates («hλ» : ∀ j, 0 < «λ» j) (a : ∀ j, A j)
    (ha : Admissible A B Q «λ» a) :
    ‖ofCoordinates A B Q «λ» «hλ» a ha‖ =
      max (∑' j, «λ» j * ‖a j‖) (⨆ j, ‖Q j (a j)‖) := by
  simpa only [coord_ofCoordinates] using norm_formula A B Q «λ» «hλ»
    (ofCoordinates A B Q «λ» «hλ» a ha)

end WeightedGraph
end BanachGeometry
