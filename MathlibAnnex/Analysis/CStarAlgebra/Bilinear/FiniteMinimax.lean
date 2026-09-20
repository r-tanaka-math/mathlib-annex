import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Sion

/-!
# A finite minimax selection lemma

This file records the finite-dimensional separation step used in the
noncommutative Grothendieck argument.  A compact convex set of possible
controls is tested by finitely many continuous convex violations.  If every
probability-weighted average of the violations can be made nonpositive, then
one control makes every violation nonpositive simultaneously.

The proof uses Sion's minimax theorem with the standard probability simplex.
It is deliberately independent of C-star algebra structure so that the
analytic sequence estimate and the state-space specialization remain
separate interfaces.
-/

set_option autoImplicit false

open Finset Set

namespace MathlibAnnex.CStarBilinear

universe uE uι

noncomputable section

variable {E : Type uE} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E]
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

/-- The probability-weighted average of a finite family of real functions. -/
def weightedViolation (g : ι → E → ℝ) (x : E) (w : ι → ℝ) : ℝ :=
  ∑ i, w i * g i x

theorem continuous_weightedViolation_left
    (g : ι → E → ℝ) (hg : ∀ i, Continuous (g i)) (w : ι → ℝ) :
    Continuous (fun x ↦ weightedViolation g x w) := by
  unfold weightedViolation
  fun_prop

theorem continuous_weightedViolation_right
    (g : ι → E → ℝ) (x : E) :
    Continuous (fun w : ι → ℝ ↦ weightedViolation g x w) := by
  unfold weightedViolation
  fun_prop

theorem convexOn_weightedViolation_left
    {K : Set E} (hK : Convex ℝ K) (g : ι → E → ℝ)
    (hg : ∀ i, ConvexOn ℝ K (g i))
    (w : ι → ℝ) (hw : w ∈ stdSimplex ℝ ι) :
    ConvexOn ℝ K (fun x ↦ weightedViolation g x w) := by
  refine ⟨hK, ?_⟩
  intro x hx y hy a b ha hb hab
  unfold weightedViolation
  calc
    ∑ i, w i * g i (a • x + b • y) ≤
        ∑ i, w i * (a • g i x + b • g i y) := by
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        ((hg i).2 hx hy ha hb hab) (hw.1 i)
    _ = a • (∑ i, w i * g i x) + b • (∑ i, w i * g i y) := by
      simp only [smul_eq_mul]
      simp_rw [mul_add]
      rw [sum_add_distrib]
      congr 1
      · rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring
      · rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring

theorem concaveOn_weightedViolation_right
    (K : Set E) (g : ι → E → ℝ) (x : E) :
    ConcaveOn ℝ (stdSimplex ℝ ι)
      (fun w : ι → ℝ ↦ weightedViolation g x w) := by
  refine ⟨convex_stdSimplex ℝ ι, ?_⟩
  intro w _ v _ a b _ _ _
  unfold weightedViolation
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  apply le_of_eq
  simp_rw [add_mul]
  rw [sum_add_distrib, mul_sum, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro i _
    ring
  · apply sum_congr rfl
    intro i _
    ring

/-- Finite Sion/Ky-Fan selection.  The hypothesis tests every probability
weighted average; the conclusion supplies one point satisfying all tests.
The conclusion is stronger than choosing a separate point for each test. -/
theorem exists_forall_nonpos_of_weightedViolation
    {K : Set E} (hKne : K.Nonempty) (hKconv : Convex ℝ K)
    (hKcompact : IsCompact K) (hEsmul : ContinuousSMul ℝ E)
    (g : ι → E → ℝ)
    (hgcont : ∀ i, Continuous (g i))
    (hgconv : ∀ i, ConvexOn ℝ K (g i))
    (hweighted : ∀ w ∈ stdSimplex ℝ ι,
      ∃ x ∈ K, weightedViolation g x w ≤ 0) :
    ∃ x ∈ K, ∀ i, g i x ≤ 0 := by
  classical
  letI : ContinuousSMul ℝ E := hEsmul
  let f : E → (ι → ℝ) → ℝ := weightedViolation g
  have hsimplex_ne : (stdSimplex ℝ ι).Nonempty := by
    let i : ι := Classical.choice inferInstance
    exact ⟨Pi.single i 1, single_mem_stdSimplex ℝ i⟩
  obtain ⟨a, ha, b, hb, hsaddle⟩ :=
    Sion.exists_isSaddlePointOn
      (X := K) (Y := stdSimplex ℝ ι) (f := f)
      hKne hKconv hKcompact
      (fun w _ ↦
        (continuous_weightedViolation_left g hgcont w).lowerSemicontinuous
          |>.lowerSemicontinuousOn K)
      (fun w hw ↦
        (convexOn_weightedViolation_left hKconv g hgconv w hw).quasiconvexOn)
      (convex_stdSimplex ℝ ι) hsimplex_ne (isCompact_stdSimplex ℝ ι)
      (fun x _ ↦
        (continuous_weightedViolation_right g x).upperSemicontinuous
          |>.upperSemicontinuousOn (stdSimplex ℝ ι))
      (fun x _ ↦
        (concaveOn_weightedViolation_right K g x).quasiconcaveOn)
  refine ⟨a, ha, fun i ↦ ?_⟩
  let e : ι → ℝ := Pi.single i 1
  have he : e ∈ stdSimplex ℝ ι := single_mem_stdSimplex ℝ i
  obtain ⟨x, hx, hxb⟩ := hweighted b hb
  have hle : f a e ≤ f x b := hsaddle x hx e he
  have hvertex : f a e = g i a := by
    unfold f weightedViolation
    change (∑ j, (Pi.single i (1 : ℝ) : ι → ℝ) j * g j a) = g i a
    rw [Fintype.sum_eq_single i (fun j hji ↦ by
      rw [Pi.single_eq_of_ne hji]
      simp), Pi.single_eq_same, one_mul]
  exact hvertex ▸ hle.trans hxb

end

end MathlibAnnex.CStarBilinear
