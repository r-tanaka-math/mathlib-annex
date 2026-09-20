import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.UniversalNormalTests
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteIsometryAverage
import Mathlib.Analysis.Convex.Topology

/-!
# Finite average points have all row and moment constraints

Every point is built with the SAME E and actual section S. The row-closure
proof uses A RET2 for all source tensor tests. There is no assumption that
an arbitrary source functional descends through a nonfaithful pi.
C04 proof-source candidate; all inherited new sources remain unbuilt.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Topology
open scoped BigOperators InnerProductSpace CStarAlgebra

namespace MathlibAnnex.RepresentedCentralCorner
open MathlibAnnex.CStarBidual MathlibAnnex.RepresentedBidual
open MathlibAnnex.FiniteApproximation MathlibAnnex.CStarAlgebra.TensorAveraging
open MathlibAnnex.ProjectiveTensorProduct MathlibAnnex.ProjectiveTensorProduct.Algebra
universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]
variable (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)

/-- A finite average is a genuine bounded linear point of the tensor bidual. -/
def averageTensorPoint (d : FiniteIsometryAverage (H →L[ℂ] H)) :
    StrongDual ℂ (StrongDual ℂ (Tensor A)) :=
  d.functional.comp (tensorAssignment pi hpi)

@[simp] theorem averageTensorPoint_apply (d : FiniteIsometryAverage (H →L[ℂ] H))
    (f : StrongDual ℂ (Tensor A)) :
    averageTensorPoint pi hpi d f = d.value (tensorAssignment pi hpi f) := rfl

/-- Correct star on the unchanged raw bidual, not a new incompatible instance. -/
theorem rawSection_star (T : H →L[ℂ] H) :
    rawSection pi hpi (star T) = bidualStar (rawSection pi hpi T) := by
  rw [rawSection_apply, section_star]
  rfl

/-- Each individual isometry sample is the previously constructed diagonal
bidual point. Thus the same source net serves every subsequent tensor test. -/
theorem sample_tensorAssignment_eq_diagonal
    (s : Isometry (H →L[ℂ] H)) (f : StrongDual ℂ (Tensor A)) :
    tensorAssignment pi hpi f (star s.val) s.val =
      diagonalTensorPoint (rawSection pi hpi s.val) f := by
  rw [tensorAssignment_apply, representedForm_apply, rawSection_star,
    diagonalTensorPoint_apply]

/-- This is a real convex combination, though its evaluations are complex. -/
theorem averageTensorPoint_eq_sum (d : FiniteIsometryAverage (H →L[ℂ] H)) :
    averageTensorPoint pi hpi d =
      ∑ i, d.weight i • diagonalTensorPoint (rawSection pi hpi (d.point i).val) := by
  ext f
  simp only [averageTensorPoint_apply, FiniteIsometryAverage.value,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    sample_tensorAssignment_eq_diagonal, Complex.real_smul]

/-- The exact norm-one bound is independent of the number of samples. -/
theorem norm_averageTensorPoint_le_one (d : FiniteIsometryAverage (H →L[ℂ] H))
    (f : StrongDual ℂ (Tensor A)) :
    ‖averageTensorPoint pi hpi d f‖ ≤ ‖f‖ := by
  change ‖d.value (tensorAssignment pi hpi f)‖ ≤ ‖f‖
  exact (d.norm_value_le _).trans (norm_tensorAssignment_apply_le pi hpi f)

/-- Canonical-image convexity is proved for the original tensor space,
not for an unrelated parallel norm or tensor completion. -/
private theorem convex_rowClosure :
    Convex ℝ (closure (canonicalImage (𝕜 := ℂ) (rowConvexSet A))) := by
  let k : StrongDual ℂ (StrongDual ℂ (Tensor A)) →ₗ[ℝ]
      WeakDual ℂ (StrongDual ℂ (Tensor A)) :=
    { toFun := StrongDual.toWeakDual
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  let j : Tensor A →ₗ[ℝ] WeakDual ℂ (StrongDual ℂ (Tensor A)) :=
    k.comp
      ((NormedSpace.inclusionInDoubleDual ℂ (Tensor A)).restrictScalars ℝ).toLinearMap
  have he : canonicalImage (𝕜 := ℂ) (rowConvexSet A) = j '' rowConvexSet A := by
    ext w
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨toWeakSpace ℂ (Tensor A) x, ⟨x, hx, rfl⟩, rfl⟩
  rw [he]
  have hconv : Convex ℝ (j '' rowConvexSet A) :=
    (convex_convexHull ℝ (rowGenerators A)).linear_image j
  intro x hx y hy a c ha hc hac
  let f : WeakDual ℂ (StrongDual ℂ (Tensor A)) →
      WeakDual ℂ (StrongDual ℂ (Tensor A)) →
      WeakDual ℂ (StrongDual ℂ (Tensor A)) := fun x' y' => a • x' + c • y'
  have hf : Continuous (Function.uncurry f) :=
    (continuous_fst.const_smul _).add (continuous_snd.const_smul _)
  exact map_mem_closure₂ (f := f) hf hx hy
    (fun _ hx' _ hy' => hconv hx' hy' ha hc hac)

/-- All finite convex averages lie in the same all-test source row closure. -/
theorem averageTensorPoint_rowClosure (d : FiniteIsometryAverage (H →L[ℂ] H)) :
    InWeakStarClosure (averageTensorPoint pi hpi d) (rowConvexSet A) := by
  letI : AddCommMonoid (WeakDual ℂ (StrongDual ℂ (Tensor A))) :=
    (inferInstance : AddCommGroup (WeakDual ℂ (StrongDual ℂ (Tensor A)))).toAddCommMonoid
  change StrongDual.toWeakDual (averageTensorPoint pi hpi d) ∈ _
  rw [averageTensorPoint_eq_sum]
  have h : ∑ i, d.weight i • StrongDual.toWeakDual
      (diagonalTensorPoint (rawSection pi hpi (d.point i).val)) ∈
      closure (canonicalImage (𝕜 := ℂ) (rowConvexSet A)) := by
    apply (convex_rowClosure (A := A)).sum_mem
    · exact fun i hi => d.weight_nonneg i
    · exact d.weight_sum
    · intro i hi
      apply diagonalTensorPoint_rowClosure
      rw [norm_rawSection, norm_isometry]
  have hsmul (r : ℝ) (x : StrongDual ℂ (StrongDual ℂ (Tensor A))) :
      StrongDual.toWeakDual (r • x) = r • StrongDual.toWeakDual x := by
    rfl
  simpa only [map_sum, hsmul] using h

/-- Exact off-diagonal moments for every pair of vectors, using s*s=1. -/
theorem averageTensorPoint_matrixCoefficient
    (d : FiniteIsometryAverage (H →L[ℂ] H)) (eta xi : H) :
    averageTensorPoint pi hpi d
      (matrixCoefficient A H pi.toNonUnitalStarAlgHom eta xi) = inner ℂ eta xi := by
  rw [averageTensorPoint_apply, tensorAssignment_matrixCoefficient,
    FiniteIsometryAverage.value_mulForm]
  rfl

theorem averageTensorPoint_vectorMoment
    (d : FiniteIsometryAverage (H →L[ℂ] H)) (xi : H) :
    averageTensorPoint pi hpi d (vectorMoment A H pi.toNonUnitalStarAlgHom xi) =
      (‖xi‖ ^ 2 : ℂ) := by
  change averageTensorPoint pi hpi d
    (matrixCoefficient A H pi.toNonUnitalStarAlgHom xi xi) = _
  rw [averageTensorPoint_matrixCoefficient, inner_self_eq_norm_sq_to_K]
  rfl

/-- The centrality test is an actual element of the ORIGINAL tensor dual. -/
def centralTest (a : A) (f : StrongDual ℂ (Tensor A)) : StrongDual ℂ (Tensor A) :=
  f.comp (leftAction ℂ A a) - f.comp (rightAction ℂ A a)

theorem averageTensorPoint_centralTest
    (d : FiniteIsometryAverage (H →L[ℂ] H)) (a : A) (f : StrongDual ℂ (Tensor A)) :
    averageTensorPoint pi hpi d (centralTest a f) =
      d.defect (pi a) (tensorAssignment pi hpi f) := by
  rw [centralTest, map_sub]
  simp only [averageTensorPoint_apply, tensorAssignment_left, tensorAssignment_right,
    FiniteIsometryAverage.defect]

/-- Frozen boundary for the next Chat Pro source task: one common finite
probability average for an arbitrary finite set of actual source tests.
This predicate is NOT asserted inhabited by this controller checkpoint. -/
def HasFiniteCentralAverages : Prop :=
  ∀ tests : Finset (A × StrongDual ℂ (Tensor A)), ∀ epsilon : ℝ, 0 < epsilon →
    ∃ d : FiniteIsometryAverage (H →L[ℂ] H), ∀ af ∈ tests,
      ‖d.defect (pi af.1) (tensorAssignment pi hpi af.2)‖ < epsilon

end MathlibAnnex.RepresentedCentralCorner
