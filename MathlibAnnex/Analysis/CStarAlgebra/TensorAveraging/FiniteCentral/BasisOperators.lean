import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Operators constructed from one Hilbert basis

C06 controller source, UNBUILT. Finite coordinate projections and extensions
of orthonormal families use the SAME Hilbert basis; no separability assumption
and no unexplained isometry between infinite-dimensional spaces is used.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace MathlibAnnex.FiniteCentral
universe v w
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι : Type w}
variable (b : HilbertBasis ι ℂ H)

@[simp] theorem basis_inner (i j : ι) :
    inner ℂ (b i) (b j) = if i = j then 1 else 0 :=
  (orthonormal_iff_ite.mp b.orthonormal) i j

/-- Equality on the basis implies equality of actual bounded operators. -/
theorem operator_ext_basis {T U : H →L[ℂ] H}
    (h : ∀ i, T (b i) = U (b i)) : T = U := by
  ext x
  have hT := T.hasSum (b.hasSum_repr x)
  have hU := U.hasSum (b.hasSum_repr x)
  simp only [map_smul, h] at hT
  simp only [map_smul] at hU
  exact hT.unique hU

/-- A coefficient rank-one operator, with the inner product linear on the right. -/
def matrixUnit (i j : ι) : H →L[ℂ] H := (innerSL ℂ (b j)).smulRight (b i)

@[simp] theorem matrixUnit_apply (i j : ι) (x : H) :
    matrixUnit b i j x = inner ℂ (b j) x • b i := rfl

@[simp] theorem matrixUnit_basis (i j k : ι) :
    matrixUnit b i j (b k) = if j = k then b i else 0 := by
  classical
  simp [matrixUnit_apply, basis_inner]

@[simp] theorem star_matrixUnit (i j : ι) :
    star (matrixUnit b i j) = matrixUnit b j i := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [matrixUnit_apply, inner_smul_left, inner_smul_right,
    inner_conj_symm]
  ring

@[simp] theorem matrixUnit_mul (i j k l : ι) :
    matrixUnit b i j * matrixUnit b k l =
      if j = k then matrixUnit b i l else 0 := by
  classical
  ext x
  by_cases h : j = k <;>
    simp [h, matrixUnit_apply, basis_inner, b.orthonormal.norm_eq_one]

/-- Orthogonal projection onto a finite set of basis coordinates. -/
def coordinateProjection (s : Finset ι) : H →L[ℂ] H :=
  ∑ i ∈ s, matrixUnit b i i

@[simp] theorem coordinateProjection_apply (s : Finset ι) (x : H) :
    coordinateProjection b s x = ∑ i ∈ s, inner ℂ (b i) x • b i := by
  simp [coordinateProjection, matrixUnit_apply]

@[simp] theorem coordinateProjection_basis (s : Finset ι) (j : ι) :
    coordinateProjection b s (b j) = if j ∈ s then b j else 0 := by
  classical
  simp [coordinateProjection_apply, basis_inner, Finset.sum_ite_eq']

@[simp] theorem star_coordinateProjection (s : Finset ι) :
    star (coordinateProjection b s) = coordinateProjection b s := by
  simp [coordinateProjection]

@[simp] theorem coordinateProjection_idempotent (s : Finset ι) :
    coordinateProjection b s * coordinateProjection b s = coordinateProjection b s := by
  apply operator_ext_basis b
  intro j
  classical
  by_cases hj : j ∈ s <;> simp [ContinuousLinearMap.mul_apply, hj]

/-- A selfadjoint idempotent has norm at most one, also in the zero space. -/
theorem norm_projection_le_one (P : H →L[ℂ] H)
    (hs : star P = P) (hi : P * P = P) : ‖P‖ ≤ 1 := by
  have hn := CStarRing.norm_star_mul_self (x := P)
  rw [hs, hi] at hn
  nlinarith [norm_nonneg P]

theorem norm_coordinateProjection_le_one (s : Finset ι) :
    ‖coordinateProjection b s‖ ≤ 1 :=
  norm_projection_le_one _ (star_coordinateProjection b s) (coordinateProjection_idempotent b s)

@[simp] theorem tail_projection_idempotent (s : Finset ι) :
    (1 - coordinateProjection b s) * (1 - coordinateProjection b s) =
      1 - coordinateProjection b s := by
  simp only [sub_mul, mul_sub, one_mul, mul_one, coordinateProjection_idempotent]
  abel

theorem norm_tail_projection_le_one (s : Finset ι) :
    ‖(1 : H →L[ℂ] H) - coordinateProjection b s‖ ≤ 1 :=
  norm_projection_le_one _ (by simp) (tail_projection_idempotent b s)

theorem coordinateProjection_nonneg (s : Finset ι) :
    0 ≤ coordinateProjection b s := by
  have h := star_mul_self_nonneg (coordinateProjection b s)
  simpa only [star_coordinateProjection, coordinateProjection_idempotent] using h

theorem tail_projection_nonneg (s : Finset ι) :
    0 ≤ (1 : H →L[ℂ] H) - coordinateProjection b s := by
  have h := star_mul_self_nonneg ((1 : H →L[ℂ] H) - coordinateProjection b s)
  simpa only [star_sub, star_one, star_coordinateProjection,
    tail_projection_idempotent] using h

/-- The finite-subset net is strongly convergent without a countable basis. -/
theorem tendsto_coordinateProjection (x : H) :
    Tendsto (fun s : Finset ι => coordinateProjection b s x) atTop (𝓝 x) := by
  simp only [coordinateProjection_apply]
  simpa only [HasSum, HilbertBasis.repr_apply_apply, SummationFilter.unconditional] using
    b.hasSum_repr x

/-- Extend an actual orthonormal family by the Hilbert-sum construction. -/
def basisIsometry (c : ι → H) (hc : Orthonormal ℂ c) : H →ₗᵢ[ℂ] H :=
  hc.orthogonalFamily.linearIsometry.comp b.repr.toLinearIsometry

@[simp] theorem basisIsometry_basis (c : ι → H) (hc : Orthonormal ℂ c) (i : ι) :
    basisIsometry b c hc (b i) = c i := by
  classical
  change hc.orthogonalFamily.linearIsometry (b.repr (b i)) = c i
  rw [b.repr_self, OrthogonalFamily.linearIsometry_apply_single]
  simp only [LinearIsometry.toSpanSingleton_apply, one_smul]

/-- Adjoints give the actual isometry equation for the bounded extension. -/
theorem star_mul_of_linearIsometry (w : H →ₗᵢ[ℂ] H) :
    star w.toContinuousLinearMap * w.toContinuousLinearMap = 1 := by
  ext x
  apply ext_inner_left ℂ
  intro y
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap, w.inner_map_map]

/-- Reindexing an orthonormal family along an injection. -/
theorem orthonormal_embedding (e : ι ↪ ι) : Orthonormal ℂ (fun i => b (e i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [basis_inner, e.injective.eq_iff]

def basisEmbedding (e : ι ↪ ι) : H →ₗᵢ[ℂ] H :=
  basisIsometry b (fun i => b (e i)) (orthonormal_embedding b e)

@[simp] theorem basisEmbedding_basis (e : ι ↪ ι) (i : ι) :
    basisEmbedding b e (b i) = b (e i) := basisIsometry_basis _ _ _ _

/-- The finite coordinate corner is a finite linear combination of matrix units. -/
theorem compression_eq_matrix_sum (s : Finset ι) (T : H →L[ℂ] H) :
    coordinateProjection b s * T * coordinateProjection b s =
      ∑ i ∈ s, ∑ j ∈ s, (inner ℂ (b i) (T (b j))) • matrixUnit b i j := by
  classical
  ext x
  simp only [ContinuousLinearMap.mul_apply, coordinateProjection_apply,
    map_sum, map_smul, inner_sum, inner_smul_right, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, matrixUnit_apply, smul_smul, Finset.sum_smul,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

end MathlibAnnex.FiniteCentral
