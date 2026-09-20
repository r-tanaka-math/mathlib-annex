import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import MathlibAnnex.Analysis.CStarAlgebra.FiniteInterpolation

/-!
# The two-by-two amplification of an irreducible representation

The source algebra is `CStarMatrix`, with its C*-norm, and the representation
space is the Hilbert `lp` sum, not the supremum-norm product.  Matrix units and
the dense orbit of a nonzero vector prove irreducibility directly.

Controller-authored candidate.  No Lean execution is claimed by this file.
-/

set_option autoImplicit false

open scoped ENNReal lp InnerProduct
open MathlibAnnex.Analysis.InnerProductSpace

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

abbrev HilbertTwo (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  HilbertSum (fun _ : Fin 2 => H)

variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The operator with `T` in block `(i,j)` and zero elsewhere. -/
noncomputable def twoBlock (i j : Fin 2) (T : H →L[ℂ] H) :
    HilbertTwo H →L[ℂ] HilbertTwo H :=
  (coordinateEmbedding i).comp (T.comp (coordinateProjection j))

@[simp]
theorem twoBlock_apply (i j : Fin 2) (T : H →L[ℂ] H)
    (x : HilbertTwo H) (k : Fin 2) :
    twoBlock i j T x k = if k = i then T (x j) else 0 := by
  simp [twoBlock, ContinuousLinearMap.comp_apply,
    coordinateEmbedding_apply, lp.coeFn_single, Pi.single_apply, eq_comm]

/-- Matrix multiplication on a two-coordinate Hilbert sum. -/
noncomputable def matrixTwoAction (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (M : CStarMatrix (Fin 2) (Fin 2) A) :
    HilbertTwo H →L[ℂ] HilbertTwo H :=
  ∑ i : Fin 2, ∑ j : Fin 2, twoBlock i j (pi (M i j))

@[simp]
theorem matrixTwoAction_apply (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (M : CStarMatrix (Fin 2) (Fin 2) A) (x : HilbertTwo H)
    (i : Fin 2) :
    matrixTwoAction pi M x i = pi (M i 0) (x 0) + pi (M i 1) (x 1) := by
  fin_cases i <;>
    simp [matrixTwoAction, Fin.sum_univ_two, twoBlock_apply]

/-- The finite Hilbert-sum inner product, in displayed coordinates. -/
theorem inner_hilbertTwo (x y : HilbertTwo H) :
    inner ℂ x y = inner ℂ (x 0) (y 0) + inner ℂ (x 1) (y 1) := by
  rw [lp.inner_eq_tsum, tsum_fintype, Fin.sum_univ_two]

/-- A genuine unital star representation of the two-by-two C*-matrix algebra. -/
noncomputable def matrixTwoRepresentation (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    CStarMatrix (Fin 2) (Fin 2) A →⋆ₐ[ℂ]
      (HilbertTwo H →L[ℂ] HilbertTwo H) where
  toFun := matrixTwoAction pi
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    fin_cases i <;> simp [matrixTwoAction_apply, CStarMatrix.one_apply]
  map_mul' M N := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    fin_cases i <;>
      simp [matrixTwoAction_apply, CStarMatrix.mul_apply, Fin.sum_univ_two,
        map_add, map_mul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.mul_apply, mul_add, add_mul, mul_assoc] <;>
      abel
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    simp [matrixTwoAction_apply]
  map_add' M N := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    simp [matrixTwoAction_apply, CStarMatrix.add_apply,
      map_add, ContinuousLinearMap.add_apply]
    abel
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    fin_cases i <;>
      simp [matrixTwoAction_apply, CStarMatrix.algebraMap_apply,
        ContinuousLinearMap.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
        map_smul, map_one]
  map_star' M := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [inner_hilbertTwo, matrixTwoAction_apply,
      CStarMatrix.star_apply, map_star, ContinuousLinearMap.star_eq_adjoint,
      inner_add_left, inner_add_right,
      ContinuousLinearMap.adjoint_inner_left]
    abel

@[simp]
theorem matrixTwoRepresentation_apply (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (M : CStarMatrix (Fin 2) (Fin 2) A) (x : HilbertTwo H)
    (i : Fin 2) :
    matrixTwoRepresentation pi M x i =
      pi (M i 0) (x 0) + pi (M i 1) (x 1) :=
  matrixTwoAction_apply pi M x i

/-- The algebraic matrix unit with entry `a` in position `(i,j)`. -/
def matrixTwoSingle (i j : Fin 2) (a : A) :
    CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix (fun r s => if r = i ∧ s = j then a else 0)

@[simp]
theorem matrixTwoSingle_apply (i j : Fin 2) (a : A) (r s : Fin 2) :
    matrixTwoSingle i j a r s = if r = i ∧ s = j then a else 0 := rfl

/-- Applying a matrix unit extracts exactly one source coordinate. -/
theorem matrixTwoRepresentation_single (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (i j : Fin 2) (a : A) (x : HilbertTwo H) :
    matrixTwoRepresentation pi (matrixTwoSingle i j a) x =
      coordinateEmbedding i (pi a (x j)) := by
  apply lp.ext
  funext k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [matrixTwoRepresentation_apply, matrixTwoSingle_apply,
      coordinateEmbedding_apply, lp.coeFn_single, Pi.single_apply]

/-- Every vector is the sum of its two embedded coordinates. -/
theorem hilbertTwo_coordinate_decomposition (x : HilbertTwo H) :
    x = coordinateEmbedding (0 : Fin 2) (x 0) +
      coordinateEmbedding (1 : Fin 2) (x 1) := by
  apply lp.ext
  funext i
  fin_cases i <;>
    simp [coordinateEmbedding_apply, lp.coeFn_single, Pi.single_apply, eq_comm]

/-- Matrix amplification preserves irreducibility.  No density or
irreducibility hypothesis on the amplification is assumed. -/
theorem isIrreducible_matrixTwoRepresentation
    [PartialOrder A] [StarOrderedRing A]
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi) :
    StarAlgHom.IsIrreducible (matrixTwoRepresentation pi) := by
  classical
  intro M hMclosed hMreduces
  by_cases hMbot : M = ⊥
  · exact Or.inl hMbot
  right
  obtain ⟨x, hxM, hxne⟩ := M.ne_bot_iff.mp hMbot
  have hj : ∃ j : Fin 2, x j ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hxne
    apply lp.ext
    funext j
    exact hn j
  obtain ⟨j, hj⟩ := hj
  have hemb (i : Fin 2) (y : H) : coordinateEmbedding i y ∈ M := by
    have hclosed : IsClosed {z : H | coordinateEmbedding i z ∈ M} :=
      hMclosed.preimage (coordinateEmbedding i).continuous
    have horbit : Set.range (fun a : A => pi a (x j)) ⊆
        {z : H | coordinateEmbedding i z ∈ M} := by
      rintro _ ⟨a, rfl⟩
      have h := (hMreduces (matrixTwoSingle i j a)).1 hxM
      change (coordinateEmbedding i) ((pi a) (x j)) ∈ M
      simpa only [matrixTwoRepresentation_single] using h
    have hclosure := closure_minimal horbit hclosed
    rw [(StarAlgHom.denseRange_orbitMap_of_irreducible pi hpi hj).closure_range]
      at hclosure
    exact hclosure (Set.mem_univ y)
  apply top_unique
  intro y _
  rw [hilbertTwo_coordinate_decomposition y]
  exact M.add_mem (hemb 0 (y 0)) (hemb 1 (y 1))

/-- A two-coordinate Hilbert sum is nontrivial when its fiber is nontrivial. -/
theorem nontrivial_hilbertTwo [Nontrivial H] : Nontrivial (HilbertTwo H) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  refine ⟨⟨coordinateEmbedding (0 : Fin 2) x, 0, ?_⟩⟩
  intro h
  apply hx
  have hc := congrArg (fun y : HilbertTwo H => y 0) h
  simpa [coordinateEmbedding_apply, lp.coeFn_single] using hc

/-- Squared norm in the Hilbert sum, rather than the supremum norm. -/
theorem norm_hilbertTwo_sq (x : HilbertTwo H) :
    ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
  have h := inner_hilbertTwo x x
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- The self-adjoint off-diagonal dilation of an arbitrary bounded operator. -/
noncomputable def twoDilation (T : H →L[ℂ] H) :
    HilbertTwo H →L[ℂ] HilbertTwo H :=
  twoBlock 0 1 T + twoBlock 1 0 (star T)

@[simp]
theorem twoDilation_apply_zero (T : H →L[ℂ] H) (x : HilbertTwo H) :
    twoDilation T x 0 = T (x 1) := by simp [twoDilation]

@[simp]
theorem twoDilation_apply_one (T : H →L[ℂ] H) (x : HilbertTwo H) :
    twoDilation T x 1 = (star T) (x 0) := by simp [twoDilation]

/-- Self-adjointness does not require `T` itself to be self-adjoint. -/
theorem isSelfAdjoint_twoDilation (T : H →L[ℂ] H) :
    IsSelfAdjoint (twoDilation T) := by
  change star (twoDilation T) = twoDilation T
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [inner_hilbertTwo, twoDilation_apply_zero, twoDilation_apply_one,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have h := ContinuousLinearMap.adjoint_inner_left (star T) (y 0) (x 1)
  simp only [← ContinuousLinearMap.star_eq_adjoint, star_star] at h
  simp only [ContinuousLinearMap.star_eq_adjoint] at h
  rw [← h]
  exact add_comm _ _

/-- The dilation is contractive at the original operator norm, not twice it. -/
theorem norm_twoDilation_le (T : H →L[ℂ] H) : ‖twoDilation T‖ ≤ ‖T‖ := by
  apply (twoDilation T).opNorm_le_bound (norm_nonneg T)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1
  rw [norm_hilbertTwo_sq, twoDilation_apply_zero, twoDilation_apply_one,
    mul_pow, norm_hilbertTwo_sq, mul_add]
  have h0 : ‖T (x 1)‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖x 1‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
        (T.le_opNorm (x 1))
  have h1 : ‖(star T) (x 0)‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖x 0‖ ^ 2 := by
    have hbound : ‖(star T) (x 0)‖ ≤ ‖T‖ * ‖x 0‖ := by
      simpa only [norm_star] using (star T).le_opNorm (x 0)
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hbound
  linarith

end MathlibAnnex.Analysis.CStarAlgebra
