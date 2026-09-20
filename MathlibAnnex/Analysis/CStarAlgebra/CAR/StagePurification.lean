import MathlibAnnex.Analysis.CStarAlgebra.CAR.CornerLift
import MathlibAnnex.Analysis.CStarAlgebra.CAR.NoCompacts
import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import MathlibAnnex.Analysis.InnerProductSpace.FiniteEmbedding
import MathlibAnnex.Analysis.InnerProductSpace.ProjectionLimit

/-!
# Finite-stage vector-state reconstruction

This file formalizes the algebraic core of finite-stage purification.  A
family in the represented root corner is assembled with the stage matrix
units.  Its vector state has precisely the prescribed Gram matrix on the
whole finite stage.  The remaining existence problem is isolated to finding
such a corner family with the target Gram matrix.
-/

set_option autoImplicit false

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

namespace MathlibAnnex.CStarAlgebra.CAR

/-- Assemble a vector from a family in the represented root corner. -/
noncomputable def reconstructedStageVector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ρ : Representation Limit H) (n : ℕ)
    (w : Fin (2 ^ n) → H) : H :=
  ∑ i, ρ (limitMatrixUnit n i 0) (w i)

theorem representation_matrixUnit_reconstructedStageVector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ρ : Representation Limit H) (n : ℕ)
    (w : Fin (2 ^ n) → H)
    (p q : Fin (2 ^ n)) :
    ρ (limitMatrixUnit n p q) (reconstructedStageVector ρ n w) =
      ρ (limitMatrixUnit n p 0) (w q) := by
  classical
  simp only [reconstructedStageVector, map_sum]
  rw [Finset.sum_eq_single q]
  · rw [← ContinuousLinearMap.mul_apply, ← map_mul]
    simp
  · intro i _ hiq
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, limitMatrixUnit_mul]
    simp [Ne.symm hiq]
  · simp

private theorem inner_matrixUnit_columns
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ρ : Representation Limit H) (n : ℕ)
    (w : Fin (2 ^ n) → H)
    (hw : ∀ i, ρ (limitMatrixUnit n 0 0) (w i) = w i)
    (i p q : Fin (2 ^ n)) :
    inner ℂ (ρ (limitMatrixUnit n i 0) (w i))
        (ρ (limitMatrixUnit n p 0) (w q)) =
      if i = p then inner ℂ (w i) (w q) else 0 := by
  classical
  have hadj : ContinuousLinearMap.adjoint (ρ (limitMatrixUnit n i 0)) =
      ρ (limitMatrixUnit n 0 i) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star,
      star_limitMatrixUnit]
  calc
    inner ℂ (ρ (limitMatrixUnit n i 0) (w i))
        (ρ (limitMatrixUnit n p 0) (w q)) =
      inner ℂ (w i)
        (ContinuousLinearMap.adjoint (ρ (limitMatrixUnit n i 0))
          (ρ (limitMatrixUnit n p 0) (w q))) :=
        (ContinuousLinearMap.adjoint_inner_right
          (ρ (limitMatrixUnit n i 0)) (w i)
            (ρ (limitMatrixUnit n p 0) (w q))).symm
    _ = inner ℂ (w i)
        (ρ (limitMatrixUnit n 0 i * limitMatrixUnit n p 0) (w q)) := by
          rw [hadj, map_mul]
          rfl
    _ = if i = p then inner ℂ (w i) (w q) else 0 := by
      by_cases hip : i = p
      · subst p
        simp [hw]
      · rw [limitMatrixUnit_mul]
        simp [hip]

/-- The reconstructed vector has the requested Gram coefficient on every
matrix unit. -/
theorem vectorFunctional_reconstructedStageVector_matrixUnit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ρ : Representation Limit H) (n : ℕ)
    (w : Fin (2 ^ n) → H)
    (hw : ∀ i, ρ (limitMatrixUnit n 0 0) (w i) = w i)
    (p q : Fin (2 ^ n)) :
    Representation.vectorFunctional ρ (reconstructedStageVector ρ n w)
        (limitMatrixUnit n p q) = inner ℂ (w p) (w q) := by
  classical
  rw [Representation.vectorFunctional_apply,
    representation_matrixUnit_reconstructedStageVector]
  simp only [reconstructedStageVector, sum_inner]
  rw [Finset.sum_eq_single p]
  · rw [inner_matrixUnit_columns ρ n w hw p p q]
    simp
  · intro i _ hip
    rw [inner_matrixUnit_columns ρ n w hw i p q]
    simp [hip]
  · simp

private theorem vectorFunctional_matrixUnit_eq_cornerGram
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Representation Limit H) (n : ℕ)
    (η : H) (p q : Fin (2 ^ n)) :
    Representation.vectorFunctional σ η (limitMatrixUnit n p q) =
      inner ℂ (σ (limitMatrixUnit n 0 p) η)
        (σ (limitMatrixUnit n 0 q) η) := by
  simpa using Representation.vectorFunctional_star_mul σ η
    (limitMatrixUnit n 0 p) (limitMatrixUnit n 0 q)

/-- Equality on the matrix-unit basis gives equality on the entire embedded
finite stage. -/
theorem continuousLinearMap_eq_on_ofStage_of_eq_matrixUnit
    (φ ψ : Limit →L[ℂ] ℂ) (n : ℕ)
    (h : ∀ i j : Fin (2 ^ n),
      φ (limitMatrixUnit n i j) = ψ (limitMatrixUnit n i j))
    (c : Stage n) : φ (ofStage n c) = ψ (ofStage n c) := by
  rw [ofStage_eq_sum_smul_limitMatrixUnit]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [h i j]

/-- Proof-bearing finite-stage purification core.  Any root-corner family
with the GNS Gram matrix reconstructs a vector state agreeing with the target
vector state on the whole chosen matrix stage; no rank-one restriction on the
target state is used. -/
theorem reconstructedStageVector_vectorFunctional_eq_on_stage
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (ρ : Representation Limit H) (σ : Representation Limit K)
    (n : ℕ) (η : K) (w : Fin (2 ^ n) → H)
    (hw : ∀ i, ρ (limitMatrixUnit n 0 0) (w i) = w i)
    (hgram : ∀ i j,
      inner ℂ (w i) (w j) =
        inner ℂ (σ (limitMatrixUnit n 0 i) η)
          (σ (limitMatrixUnit n 0 j) η))
    (c : Stage n) :
    Representation.vectorFunctional ρ (reconstructedStageVector ρ n w)
        (ofStage n c) = Representation.vectorFunctional σ η (ofStage n c) := by
  apply continuousLinearMap_eq_on_ofStage_of_eq_matrixUnit _ _ n _ c
  intro i j
  rw [vectorFunctional_reconstructedStageVector_matrixUnit ρ n w hw i j,
    hgram i j]
  exact (vectorFunctional_matrixUnit_eq_cornerGram σ n η i j).symm

/-- The reconstruction preserves normalization. -/
theorem norm_reconstructedStageVector_eq_one
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (ρ : Representation Limit H) (σ : Representation Limit K)
    (n : ℕ) (η : K) (hη : ‖η‖ = 1)
    (w : Fin (2 ^ n) → H)
    (hw : ∀ i, ρ (limitMatrixUnit n 0 0) (w i) = w i)
    (hgram : ∀ i j,
      inner ℂ (w i) (w j) =
        inner ℂ (σ (limitMatrixUnit n 0 i) η)
          (σ (limitMatrixUnit n 0 j) η)) :
    ‖reconstructedStageVector ρ n w‖ = 1 := by
  have hstate := reconstructedStageVector_vectorFunctional_eq_on_stage
    ρ σ n η w hw hgram (1 : Stage n)
  have hofone : ofStage n (1 : Stage n) = 1 := map_one (ofStage n)
  rw [hofone] at hstate
  have hinner :
      inner ℂ (reconstructedStageVector ρ n w)
          (reconstructedStageVector ρ n w) = inner ℂ η η := by
    simpa [Representation.vectorFunctional_apply] using hstate
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
  have hre : ‖reconstructedStageVector ρ n w‖ ^ 2 = ‖η‖ ^ 2 := by
    exact_mod_cast hinner
  rw [hη, one_pow] at hre
  nlinarith [norm_nonneg (reconstructedStageVector ρ n w)]

/-- In every nonzero irreducible CAR representation, the represented root
corner has infinite Hilbert dimension.  Otherwise the corner projection
would be a nonzero compact operator in the represented CAR image. -/
theorem not_finiteDimensional_range_rootCorner
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ρ : Representation Limit H)
    (hρ : ρ.IsIrreducible) (n : ℕ) :
    ¬ FiniteDimensional ℂ
      (LinearMap.range (ρ (limitMatrixUnit n 0 0)).toLinearMap) := by
  intro hfinite
  let P : H →L[ℂ] H := ρ (limitMatrixUnit n 0 0)
  let R : Submodule ℂ H := LinearMap.range P.toLinearMap
  let Q : H →L[ℂ] R := P.codRestrict R (fun x => ⟨x, rfl⟩)
  letI : FiniteDimensional ℂ R := hfinite
  letI : LocallyCompactSpace R :=
    LocallyCompactSpace.of_finiteDimensional_of_complete ℂ R
  have hQ : IsCompactOperator Q :=
    isCompactOperator_of_locallyCompactSpace_dom Q
  have hcompact : IsCompactOperator P := by
    have hc := hQ.clm_comp R.subtypeL
    simpa [P, Q, R, Function.comp_def] using hc
  have hezero : limitMatrixUnit n 0 0 = 0 :=
    eq_zero_of_isCompactOperator_image ρ hρ hcompact
  have hstage : matrixUnit n 0 0 = 0 := by
    apply ofStage_injective n
    change ofStage n (matrixUnit n 0 0) = 0 at hezero
    rw [map_zero]
    exact hezero
  have hentry := congrFun (congrFun hstage (0 : Fin (2 ^ n)))
    (0 : Fin (2 ^ n))
  simp at hentry

/-- Any finite Gram matrix occurring in a Hilbert space can be realized by
vectors in the represented root corner of an irreducible CAR
representation.  Infinite-dimensionality of the corner supplies an
isometric copy of the finite-dimensional span of the input family. -/
theorem exists_rootCornerFamily_with_gram
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (ρ : Representation Limit H) (hρ : ρ.IsIrreducible)
    (n : ℕ) {I : Type*} [Fintype I] (v : I → K) :
    ∃ w : I → H,
      (∀ i, ρ (limitMatrixUnit n 0 0) (w i) = w i) ∧
      ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j) := by
  classical
  let P : H →L[ℂ] H := ρ (limitMatrixUnit n 0 0)
  have hP : IsStarProjection P :=
    (isStarProjection_limitMatrixUnit_zero_zero n).map ρ
  let R : Submodule ℂ H := LinearMap.range P.toLinearMap
  letI : CompleteSpace R := IsComplete.completeSpace_coe
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range hP.isIdempotentElem).isComplete
  let S : Submodule ℂ K := Submodule.span ℂ (Set.range v)
  letI : FiniteDimensional ℂ S :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  have hR : ¬ FiniteDimensional ℂ R := by
    simpa [P, R] using
      not_finiteDimensional_range_rootCorner ρ hρ n
  obtain ⟨L⟩ :=
    nonempty_linearIsometry_of_finiteDimensional_of_not_finiteDimensional
      (E := S) (F := R) hR
  let vS : I → S := fun i =>
    ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
  let w : I → H := fun i => (L (vS i) : R)
  refine ⟨w, ?_, ?_⟩
  · intro i
    have hmem : w i ∈ LinearMap.range P.toLinearMap := (L (vS i)).property
    exact (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap
        hP.isIdempotentElem)).mp hmem
  · intro i j
    change inner ℂ (L (vS i)) (L (vS j)) = inner ℂ (vS i) (vS j)
    exact L.inner_map_map (vS i) (vS j)

/-- Every unit vector state has an exact unit-vector realization on an
arbitrary finite CAR stage inside any irreducible CAR representation.  This
is the finite-stage purification step, with the root-corner Gram family now
constructed rather than assumed. -/
theorem exists_unitVector_vectorFunctional_eq_on_stage
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (ρ : Representation Limit H) (hρ : ρ.IsIrreducible)
    (σ : Representation Limit K) (n : ℕ) (η : K) (hη : ‖η‖ = 1) :
    ∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ c : Stage n,
      Representation.vectorFunctional ρ ξ (ofStage n c) =
        Representation.vectorFunctional σ η (ofStage n c) := by
  let v : Fin (2 ^ n) → K := fun i => σ (limitMatrixUnit n 0 i) η
  obtain ⟨w, hw, hgram⟩ :=
    exists_rootCornerFamily_with_gram ρ hρ n v
  refine ⟨reconstructedStageVector ρ n w,
    norm_reconstructedStageVector_eq_one ρ σ n η hη w hw ?_, ?_⟩
  · intro i j
    exact hgram i j
  · intro c
    exact reconstructedStageVector_vectorFunctional_eq_on_stage
      ρ σ n η w hw hgram c

end MathlibAnnex.CStarAlgebra.CAR
