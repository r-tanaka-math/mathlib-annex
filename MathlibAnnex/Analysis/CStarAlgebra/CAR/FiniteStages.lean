import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Binary matrix stages for the CAR inductive system

This file constructs the actual finite-dimensional C-star algebras
`M_(2^n)(ℂ)` and the standard unital star embeddings `x ↦ x ⊗ 1₂`.
The embeddings are proved injective and hence isometric in the C-star norms.
-/

set_option autoImplicit false

open scoped ComplexOrder Matrix Kronecker

namespace MathlibAnnex.CStarAlgebra.CAR

/-- The `n`-th binary matrix stage. -/
abbrev Stage (n : ℕ) := CStarMatrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

/-- Reindex a pair consisting of an old coordinate and a bit as the next-stage coordinate. -/
def stepIndexEquiv (n : ℕ) : Fin (2 ^ n) × Fin 2 ≃ Fin (2 ^ (n + 1)) :=
  finProdFinEquiv.trans (finCongr (by simp [pow_succ]))

set_option backward.isDefEq.respectTransparency false in
/-- Before reindexing, the standard CAR stage embedding is Kronecker product with `1₂`. -/
noncomputable def amplify (n : ℕ) :
    Stage n →⋆ₐ[ℂ] CStarMatrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℂ where
  toFun x := CStarMatrix.ofMatrix
    (Matrix.kronecker (CStarMatrix.ofMatrix.symm x) (1 : Matrix (Fin 2) (Fin 2) ℂ))
  map_one' := by
    change Matrix.kronecker (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
      (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1
    exact Matrix.one_kronecker_one
  map_mul' x y := by
    change Matrix.kronecker (x * y) (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.kronecker x 1 * Matrix.kronecker y 1
    simpa using Matrix.mul_kronecker_mul x y
      (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ)
  map_zero' := by
    change Matrix.kronecker (0 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
      (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0
    exact Matrix.zero_kronecker _
  map_add' x y := by
    change Matrix.kronecker (x + y) (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.kronecker x 1 + Matrix.kronecker y 1
    exact Matrix.add_kronecker _ _ _
  commutes' r := by
    ext ⟨i, b⟩ ⟨j, c⟩
    by_cases hij : i = j <;> by_cases hbc : b = c <;>
      simp [CStarMatrix.algebraMap_apply, Prod.ext_iff, hij, hbc]
  map_star' x := by
    ext ⟨i, b⟩ ⟨j, c⟩
    by_cases hbc : b = c
    · subst c
      simp [CStarMatrix.star_apply]
    · simp [CStarMatrix.star_apply, hbc, Ne.symm hbc]

theorem amplify_injective (n : ℕ) : Function.Injective (amplify n) := by
  intro x y hxy
  apply CStarMatrix.ext
  intro i j
  have hentry := congrFun (congrFun hxy (i, (0 : Fin 2))) (j, (0 : Fin 2))
  simpa [amplify, Matrix.kronecker_apply] using hentry

/-- The standard diagonal amplification is not onto: it has no matrix entry
between the two new bit coordinates.  Thus it must not be confused with an
ambient matrix-algebra equivalence. -/
theorem amplify_not_surjective (n : ℕ) : ¬ Function.Surjective (amplify n) := by
  intro hsurj
  let y : CStarMatrix (Fin (2 ^ n) × Fin 2) (Fin (2 ^ n) × Fin 2) ℂ :=
    CStarMatrix.ofMatrix (Matrix.single (0, 0) (0, 1) 1)
  obtain ⟨x, hx⟩ := hsurj y
  have hentry := congrFun (congrFun hx ((0, 0) : Fin (2 ^ n) × Fin 2))
    ((0, 1) : Fin (2 ^ n) × Fin 2)
  simp [amplify, y, Matrix.single] at hentry

/-- The standard map from stage `n` to stage `n+1`. -/
noncomputable def step (n : ℕ) : Stage n →⋆ₐ[ℂ] Stage (n + 1) :=
  (CStarMatrix.reindexₐ ℂ ℂ (stepIndexEquiv n)).toStarAlgHom.comp (amplify n)

theorem step_injective (n : ℕ) : Function.Injective (step n) :=
  (CStarMatrix.reindexₐ ℂ ℂ (stepIndexEquiv n)).injective.comp (amplify_injective n)

/-- Each standard stage embedding preserves the actual C-star norm. -/
theorem norm_step (n : ℕ) (x : Stage n) : ‖step n x‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map (step n) (step_injective n) x

/-- Each finite matrix stage is nonzero. -/
instance stageNontrivial (n : ℕ) : Nontrivial (Stage n) := inferInstance

/-- Full finite matrix stages are simple rings. -/
noncomputable instance stageIsSimpleRing (n : ℕ) : IsSimpleRing (Stage n) :=
  IsSimpleRing.of_ringEquiv CStarMatrix.ofMatrixRingEquiv inferInstance

/-- Each matrix stage is finite-dimensional over `ℂ`. -/
noncomputable instance stageFiniteDimensional (n : ℕ) : FiniteDimensional ℂ (Stage n) :=
  LinearEquiv.finiteDimensional (CStarMatrix.ofMatrixₗ (R := ℂ))

/-- Each finite stage is separable in its actual C-star norm topology. -/
noncomputable instance stageSeparableSpace (n : ℕ) :
    TopologicalSpace.SeparableSpace (Stage n) :=
  let e : Stage n ≃L[ℂ] Fin (Module.finrank ℂ (Stage n)) → ℂ :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
  e.symm.surjective.denseRange.separableSpace e.symm.continuous

end MathlibAnnex.CStarAlgebra.CAR
