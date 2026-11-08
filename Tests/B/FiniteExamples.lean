import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeII1
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Typed consumers for finiteness and the type II₁ boundary

The matrix consumer instantiates the faithful-trace argument with the actual
matrix trace. The scalar algebra is a finite factor but is not type II₁.
The two-coordinate diagonal algebra is finite and is not a factor.
-/

set_option autoImplicit false

open scoped ComplexOrder

noncomputable section

namespace VonNeumannAlgebra

private theorem finite_on_finiteDimensional_space
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] (M : VonNeumannAlgebra H) :
    IsFinite M := by
  intro v _ hv
  have hleft : Function.LeftInverse (fun x ↦ (star v : H →L[ℂ] H) x) v := by
    intro x
    change (star v * v) x = (1 : H →L[ℂ] H) x
    rw [hv]
  have hsurj : Function.Surjective v :=
    LinearMap.surjective_of_injective (f := v.toLinearMap) hleft.injective
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hsurj x
  change v (star v (v y)) = v y
  exact congrArg v (hleft y)

/-- The ordinary matrix trace supplies the actual faithful trace used by
the algebraic proof, for every finite matrix size. -/
example {n : Type*} [Fintype n] [DecidableEq n]
    {v : Matrix n n ℂ} (hv : star v * v = 1) :
    v ∈ unitary (Matrix n n ℂ) := by
  refine Unitary.mem_iff.mpr ⟨hv, ?_⟩
  apply (Matrix.traceLinearMap n ℂ ℂ).mul_star_self_eq_one_of_faithful_tracial
    (fun a b => Matrix.trace_mul_comm a b) ?_ hv
  intro a ha
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ha

private def scalarAlgebra : VonNeumannAlgebra ℂ where
  toStarSubalgebra := ⊤
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (Set.univ : Set (ℂ →L[ℂ] ℂ))) = Set.univ
    exact Set.Subset.antisymm (Set.subset_univ _) Set.subset_centralizer_centralizer

private theorem complex_end_eq_smul_one (T : ℂ →L[ℂ] ℂ) :
    T = T 1 • (1 : ℂ →L[ℂ] ℂ) := by
  apply ContinuousLinearMap.ext
  intro z
  calc
    T z = T (z • (1 : ℂ)) := by simp
    _ = z • T 1 := map_smul T z 1
    _ = (T 1 • (1 : ℂ →L[ℂ] ℂ)) z := by simp [mul_comm]

private theorem isFactor_scalarAlgebra : IsFactor scalarAlgebra := by
  refine ⟨?_, ?_⟩
  · intro h
    have h10 : (1 : ℂ) = 0 := congrArg (fun T : ℂ →L[ℂ] ℂ => T 1) h
    exact one_ne_zero h10
  · intro z _ _
    exact ⟨z 1, complex_end_eq_smul_one z⟩

private theorem finiteDimensional_scalarAlgebra :
    FiniteDimensional ℂ scalarAlgebra.toStarSubalgebra := by
  let f : ℂ →ₗ[ℂ] scalarAlgebra.toStarSubalgebra :=
    { toFun := fun c => c • (1 : scalarAlgebra.toStarSubalgebra)
      map_add' := fun c d => add_smul c d 1
      map_smul' := fun c d => by simp only [RingHom.id_apply, smul_eq_mul, smul_smul] }
  apply FiniteDimensional.of_surjective f
  intro T
  refine ⟨(T : ℂ →L[ℂ] ℂ) 1, ?_⟩
  apply Subtype.ext
  exact (complex_end_eq_smul_one T).symm

/-- A one-dimensional algebra is finite and a factor, while its algebra
dimension excludes type II₁. -/
example : IsFinite scalarAlgebra ∧ IsFactor scalarAlgebra ∧ ¬ IsTypeII1 scalarAlgebra := by
  letI := finiteDimensional_scalarAlgebra
  exact ⟨finite_on_finiteDimensional_space scalarAlgebra,
    isFactor_scalarAlgebra, not_isTypeII1_of_finiteDimensional scalarAlgebra⟩

private abbrev TwoDimensionalSpace := EuclideanSpace ℂ (Fin 2)

private def firstVector : TwoDimensionalSpace := EuclideanSpace.single 0 1

private def secondVector : TwoDimensionalSpace := EuclideanSpace.single 1 1

private def firstProjection : TwoDimensionalSpace →L[ℂ] TwoDimensionalSpace :=
  InnerProductSpace.rankOne ℂ firstVector firstVector

private theorem star_firstProjection : star firstProjection = firstProjection := by
  unfold firstProjection
  rw [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]

/-- The commutant of the first-coordinate projection is the diagonal
two-coordinate algebra. The construction uses only the standard centralizer. -/
private def diagonalAlgebra : VonNeumannAlgebra TwoDimensionalSpace where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ ({firstProjection} : Set
    (TwoDimensionalSpace →L[ℂ] TwoDimensionalSpace))
  centralizer_centralizer' := by
    exact Set.centralizer_centralizer_centralizer _

private theorem firstProjection_mem_diagonalAlgebra : firstProjection ∈ diagonalAlgebra := by
  change firstProjection ∈ StarSubalgebra.centralizer ℂ ({firstProjection} : Set
    (TwoDimensionalSpace →L[ℂ] TwoDimensionalSpace))
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  intro g hg
  have hg' : g = firstProjection := Set.mem_singleton_iff.mp hg
  subst g
  exact ⟨rfl, by rw [star_firstProjection]⟩

private theorem firstProjection_central_diagonalAlgebra
    (a : TwoDimensionalSpace →L[ℂ] TwoDimensionalSpace) (ha : a ∈ diagonalAlgebra) :
    a * firstProjection = firstProjection * a := by
  change a ∈ StarSubalgebra.centralizer ℂ ({firstProjection} : Set
    (TwoDimensionalSpace →L[ℂ] TwoDimensionalSpace)) at ha
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp ha firstProjection
    (Set.mem_singleton firstProjection)).1.symm

private theorem not_isFactor_diagonalAlgebra : ¬ IsFactor diagonalAlgebra := by
  intro hfactor
  obtain ⟨c, hc⟩ := hfactor.2 firstProjection firstProjection_mem_diagonalAlgebra
    firstProjection_central_diagonalAlgebra
  have hc1 : (1 : ℂ) = c := by
    have h := congrArg
      (fun T : TwoDimensionalSpace →L[ℂ] TwoDimensionalSpace => T firstVector 0) hc
    simpa [firstProjection, firstVector, InnerProductSpace.rankOne_apply,
      EuclideanSpace.inner_single_left, PiLp.single_apply] using h
  have hc0 : (0 : ℂ) = c := by
    have h := congrArg
      (fun T : TwoDimensionalSpace →L[ℂ] TwoDimensionalSpace => T secondVector 1) hc
    simpa [firstProjection, firstVector, secondVector, InnerProductSpace.rankOne_apply,
      EuclideanSpace.inner_single_left, PiLp.single_apply] using h
  exact one_ne_zero (hc1.trans hc0.symm)

/-- Finiteness alone does not imply factorality or type II₁. This is the
concrete two-coordinate diagonal algebra, with a nonscalar central projection. -/
example : IsFinite diagonalAlgebra ∧ ¬ IsFactor diagonalAlgebra ∧ ¬ IsTypeII1 diagonalAlgebra := by
  refine ⟨finite_on_finiteDimensional_space diagonalAlgebra, not_isFactor_diagonalAlgebra, ?_⟩
  intro h
  exact not_isFactor_diagonalAlgebra h.1

end VonNeumannAlgebra
