import MathlibAnnex.Analysis.Distribution.TestField
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! Basis-free divergence and common test-field identities. -/
noncomputable section
open Set
open scoped BigOperators

namespace MathlibAnnex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Divergence is the trace of the Fréchet derivative on a finite-dimensional
real normed space.  The instance is part of the public declaration type. -/
def divergence [FiniteDimensional ℝ E] (W : E → E) (x : E) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ W x).toLinearMap

section FiniteDimensional
variable [FiniteDimensional ℝ E]

/-- Rank-one trace identity in the continuous-linear-map representation. -/
theorem trace_smulRight (L : E →L[ℝ] ℝ) (v : E) :
    LinearMap.trace ℝ E (L.smulRight v).toLinearMap = L v := by
  change LinearMap.trace ℝ E (L.toLinearMap.smulRight v) = L v
  exact LinearMap.trace_smulRight _ _

/-- The minus sign is the chain-rule contribution of translation followed by negation. -/
theorem divergence_sub_smul {φ : E → ℝ} (y z v : E)
    (hφ : DifferentiableAt ℝ φ (y - z)) :
    divergence (fun w => φ (y - w) • v) z = - fderiv ℝ φ (y - z) v := by
  have hsub := (hasFDerivAt_id (𝕜 := ℝ) z).const_sub y
  have hscalar := hφ.hasFDerivAt.comp z hsub
  have hfield := (hscalar.smul_const v).fderiv
  have hfd : fderiv ℝ (fun w : E => φ (y - w) • v) z =
      ((fderiv ℝ φ (y - z)).comp (-(ContinuousLinearMap.id ℝ E))).smulRight v := by
    simpa only [Function.comp_apply, id_eq] using hfield
  rw [divergence, hfd, trace_smulRight]
  simp

namespace CompactC1VectorField

theorem divergence_eq_zero_of_not_mem_carrier (W : CompactC1VectorField E)
    {x : E} (hx : x ∉ W.carrier) : divergence W x = 0 := by
  simp [divergence, W.fderiv_eq_zero_of_not_mem_carrier hx]

theorem support_divergence_subset (W : CompactC1VectorField E) :
    Function.support (divergence W) ⊆ W.carrier := by
  intro x hx
  by_contra h
  exact hx (W.divergence_eq_zero_of_not_mem_carrier h)

end CompactC1VectorField

/-- Coordinate realization, including the empty index type.  The ambient norm
is the standard Pi norm; no identification with `EuclideanSpace` is implicit. -/
theorem divergence_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : (ι → ℝ) → (ι → ℝ)) (x : ι → ℝ) :
    divergence W x = ∑ i : ι, (fderiv ℝ W x (Pi.single i 1)) i := by
  rw [divergence, LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ ι)]
  simp [Matrix.trace, LinearMap.toMatrix_apply]

end FiniteDimensional
end MathlibAnnex
