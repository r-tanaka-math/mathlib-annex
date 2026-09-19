import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
The canonical cyclic vector in Mathlib's unital GNS representation.  This
fills only the unit-vector, coefficient, and dense-orbit interface; purity and
irreducibility are deliberately separate.
-/

set_option autoImplicit false

open scoped ComplexOrder InnerProductSpace
open Set UniformSpace

namespace MathlibAnnex.Analysis.CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace PositiveLinearMap

/-- The completion image of the unit is the canonical GNS cyclic vector. -/
noncomputable def gnsCyclicVector (f : A →ₚ[ℂ] ℂ) : f.GNS :=
  (↑(f.toPreGNS 1) : f.GNS)

/-- A normalized positive functional gives a unit canonical GNS vector. -/
theorem norm_gnsCyclicVector (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) :
    ‖gnsCyclicVector f‖ = 1 := by
  have hsq := f.preGNS_norm_sq (f.toPreGNS 1)
  have hre := congrArg Complex.re hsq
  have hre' : ‖f.toPreGNS 1‖ ^ 2 = (1 : ℝ) := by
    simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul] at hre
    rw [← Complex.ofReal_pow] at hre
    simpa only [Complex.ofReal_re, hf, Complex.one_re] using hre
  change ‖(↑(f.toPreGNS 1) : f.GNS)‖ = 1
  rw [UniformSpace.Completion.norm_coe]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  simpa using hre'

/-- The canonical GNS vector realizes the original functional, with Mathlib's
conjugate-first inner-product convention. -/
theorem inner_gnsStarAlgHom_gnsCyclicVector (f : A →ₚ[ℂ] ℂ) (a : A) :
    inner ℂ (gnsCyclicVector f) (f.gnsStarAlgHom a (gnsCyclicVector f)) = f a := by
  simp [gnsCyclicVector, PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.gnsStarAlgHom, PositiveLinearMap.leftMulMapPreGNS]

/-- Every completion vector is approximated by the algebraic orbit of the
canonical GNS vector. -/
theorem denseRange_gnsStarAlgHom_gnsCyclicVector (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A ↦ f.gnsStarAlgHom a (gnsCyclicVector f)) := by
  have hpre : DenseRange f.toPreGNS := f.toPreGNS.surjective.denseRange
  have hcoe : DenseRange ((fun x : f.PreGNS ↦ (x : f.GNS)) ∘ f.toPreGNS) :=
    UniformSpace.Completion.denseRange_coe.comp hpre
      (UniformSpace.Completion.continuous_coe f.PreGNS)
  simpa [Function.comp_def, gnsCyclicVector, PositiveLinearMap.gnsStarAlgHom,
    PositiveLinearMap.leftMulMapPreGNS] using hcoe

/-- The complex-scalar probe fixes the sign at `I`: normalized vector states
are complex-linear rather than conjugate-linear. -/
theorem inner_gnsStarAlgHom_I_gnsCyclicVector (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) :
    inner ℂ (gnsCyclicVector f)
      (f.gnsStarAlgHom ((Complex.I : ℂ) • (1 : A)) (gnsCyclicVector f)) = Complex.I := by
  rw [inner_gnsStarAlgHom_gnsCyclicVector]
  simp [hf]

end PositiveLinearMap

end MathlibAnnex.Analysis.CStarAlgebra
