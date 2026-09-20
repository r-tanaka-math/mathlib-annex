import MathlibAnnex.Analysis.CStarAlgebra.GNSCyclic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional

/-!
# Faithfulness of a tracial cyclic vector state

A faithful representation alone need not have a faithful vector state.
Here the trace identity makes the null space a right ideal. Cyclicity then
shows that a zero-square-value element acts as zero on the entire space.
-/

set_option autoImplicit false

open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The trace identity turns a null square into null squares of all right
multiples. The only analytic input is positive-functional Cauchy--Schwarz. -/
theorem apply_star_mul_self_mul_eq_zero_of_tracial
    (f : A →ₚ[ℂ] ℂ) (hf : ∀ a b, f (a * b) = f (b * a))
    {a : A} (ha : f (star a * a) = 0) (b : A) :
    f (star (a * b) * (a * b)) = 0 := by
  calc
    f (star (a * b) * (a * b)) = f (star b * (star a * (a * b))) := by
      simp only [star_mul, mul_assoc]
    _ = f ((star a * (a * b)) * star b) := hf _ _
    _ = f (star a * (a * (b * star b))) := by simp only [mul_assoc]
    _ = 0 := f.apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero ha _

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Null square value annihilates the whole cyclic orbit, not just its
initial vector. -/
theorem map_orbit_eq_zero_of_vectorFunctional_eq_of_tracial
    (f : A →ₚ[ℂ] ℂ) (hf : ∀ a b, f (a * b) = f (b * a))
    (π : Representation A H) (ξ : H)
    (hξ : ∀ a, Representation.vectorFunctional π ξ a = f a)
    {a : A} (ha : f (star a * a) = 0) (b : A) : π a (π b ξ) = 0 := by
  have hnull := apply_star_mul_self_mul_eq_zero_of_tracial f hf ha b
  have hinner : inner ℂ (π (a * b) ξ) (π (a * b) ξ) = 0 := by
    rw [← Representation.vectorFunctional_star_mul, hξ]
    exact hnull
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsq_real : ‖π (a * b) ξ‖ ^ 2 = 0 := by
    norm_cast at hinner
    apply Complex.ofReal_injective
    simpa using hinner
  have hzero : π (a * b) ξ = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hsq_real)
  simpa only [map_mul, mul_apply_eq_comp] using hzero

/-- A tracial cyclic vector state is faithful whenever the representation
itself is faithful. No separability or irreducibility is assumed. -/
theorem eq_zero_of_apply_star_mul_self_eq_zero_of_tracial
    (f : A →ₚ[ℂ] ℂ) (hf : ∀ a b, f (a * b) = f (b * a))
    (π : Representation A H) (ξ : H)
    (hξ : ∀ a, Representation.vectorFunctional π ξ a = f a)
    (hcyclic : DenseRange (fun b ↦ π b ξ)) (hπ : Function.Injective π)
    {a : A} (ha : f (star a * a) = 0) : a = 0 := by
  have hfun : (π a : H → H) = (fun _ ↦ (0 : H)) := by
    apply (π a).continuous.ext_on hcyclic continuous_const
    intro x hx
    obtain ⟨b, rfl⟩ := hx
    exact map_orbit_eq_zero_of_vectorFunctional_eq_of_tracial f hf π ξ hξ ha b
  have hmap : π a = 0 := ContinuousLinearMap.ext fun x ↦ congrFun hfun x
  apply hπ
  simpa only [map_zero] using hmap

end MathlibAnnex.Analysis.CStarAlgebra
