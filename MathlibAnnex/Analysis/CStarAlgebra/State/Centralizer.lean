import MathlibAnnex.Analysis.CStarAlgebra.State.Basic
import MathlibAnnex.Analysis.InnerProductSpace.StrongOperator

/-!
# The centralizer of a state

Norm-closed star-algebra operations and passage to a represented strong limit
are separated. No strong continuity of a star homomorphism is asserted.
-/

set_option autoImplicit false

open Filter Topology
open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A positive state preserves the star operation. -/
theorem apply_star_of_mem_stateSpace (φ : A →L[ℂ] ℂ) (hφ : φ ∈ stateSpace A) (a : A) :
    φ (star a) = star (φ a) :=
  map_star (positiveLinearMapOfMemStateSpace φ hφ) a

/-- Elements which can be moved cyclically through the state. -/
def stateCentralizer (φ : A →L[ℂ] ℂ) (hφ : φ ∈ stateSpace A) : StarSubalgebra ℂ A where
  carrier := {a | ∀ b, φ (a * b) = φ (b * a)}
  zero_mem' := by intro b; simp
  one_mem' := by intro b; simp
  add_mem' := by
    intro a c ha hc b
    simp only [add_mul, mul_add, map_add, ha b, hc b]
  mul_mem' := by
    intro a c ha hc b
    calc
      φ ((a * c) * b) = φ (a * (c * b)) := by rw [mul_assoc]
      _ = φ ((c * b) * a) := ha _
      _ = φ (c * (b * a)) := by rw [mul_assoc]
      _ = φ ((b * a) * c) := hc _
      _ = φ (b * (a * c)) := by rw [mul_assoc]
  algebraMap_mem' := by
    intro c b
    rw [Algebra.commutes c b]
  star_mem' := by
    intro a ha b
    have h := congrArg star (ha (star b))
    simpa only [← apply_star_of_mem_stateSpace φ hφ, star_mul, star_star] using h.symm

@[simp]
theorem mem_stateCentralizer_iff (φ : A →L[ℂ] ℂ) (hφ : φ ∈ stateSpace A) (a : A) :
    a ∈ stateCentralizer φ hφ ↔ ∀ b, φ (a * b) = φ (b * a) := Iff.rfl

theorem isClosed_stateCentralizer (φ : A →L[ℂ] ℂ) (hφ : φ ∈ stateSpace A) :
    IsClosed (stateCentralizer φ hφ : Set A) := by
  change IsClosed {a : A | ∀ b, φ (a * b) = φ (b * a)}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun b ↦ isClosed_eq
    (φ.continuous.comp (continuous_id.mul continuous_const))
    (φ.continuous.comp (continuous_const.mul continuous_id))

/-- A vector-functional centralizer identity passes to an operator strong
limit formed in that same representation. -/
theorem vectorFunctional_mul_eq_mul_of_stronglyConverges
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : Representation A H) (ξ : H) (x : ℕ → A) (u a : A)
    (hx : ContinuousLinearMap.StronglyConverges (fun n ↦ ρ (x n)) atTop (ρ u))
    (heq : ∀ n, Representation.vectorFunctional ρ ξ (x n * a) =
      Representation.vectorFunctional ρ ξ (a * x n)) :
    Representation.vectorFunctional ρ ξ (u * a) =
      Representation.vectorFunctional ρ ξ (a * u) := by
  have hleft : Tendsto (fun n ↦ Representation.vectorFunctional ρ ξ (x n * a)) atTop
      (nhds (Representation.vectorFunctional ρ ξ (u * a))) := by
    simpa only [Representation.vectorFunctional_apply, map_mul, mul_apply_eq_comp,
      Function.comp_def, innerSL_apply_apply] using
      ((innerSL ℂ ξ).continuous.tendsto (ρ u (ρ a ξ))).comp (hx (ρ a ξ))
  have hright : Tendsto (fun n ↦ Representation.vectorFunctional ρ ξ (a * x n)) atTop
      (nhds (Representation.vectorFunctional ρ ξ (a * u))) := by
    simpa only [Representation.vectorFunctional_apply, map_mul, mul_apply_eq_comp,
      Function.comp_def, ContinuousLinearMap.comp_apply, innerSL_apply_apply] using
      (((innerSL ℂ ξ).comp (ρ a)).continuous.tendsto (ρ u ξ)).comp (hx ξ)
  exact tendsto_nhds_unique hleft (by simpa only [← heq] using hright)

end MathlibAnnex.Analysis.CStarAlgebra
