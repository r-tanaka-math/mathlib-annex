import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.Cyclic

/-!
Typed consumers with no assumed state norm or positivity hypothesis.
-/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra.CyclicConsumers

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open NonUnitalCStarRepresentation

/-- A nondegenerate action and a unit vector supply a state without a
separate norm-one functional premise. -/
example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (x : H) (hx : ‖x‖ = 1) :
    matrixCoefficient pi x x ∈ nonUnitalStateSpace A :=
  matrixCoefficient_self_mem_nonUnitalStateSpace_of_isNondegenerate pi hnd x hx

/-- Original-algebra cyclicity supplies nondegeneracy. -/
example (pi : NonUnitalCStarRepresentation A H) (x : H)
    (hcyclic : DenseRange (fun a : A => pi a x)) : pi.IsNondegenerate :=
  isNondegenerate_of_denseRange pi x hcyclic

/-- The displayed unit cyclic vector is carried to its actual universal
state vector, and the whole representation is intertwined. -/
example (pi : NonUnitalCStarRepresentation A H) (x : H) (hx : ‖x‖ = 1)
    (hcyclic : DenseRange (fun a : A => pi a x)) :
    ∃ (phi : nonUnitalStateSpace A) (U : H →ₗᵢ[ℂ] UniversalHilbertSpace A),
      phi.val = matrixCoefficient pi x x ∧
      U x = universalStateVector phi ∧
      ∀ (a : A) (z : H), U (pi a z) = universalRepresentation a (U z) :=
  exists_pointed_universalRepresentation_embedding pi x hx hcyclic

/-- Containment preserves every matrix coefficient of the cyclic model,
not only the chosen diagonal vector state. -/
example (pi : NonUnitalCStarRepresentation A H) (x : H) (hx : ‖x‖ = 1)
    (hcyclic : DenseRange (fun a : A => pi a x)) :
    ∃ U : H →ₗᵢ[ℂ] UniversalHilbertSpace A,
      ∀ (a : A) (z w : H),
        inner ℂ (U w) (universalRepresentation a (U z)) = inner ℂ w (pi a z) := by
  obtain ⟨_phi, U, _hstate, _hpoint, hU⟩ :=
    exists_pointed_universalRepresentation_embedding pi x hx hcyclic
  refine ⟨U, ?_⟩
  intro a z w
  rw [← hU a z, U.inner_map_map]

end MathlibAnnex.Analysis.CStarAlgebra.CyclicConsumers
