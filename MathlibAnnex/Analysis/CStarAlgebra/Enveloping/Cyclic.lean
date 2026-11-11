import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.UniversalBidual
import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.ApproximateUnit

/-!
# Cyclic representations inside the all-state universal representation

A unit vector in a nondegenerate representation defines a norm-one state
on the original algebra. The lower norm bound follows from strong
convergence of the original algebra's contractive approximate unit.

An original-algebra cyclic vector implies nondegeneracy. Its vector
functional is therefore a state without an additional state hypothesis.
The existing pointed GNS transport then realizes the whole cyclic
representation as an isometric invariant subspace of the actual all-state
Hilbert sum, carrying the cyclic vector to that state's universal vector.
-/

set_option autoImplicit false
noncomputable section

open Filter Set Topology
open scoped CStarAlgebra ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Density of one original-algebra orbit implies nondegeneracy of the
whole representation. No unit or nonzero-vector premise is needed. -/
theorem isNondegenerate_of_denseRange
    (pi : NonUnitalCStarRepresentation A H) (x : H)
    (hcyclic : DenseRange (fun a : A => pi a x)) : pi.IsNondegenerate := by
  intro z hz
  have hinner (a : A) : inner ℂ (pi a x) z = 0 := by
    calc
      inner ℂ (pi a x) z = inner ℂ x (pi (star a) z) := by
        rw [map_star, ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_right]
      _ = 0 := by rw [hz (star a), inner_zero_right]
  have hall (y : H) : inner ℂ y z = 0 :=
    hcyclic.induction_on y (isClosed_eq (by fun_prop) continuous_const) hinner
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp (hall z)

/-- A nondegenerate representation's unit-vector coefficient has norm one
on the original, possibly nonunital algebra. -/
theorem norm_matrixCoefficient_self_eq_one_of_isNondegenerate
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (x : H) (hx : ‖x‖ = 1) : ‖matrixCoefficient pi x x‖ = 1 := by
  have hupper : ‖matrixCoefficient pi x x‖ ≤ 1 := by
    simpa only [hx, one_mul] using norm_matrixCoefficient_le pi x x
  have hscalar : Tendsto (fun e : A => matrixCoefficient pi x x e)
      (_root_.CStarAlgebra.approximateUnit A) (𝓝 (1 : ℂ)) := by
    have h := (innerSL ℂ x).continuous.tendsto x |>.comp
      (stronglyConverges_approximateUnit pi hnd x)
    change Tendsto (fun e : A => inner ℂ x (pi e x))
      (_root_.CStarAlgebra.approximateUnit A) (𝓝 (inner ℂ x x)) at h
    simpa only [matrixCoefficient_apply, inner_self_eq_norm_sq_to_K,
      hx, RCLike.ofReal_one, one_pow] using h
  have hnorm : Tendsto (fun e : A => ‖matrixCoefficient pi x x e‖)
      (_root_.CStarAlgebra.approximateUnit A) (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, norm_one] using (continuous_norm.tendsto (1 : ℂ)).comp hscalar
  refine le_antisymm hupper ?_
  apply le_of_tendsto hnorm
  filter_upwards [(_root_.CStarAlgebra.increasingApproximateUnit A).eventually_norm] with e he
  calc
    ‖matrixCoefficient pi x x e‖ ≤ ‖matrixCoefficient pi x x‖ * ‖e‖ :=
      (matrixCoefficient pi x x).le_opNorm e
    _ ≤ ‖matrixCoefficient pi x x‖ * 1 :=
      mul_le_mul_of_nonneg_left he (norm_nonneg _)
    _ = ‖matrixCoefficient pi x x‖ := mul_one _

/-- Positivity and the approximate-unit norm bound give an actual original
state, with no purity or irreducibility assumption. -/
theorem matrixCoefficient_self_mem_nonUnitalStateSpace_of_isNondegenerate
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (x : H) (hx : ‖x‖ = 1) :
    matrixCoefficient pi x x ∈ nonUnitalStateSpace A :=
  ⟨fun _a ha => matrixCoefficient_self_nonneg pi x ha,
    norm_matrixCoefficient_self_eq_one_of_isNondegenerate pi hnd x hx⟩

/-- Every unit pointed cyclic representation of the original algebra is
contained in the actual all-state universal representation. The state
property is proved here, rather than included among the hypotheses. -/
theorem exists_pointed_universalRepresentation_embedding
    (pi : NonUnitalCStarRepresentation A H) (x : H) (hx : ‖x‖ = 1)
    (hcyclic : DenseRange (fun a : A => pi a x)) :
    ∃ (phi : nonUnitalStateSpace A) (U : H →ₗᵢ[ℂ] UniversalHilbertSpace A),
      phi.val = matrixCoefficient pi x x ∧
      U x = universalStateVector phi ∧
      ∀ (a : A) (z : H), U (pi a z) = universalRepresentation a (U z) := by
  have hnd : pi.IsNondegenerate := isNondegenerate_of_denseRange pi x hcyclic
  have hstate : matrixCoefficient pi x x ∈ nonUnitalStateSpace A :=
    matrixCoefficient_self_mem_nonUnitalStateSpace_of_isNondegenerate pi hnd x hx
  obtain ⟨W, hpoint, hW⟩ := exists_pointed_stateGNS_transport pi x hx hcyclic hstate
  let phi : nonUnitalStateSpace A := ⟨matrixCoefficient pi x x, hstate⟩
  let U : H →ₗᵢ[ℂ] UniversalHilbertSpace A :=
    { ((universalStateEmbedding phi).comp
        (W : H →L[ℂ] NonUnitalStateGNS.Space phi.val phi.property)).toLinearMap with
      norm_map' := fun z => by
        change ‖universalStateEmbedding phi (W z)‖ = ‖z‖
        rw [norm_universalStateEmbedding, W.norm_map] }
  refine ⟨phi, U, rfl, ?_, ?_⟩
  · change universalStateEmbedding phi (W x) =
      universalStateEmbedding phi (NonUnitalStateGNS.vector phi.val phi.property)
    rw [hpoint]
  · intro a z
    change universalStateEmbedding phi (W (pi a z)) =
      universalRepresentation a (universalStateEmbedding phi (W z))
    exact (congrArg (universalStateEmbedding phi) (hW a z)).trans
      (universalRepresentation_embedding a phi (W z)).symm

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
