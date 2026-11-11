import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.Basic

/-!
Typed consumers of the actual all-state representation and original-range
envelope. These declarations require proof terms; this is not a list of
`#check` commands. Their compilation is recorded with the candidate evidence.
-/

set_option autoImplicit false
noncomputable section

open Filter Set Topology
open scoped CStarAlgebra InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra.EnvelopingConsumers

universe u

section Ordered

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

/-- A displayed arbitrary state, without a purity premise, is recovered by
its unit vector in the all-state universal sum. -/
example (phi : nonUnitalStateSpace A) (a : A) :
    ‖universalStateVector phi‖ = 1 ∧
      inner ℂ (universalStateVector phi)
        (universalRepresentation a (universalStateVector phi)) = phi.val a := by
  refine ⟨norm_universalStateVector phi, ?_⟩
  exact congrArg (fun f : StrongDual ℂ A => f a)
    (matrixCoefficient_universalStateVector phi)

/-- The coordinate is isometric and intertwines the original algebra. -/
example (phi : nonUnitalStateSpace A)
    (x : NonUnitalStateGNS.Space phi.val phi.property) (a : A) :
    ‖universalStateEmbedding phi x‖ = ‖x‖ ∧
      universalRepresentation a (universalStateEmbedding phi x) =
        universalStateEmbedding phi
          (NonUnitalStateGNS.representation phi.val phi.property a x) :=
  ⟨norm_universalStateEmbedding phi x, universalRepresentation_embedding a phi x⟩

/-- Consumers can transfer general two-vector coefficients, as required for
all-dual-functional norm tests. -/
example (phi : nonUnitalStateSpace A)
    (x y : NonUnitalStateGNS.Space phi.val phi.property) :
    NonUnitalCStarRepresentation.matrixCoefficient
      (universalRepresentation (A := A))
      (universalStateEmbedding phi x) (universalStateEmbedding phi y) =
    NonUnitalCStarRepresentation.matrixCoefficient
      (NonUnitalStateGNS.representation phi.val phi.property) x y :=
  matrixCoefficient_universalStateEmbedding phi x y

/-- Density is for the original, possibly nonunital algebra, not just its
unitization. -/
example (phi : nonUnitalStateSpace A) :
    DenseRange (fun a : A => NonUnitalStateGNS.representation phi.val phi.property a
      (NonUnitalStateGNS.vector phi.val phi.property)) :=
  NonUnitalStateGNS.denseRange_representation_vector phi.val phi.property

/-- There is no original-algebra annihilator vector in the universal sum. -/
example (x : UniversalHilbertSpace A) (hx : ∀ a : A, universalRepresentation a x = 0) :
    x = 0 :=
  isNondegenerate_universalRepresentation x hx

/-- The actual canonical approximate unit tends to the identity on each
universal vector. -/
example (x : UniversalHilbertSpace A) :
    Tendsto (fun e : A => universalRepresentation e x)
      (_root_.CStarAlgebra.approximateUnit A) (𝓝 x) :=
  NonUnitalCStarRepresentation.stronglyConverges_approximateUnit
    (universalRepresentation (A := A)) isNondegenerate_universalRepresentation x

set_option maxHeartbeats 1000000 in
/-- The concrete original inclusion preserves multiplication, star and norm. -/
example (a b : A) :
    envelopingInclusion (A := A) (a * b) = envelopingInclusion (A := A) a * envelopingInclusion (A := A) b ∧
      envelopingInclusion (A := A) (star a) = star (envelopingInclusion (A := A) a) ∧
      ‖envelopingInclusion (A := A) a‖ = ‖a‖ :=
  ⟨map_mul (envelopingInclusion (A := A)) a b,
    map_star (envelopingInclusion (A := A)) a, norm_envelopingInclusion (A := A) a⟩

/-- The accepted VN topology is applied to the original all-state range. -/
example (T : UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A) :
    T ∈ envelopingVonNeumannAlgebra (A := A) ↔
      ContinuousLinearMapWOT.ofCLM T ∈
        closure (ContinuousLinearMapWOT.ofCLM ''
          Set.range (universalRepresentation (A := A))) :=
  mem_envelopingVonNeumannAlgebra_iff_mem_wotClosure T

example (T : UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A) :
    T ∈ envelopingVonNeumannAlgebra (A := A) ↔
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        (UniversalHilbertSpace A) (UniversalHilbertSpace A) T ∈
          closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
            (UniversalHilbertSpace A) (UniversalHilbertSpace A) ''
              Set.range (universalRepresentation (A := A))) :=
  mem_envelopingVonNeumannAlgebra_iff_mem_sotClosure T

/-- The zero algebra case has no added scalar Hilbert space or envelope. -/
example [Subsingleton A] :
    IsEmpty (nonUnitalStateSpace A) ∧ Subsingleton (UniversalHilbertSpace A) ∧
      Subsingleton (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
  ⟨isEmpty_nonUnitalStateSpace_of_subsingleton,
    subsingleton_universalHilbertSpace, subsingleton_envelopingVonNeumannAlgebra⟩

end Ordered

/-- Every nonunital C*-algebra supplies the order used by the state-space
interface via Mathlib's proved spectral-order provider. No extra mathematical
restriction is imposed on the algebra. -/
example (A : Type u) [NonUnitalCStarAlgebra A] (a : A) :
    letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
    letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
    ‖universalRepresentation (A := A) a‖ = ‖a‖ := by
  letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
  exact norm_universalRepresentation a

example (A : Type u) [NonUnitalCStarAlgebra A] :
    letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
    letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
    Function.Injective (envelopingInclusion (A := A)) := by
  letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
  exact envelopingInclusion_injective

end MathlibAnnex.Analysis.CStarAlgebra.EnvelopingConsumers
