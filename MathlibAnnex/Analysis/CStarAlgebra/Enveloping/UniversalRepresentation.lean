/-
Direct-sum action, coordinate intertwining and primitive-separation proof
patterns are adapted from MathlibAnnex/Analysis/CStarAlgebra/Representation/ReducedAtomic.lean
at 5cbbf304e651c6c50163a59ba7f9fcf6c22eca4e.
Original portions: Copyright (c) 2026 Ryotaro Tanaka, Apache 2.0 license.
Modification: the carrier includes every state; the original-algebra cyclicity,
nondegeneracy and coefficient interfaces below do not assume purity.
-/
import Mathlib.Analysis.CStarAlgebra.Hom
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.NonUnitalStateGNS
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.CyclicCoefficient
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Atomic
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.PrimitiveCoordinate
import MathlibAnnex.Analysis.InnerProductSpace.HilbertSumCoordinates

/-!
# The all-state universal representation

The index is the entire existing space of norm-one positive functionals on
the original, possibly nonunital C*-algebra. Each fiber is the existing GNS
space of its canonical state extension to the unitization. The action is
restricted to the original algebra on the same Hilbert space.

First we prove that this restriction is cyclic and nondegenerate for every
state, without purity. The unitization has therefore introduced no scalar
summand on which the original algebra acts trivially. The general dependent
Hilbert-sum construction supplies the direct sum; no new `lp` model is used.

Primitive-kernel separation is used only to prove faithfulness of this
all-state sum. Its carrier and its universal state vectors include every
state, including states whose GNS representation is not irreducible.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra ENNReal lp InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

open MathlibAnnex.Analysis.InnerProductSpace

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

namespace NonUnitalStateGNS

/-- Re-extending the canonical restricted GNS action recovers the original
unital GNS action on exactly the same Hilbert space. -/
theorem unitization_representation (phi : StrongDual ℂ A)
    (hphi : phi ∈ nonUnitalStateSpace A) :
    (representation phi hphi).unitization =
      (positiveLinearMapOfMemStateSpace (unitizationExtension phi)
        (unitizationExtension_mem_stateSpace phi hphi)).gnsStarAlgHom := by
  apply Unitization.starAlgHom_ext
  apply NonUnitalStarAlgHom.ext
  intro a
  exact NonUnitalCStarRepresentation.unitization_inr (representation phi hphi) a

/-- The original-algebra cyclic subspace of a state vector is the whole GNS
space. Norm one, rather than purity, excludes the scalar-character summand. -/
theorem cyclicSubspace_representation_vector_eq_top
    (phi : StrongDual ℂ A) (hphi : phi ∈ nonUnitalStateSpace A) :
    NonUnitalCStarRepresentation.cyclicSubspace (representation phi hphi)
      (vector phi hphi) = ⊤ := by
  let pi := representation phi hphi
  let xi := vector phi hphi
  let M := NonUnitalCStarRepresentation.cyclicSubspace pi xi
  have hxi : ‖xi‖ ≤ 1 := (norm_vector phi hphi).le
  have hcoef : ‖NonUnitalCStarRepresentation.matrixCoefficient pi xi xi‖ = 1 := by
    rw [matrixCoefficient_representation phi hphi]
    exact hphi.2
  have hmem : xi ∈ M :=
    (NonUnitalCStarRepresentation.mem_cyclicSubspace_of_norm_matrixCoefficient_eq_one
      pi xi xi hxi hxi hcoef).1
  have hred : pi.unitization.Reduces M :=
    NonUnitalCStarRepresentation.reduces_unitization_of_reduces pi M
      (NonUnitalCStarRepresentation.reduces_cyclicSubspace pi xi)
  have hdense : DenseRange (fun z : Unitization ℂ A => pi.unitization z xi) := by
    dsimp only [pi, xi]
    rw [unitization_representation]
    exact denseRange_gnsStarAlgHom_stateGNSVector (unitizationExtension phi)
      (unitizationExtension_mem_stateSpace phi hphi)
  apply top_unique
  intro y _hy
  exact hdense.induction_on y hred.1 (fun z => (hred.2 z xi hmem).1)

/-- Every state's vector is cyclic for the original algebra, with no purity
or separability assumption. -/
theorem denseRange_representation_vector
    (phi : StrongDual ℂ A) (hphi : phi ∈ nonUnitalStateSpace A) :
    DenseRange (fun a : A => representation phi hphi a (vector phi hphi)) := by
  change Dense (Set.range (fun a : A => representation phi hphi a (vector phi hphi)))
  rw [dense_iff_closure_eq]
  change (NonUnitalCStarRepresentation.cyclicSubspace
    (representation phi hphi) (vector phi hphi) : Set (Space phi hphi)) = Set.univ
  exact congrArg (fun M : Submodule ℂ (Space phi hphi) => (M : Set (Space phi hphi)))
    (cyclicSubspace_representation_vector_eq_top phi hphi)

/-- The state GNS restriction has no nonzero vector annihilated by the
original algebra. In particular it has no unitization-only scalar part. -/
theorem isNondegenerate_representation
    (phi : StrongDual ℂ A) (hphi : phi ∈ nonUnitalStateSpace A) :
    (representation phi hphi).IsNondegenerate := by
  intro x hx
  have hinner (a : A) :
      inner ℂ (representation phi hphi a (vector phi hphi)) x = 0 := by
    calc
      inner ℂ (representation phi hphi a (vector phi hphi)) x =
          inner ℂ (vector phi hphi) (representation phi hphi (star a) x) := by
        rw [map_star, ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_right]
      _ = 0 := by rw [hx (star a), inner_zero_right]
  have hall (y : Space phi hphi) : inner ℂ y x = 0 :=
    (denseRange_representation_vector phi hphi).induction_on y
      (isClosed_eq (by fun_prop) continuous_const) hinner
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp (hall x)

end NonUnitalStateGNS

/-- The completed dependent Hilbert sum over ALL norm-one positive
functionals of the original algebra. An empty state space gives a zero sum. -/
abbrev UniversalHilbertSpace (A : Type u) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :=
  HilbertSum (fun phi : nonUnitalStateSpace A =>
    NonUnitalStateGNS.Space phi.val phi.property)

/-- The all-state universal representation of an arbitrary nonunital
complex C*-algebra, built with the existing dependent direct-sum action. -/
def universalRepresentation : NonUnitalCStarRepresentation A (UniversalHilbertSpace A) :=
  (atomicRepresentation (fun phi : nonUnitalStateSpace A =>
    (NonUnitalStateGNS.representation phi.val phi.property).unitization)).toNonUnitalStarAlgHom.comp
      (Unitization.inrNonUnitalStarAlgHom ℂ A)

@[simp]
theorem universalRepresentation_apply (a : A) (x : UniversalHilbertSpace A)
    (phi : nonUnitalStateSpace A) :
    universalRepresentation a x phi =
      NonUnitalStateGNS.representation phi.val phi.property a (x phi) := by
  exact NonUnitalCStarRepresentation.unitization_inr_apply _ a (x phi)

/-- Include the actual GNS space of a displayed state as one coordinate. -/
def universalStateEmbedding (phi : nonUnitalStateSpace A) :
    NonUnitalStateGNS.Space phi.val phi.property →L[ℂ] UniversalHilbertSpace A := by
  classical
  exact coordinateEmbedding (H := (fun ψ : nonUnitalStateSpace A => NonUnitalStateGNS.Space ψ.val ψ.property)) phi

/-- Compression to the actual GNS coordinate of a displayed state. -/
def universalStateProjection (phi : nonUnitalStateSpace A) :
    UniversalHilbertSpace A →L[ℂ] NonUnitalStateGNS.Space phi.val phi.property := by
  classical
  exact coordinateProjection phi

@[simp]
theorem universalStateProjection_apply (phi : nonUnitalStateSpace A)
    (x : UniversalHilbertSpace A) : universalStateProjection phi x = x phi := rfl

@[simp]
theorem universalStateProjection_embedding (phi : nonUnitalStateSpace A)
    (x : NonUnitalStateGNS.Space phi.val phi.property) :
    universalStateProjection phi (universalStateEmbedding phi x) = x := by
  classical
  simp [universalStateProjection, universalStateEmbedding, coordinateProjection_apply,
    coordinateEmbedding_apply, lp.coeFn_single]

@[simp]
theorem norm_universalStateEmbedding (phi : nonUnitalStateSpace A)
    (x : NonUnitalStateGNS.Space phi.val phi.property) :
    ‖universalStateEmbedding phi x‖ = ‖x‖ := by
  classical
  exact norm_coordinateEmbedding (H := (fun ψ : nonUnitalStateSpace A => NonUnitalStateGNS.Space ψ.val ψ.property)) phi x

/-- The displayed state coordinate preserves the inner product. -/
@[simp]
theorem inner_universalStateEmbedding (phi : nonUnitalStateSpace A)
    (x y : NonUnitalStateGNS.Space phi.val phi.property) :
    inner ℂ (universalStateEmbedding phi x) (universalStateEmbedding phi y) =
      inner ℂ x y := by
  classical
  change inner ℂ (lp.single (E := (fun ψ : nonUnitalStateSpace A => NonUnitalStateGNS.Space ψ.val ψ.property)) 2 phi x) (lp.single (E := (fun ψ : nonUnitalStateSpace A => NonUnitalStateGNS.Space ψ.val ψ.property)) 2 phi y) = inner ℂ x y
  rw [lp.inner_single_left]
  simp only [lp.coeFn_single, Pi.single_eq_same]

/-- Each GNS coordinate is an invariant isometric copy of the full state
representation, not merely a copy of its functional kernel. -/
@[simp]
theorem universalRepresentation_embedding (a : A) (phi : nonUnitalStateSpace A)
    (x : NonUnitalStateGNS.Space phi.val phi.property) :
    universalRepresentation a (universalStateEmbedding phi x) =
      universalStateEmbedding phi
        (NonUnitalStateGNS.representation phi.val phi.property a x) := by
  classical
  apply lp.ext
  funext psi
  by_cases hpsi : psi = phi
  · subst psi
    simp [universalRepresentation_apply, universalStateEmbedding,
      coordinateEmbedding_apply, lp.coeFn_single]
  · simp [universalRepresentation_apply, universalStateEmbedding,
      coordinateEmbedding_apply, lp.coeFn_single, hpsi, Ne.symm hpsi]

/-- Evaluation commutes with the all-state action. -/
@[simp]
theorem universalStateProjection_representation (a : A)
    (phi : nonUnitalStateSpace A) (x : UniversalHilbertSpace A) :
    universalStateProjection phi (universalRepresentation a x) =
      NonUnitalStateGNS.representation phi.val phi.property a
        (universalStateProjection phi x) := by
  simp only [universalStateProjection_apply, universalRepresentation_apply]

/-- Every coefficient of a displayed state's actual GNS representation is
the same coefficient in its universal coordinate. -/
theorem matrixCoefficient_universalStateEmbedding (phi : nonUnitalStateSpace A)
    (x y : NonUnitalStateGNS.Space phi.val phi.property) :
    NonUnitalCStarRepresentation.matrixCoefficient (universalRepresentation (A := A))
      (universalStateEmbedding phi x) (universalStateEmbedding phi y) =
    NonUnitalCStarRepresentation.matrixCoefficient
      (NonUnitalStateGNS.representation phi.val phi.property) x y := by
  ext a
  simp only [NonUnitalCStarRepresentation.matrixCoefficient_apply,
    universalRepresentation_embedding, inner_universalStateEmbedding]

/-- The unit vector representing a displayed state inside the universal sum. -/
def universalStateVector (phi : nonUnitalStateSpace A) : UniversalHilbertSpace A :=
  universalStateEmbedding phi (NonUnitalStateGNS.vector phi.val phi.property)

@[simp]
theorem norm_universalStateVector (phi : nonUnitalStateSpace A) :
    ‖universalStateVector phi‖ = 1 := by
  rw [universalStateVector, norm_universalStateEmbedding, NonUnitalStateGNS.norm_vector]

/-- Exact scalar recovery for every state in its own universal coordinate. -/
theorem matrixCoefficient_universalStateVector (phi : nonUnitalStateSpace A) :
    NonUnitalCStarRepresentation.matrixCoefficient (universalRepresentation (A := A))
      (universalStateVector phi) (universalStateVector phi) = phi.val := by
  rw [universalStateVector, matrixCoefficient_universalStateEmbedding]
  exact NonUnitalStateGNS.matrixCoefficient_representation phi.val phi.property

/-- The universal action is contractive before faithfulness is used. -/
theorem norm_universalRepresentation_le (a : A) :
    ‖universalRepresentation (A := A) a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le (universalRepresentation (A := A)) a

/-- Nondegeneracy holds coordinate by coordinate for the entire all-state
sum, including an empty index set. -/
theorem isNondegenerate_universalRepresentation :
    (universalRepresentation (A := A)).IsNondegenerate := by
  intro x hx
  apply lp.ext
  funext phi
  change x phi = 0
  apply NonUnitalStateGNS.isNondegenerate_representation phi.val phi.property
  intro a
  have ha := congrArg (fun y : UniversalHilbertSpace A => y phi) (hx a)
  simpa only [universalRepresentation_apply, lp.coeFn_zero, Pi.zero_apply] using ha

/-- All-state faithfulness follows from primitive-kernel separation because
each chosen pure GNS coordinate is one of the all-state coordinates. -/
theorem universalRepresentation_injective :
    Function.Injective (universalRepresentation (A := A)) := by
  classical
  intro a b hab
  apply sub_eq_zero.mp
  have hz : universalRepresentation (A := A) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hcomponent (phi : nonUnitalStateSpace A) :
      NonUnitalStateGNS.representation phi.val phi.property (a - b) = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    have h := congrArg
      (fun T : UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A =>
        universalStateProjection phi (T (universalStateEmbedding phi x))) hz
    simpa only [universalStateProjection_representation, universalStateProjection_embedding,
      ContinuousLinearMap.zero_apply, map_zero] using h
  have hall : a - b ∈ PrimitiveSpectrum.kernelIntersection
      (Set.univ : Set (PrimitiveSpectrum A)) := by
    rw [PrimitiveSpectrum.mem_kernelIntersection]
    intro P _hP
    rw [← P.coe_toTwoSidedIdeal, ← P.kernelIdeal_pureStateRepresentative]
    apply (NonUnitalCStarRepresentation.mem_kernelIdeal
      P.pureStateRepresentative.gnsRepresentation (a - b)).2
    exact hcomponent ⟨P.pureStateRepresentative.val, P.pureStateRepresentative.property.1⟩
  rw [PrimitiveSpectrum.kernelIntersection_univ_eq_bot, TwoSidedIdeal.mem_bot] at hall
  exact hall

/-- The universal representation preserves the original C*-norm. -/
theorem isometry_universalRepresentation : Isometry (universalRepresentation (A := A)) :=
  NonUnitalStarAlgHom.isometry (universalRepresentation (A := A))
    universalRepresentation_injective

@[simp]
theorem norm_universalRepresentation (a : A) :
    ‖universalRepresentation (A := A) a‖ = ‖a‖ := by
  simpa only [map_zero, dist_zero_right] using
    (isometry_universalRepresentation (A := A)).dist_eq a 0

/-- A zero algebra has no norm-one positive functional. -/
theorem isEmpty_nonUnitalStateSpace_of_subsingleton [Subsingleton A] :
    IsEmpty (nonUnitalStateSpace A) := by
  refine ⟨fun phi => ?_⟩
  have hz : phi.val = 0 := by
    ext a
    simp [Subsingleton.elim a 0]
  have hn := phi.property.2
  rw [hz, norm_zero] at hn
  exact zero_ne_one hn

/-- The universal Hilbert space of a zero algebra is zero; no extraneous
one-dimensional scalar summand is adjoined. -/
theorem subsingleton_universalHilbertSpace [Subsingleton A] :
    Subsingleton (UniversalHilbertSpace A) := by
  letI : IsEmpty (nonUnitalStateSpace A) := isEmpty_nonUnitalStateSpace_of_subsingleton
  refine ⟨fun x y => ?_⟩
  apply lp.ext
  funext phi
  exact isEmptyElim phi

end MathlibAnnex.Analysis.CStarAlgebra
