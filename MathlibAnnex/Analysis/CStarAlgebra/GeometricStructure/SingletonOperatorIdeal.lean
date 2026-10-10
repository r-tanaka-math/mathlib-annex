/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartUnitaryInvariance
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorAlgebra
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import MathlibAnnex.Analysis.CStarAlgebra.OperatorSubalgebraIdeal

/-!
# The operator ideal of the same singleton representation image

A literal non-unital star subalgebra with both multiplier absorption laws is
bundled as a `TwoSidedIdeal`, with no change to its carrier or ambient norm.
For a nonzero closed image, the already proved least-ideal theorem supplies
all compact operators. The final theorem uses the very pure-state witness
returned by the finite-conjugation construction, rather than choosing a new
representation. No reverse compact inclusion or quotient representation is
assumed or claimed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Representation

variable {A : Type u} [NonUnitalCStarAlgebra A]

variable [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

/-- The R21 pure-state witness, unchanged, now comes with a literal nonzero
closed operator ideal and all compact preimages. Its old normal-part
homeomorphism still has the same range-restriction preimage formula. -/
theorem exists_faithful_image_operatorIdeal_of_singleton
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (hproperty : ∃ I : NormedSpace.GeometricStructureSpace ℂ A,
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I)).HasContinuousFiniteConjugation
          (ClosureCat.IsCStarRealizable.{u, max u w})) :
    ∃ phi : NonUnitalPureState A,
      Function.Injective phi.gnsRepresentation ∧
      normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation) = Set.univ ∧
      ∃ r : ClosureSpace.Homeomorph
          ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range phi.gnsRepresentation)).subspace
            (normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation)))
          (NormedSpace.geometricStructureClosure ℂ A),
        (∀ J : normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation),
          (r.toEquiv J).val = (NonUnitalStarAlgHom.rangeRestrict phi.gnsRepresentation) ⁻¹' J.val.val) ∧
        ∃ I : TwoSidedIdeal (phi.GNS →L[ℂ] phi.GNS),
          (I : Set (phi.GNS →L[ℂ] phi.GNS)) = (NonUnitalStarAlgHom.range phi.gnsRepresentation) ∧
          I ≠ ⊥ ∧ IsClosed (I : Set (phi.GNS →L[ℂ] phi.GNS)) ∧
          ContinuousLinearMap.compactOperatorIdeal ℂ phi.GNS ≤ I ∧
          (∀ (b a : phi.GNS →L[ℂ] phi.GNS), a ∈ (NonUnitalStarAlgHom.range phi.gnsRepresentation) →
            b * a ∈ (NonUnitalStarAlgHom.range phi.gnsRepresentation) ∧ a * b ∈ (NonUnitalStarAlgHom.range phi.gnsRepresentation)) ∧
          (∀ T : phi.GNS →L[ℂ] phi.GNS, IsCompactOperator T →
            ∃ a : A, phi.gnsRepresentation a = T) := by
  obtain ⟨phi, hfaith, hnormal, r, hr, _hunitary, hmul⟩ :=
    exists_faithful_image_unitary_invariant_of_singleton.{u, w} hsingle hproperty
  let I := operatorIdealOfMulMem (NonUnitalStarAlgHom.range phi.gnsRepresentation) hmul
  have hclosed : IsClosed ((NonUnitalStarAlgHom.range phi.gnsRepresentation) :
      Set (phi.GNS →L[ℂ] phi.GNS)) := by
    change IsClosed (Set.range phi.gnsRepresentation)
    exact (NonUnitalStarAlgHom.isometry phi.gnsRepresentation hfaith).isClosedEmbedding.isClosed_range
  have hnz : ∃ a : phi.GNS →L[ℂ] phi.GNS,
      a ∈ (NonUnitalStarAlgHom.range phi.gnsRepresentation) ∧ a ≠ 0 := by
    obtain ⟨a, ha⟩ := phi.isIrreducible_gnsRepresentation.1
    exact ⟨phi.gnsRepresentation a,
      (NonUnitalStarAlgHom.mem_range phi.gnsRepresentation).2 ⟨a, rfl⟩, ha⟩
  have hI : I ≠ ⊥ := operatorIdealOfMulMem_ne_bot _ hmul hnz
  have hIc : IsClosed (I : Set (phi.GNS →L[ℂ] phi.GNS)) :=
    isClosed_operatorIdealOfMulMem _ hmul hclosed
  refine ⟨phi, hfaith, hnormal, r, hr, I,
    coe_operatorIdealOfMulMem _ hmul, hI, hIc,
    I.compactOperatorIdeal_le hI hIc, hmul, ?_⟩
  exact exists_preimage_compact_of_image_mul_mem phi.gnsRepresentation hfaith
    phi.isIrreducible_gnsRepresentation.1 hmul

end Representation
end MathlibAnnex.Analysis.CStarAlgebra
