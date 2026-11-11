/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.CStarAlgebra.TypeI.Basic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactRange
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactOperators
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactIntersection
import MathlibAnnex.Analysis.CStarAlgebra.Representation.FiniteDimensionalCompact
import MathlibAnnex.Analysis.CStarAlgebra.Representation.NonUnital
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.SurjectiveRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.Image
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.ImageRepresentation

/-!
# Representation-side GCR transport and quotient permanence

The small pure-GNS definition is transported to an independently specified
Hilbert universe by an actual unitary intertwiner. Surjective pullback then
proves permanence without changing the represented Hilbert space or replacing
the algebraic image by its weak closure.

The kernel quotient and the literal closed range use the existing quotient
construction and inherited norms. The compact-operator example includes the
zero Hilbert space and does not introduce a unit into the compact algebra.

Minimal unitization is handled in both directions. The scalar branch is
separated from a nonzero original-algebra action, and the reverse direction
constructs a nonzero compact in the original represented image.
-/

set_option autoImplicit false
noncomputable section

open Set InnerProductSpace
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every nonzero irreducible representation of a GCR algebra contains all
compact operators, even when its Hilbert universe is independent of `A`. -/
theorem IsGCR.compact_le_range (hA : IsGCR A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤
      NonUnitalStarAlgHom.range pi := by
  obtain ⟨phi, hU⟩ := pi.exists_pureState_unitaryEquivalent_gnsRepresentation hpi
  exact hU.symm.compactOperatorStarSubalgebra_le_range (hA phi)

/-- The small test can equivalently quantify over all Hilbert spaces in the
algebra universe. The preceding theorem separately supplies arbitrary universes. -/
theorem isGCR_iff_forall_irreducible :
    IsGCR A ↔
      ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
        ∀ pi : NonUnitalCStarRepresentation A K, pi.IsIrreducible →
          ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K ≤
            NonUnitalStarAlgHom.range pi := by
  constructor
  · intro hA K _ _ _ pi hpi
    exact hA.compact_le_range pi hpi
  · intro h phi
    exact h phi.GNS phi.gnsRepresentation phi.isIrreducible_gnsRepresentation

/-- Finite-dimensionality of the algebra makes each actual pure-state GNS
space finite-dimensional, so exact interpolation gives every compact preimage. -/
theorem isGCR_of_finiteDimensional [FiniteDimensional ℂ A] : IsGCR A := by
  intro phi
  letI : FiniteDimensional ℂ phi.GNS := phi.finiteDimensional_gns
  intro T _hT
  exact (NonUnitalStarAlgHom.mem_range phi.gnsRepresentation).2
    (NonUnitalCStarRepresentation.surjective_of_isIrreducible_of_finiteDimensional
      phi.gnsRepresentation phi.isIrreducible_gnsRepresentation T)

/-- If the unitization of an irreducible representation contains all compacts,
then its original nonunital image does too. A nonzero represented operator
multiplied by a suitable rank-one operator gives an actual compact element of
the original image. Compact-intersection simplicity then supplies all compacts. -/
theorem NonUnitalCStarRepresentation.compact_le_range_of_unitization
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hcompact : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤
      NonUnitalStarAlgHom.range pi.unitization.toNonUnitalStarAlgHom) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤
      NonUnitalStarAlgHom.range pi := by
  classical
  obtain ⟨a, ha⟩ := hpi.1
  obtain ⟨x, hx⟩ : ∃ x : H, pi a x ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (ContinuousLinearMap.ext h)
  have hx0 : x ≠ 0 := by
    intro hx0
    exact hx (by rw [hx0, map_zero])
  obtain ⟨z, hz⟩ := (NonUnitalStarAlgHom.mem_range
    pi.unitization.toNonUnitalStarAlgHom).1
      (hcompact (isCompactOperator_rankOne x x))
  have hinr : (Unitization.inr a : Unitization ℂ A) * z =
      Unitization.inr (z.fst • a + a * z.snd) := by
    calc
      (Unitization.inr a : Unitization ℂ A) * z =
          Unitization.inr a * (Unitization.inl z.fst + Unitization.inr z.snd) :=
        congrArg (fun q : Unitization ℂ A => Unitization.inr a * q)
          (Unitization.inl_fst_add_inr_snd_eq z).symm
      _ = Unitization.inr (z.fst • a + a * z.snd) := by
        rw [mul_add, Unitization.inr_mul_inl,
          ← Unitization.inr_mul, ← Unitization.inr_add]
  have hproduct : pi (z.fst • a + a * z.snd) = pi a * rankOne ℂ x x := by
    calc
      pi (z.fst • a + a * z.snd) =
          pi.unitization (Unitization.inr (z.fst • a + a * z.snd)) :=
        (pi.unitization_inr _).symm
      _ = pi.unitization ((Unitization.inr a : Unitization ℂ A) * z) := by
        rw [hinr]
      _ = pi a * rankOne ℂ x x := by
        rw [map_mul, pi.unitization_inr]
        exact congrArg (fun T : H →L[ℂ] H => pi a * T) hz
  have hnonzero : pi a * rankOne ℂ x x ≠ 0 := by
    change pi a ∘L rankOne ℂ x x ≠ 0
    rw [comp_rankOne]
    exact rankOne_ne_zero (𝕜 := ℂ) hx hx0
  apply compactOperatorStarSubalgebra_le_of_exists_nonzero_compact
    (NonUnitalStarAlgHom.range pi) (HomKernelQuotient.isClosed_image pi)
    ((NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff pi).2 hpi)
  refine ⟨pi a * rankOne ℂ x x, ?_, ?_, hnonzero⟩
  · exact (NonUnitalStarAlgHom.mem_range pi).2
      ⟨z.fst • a + a * z.snd, hproduct⟩
  · exact (isCompactOperator_rankOne x x).clm_comp (pi a)

/-- GCR is preserved by minimal unitization. A representation which vanishes
on the original algebra factors through the one-dimensional scalar algebra;
every other irreducible representation restricts irreducibly to the algebra. -/
theorem IsGCR.unitization (hA : IsGCR A) : IsGCR (Unitization ℂ A) := by
  classical
  intro phi
  let rho : Representation (Unitization ℂ A) phi.GNS :=
    NonUnitalRepresentation.toUnital phi.gnsRepresentation
      phi.isIrreducible_gnsRepresentation
  have hrho : rho.IsIrreducible :=
    NonUnitalRepresentation.isIrreducible_toUnital phi.gnsRepresentation
      phi.isIrreducible_gnsRepresentation
  let pi : NonUnitalCStarRepresentation A phi.GNS :=
    rho.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  by_cases hnz : pi.IsNonzero
  · have hpi : pi.IsIrreducible :=
      NonUnitalCStarRepresentation.isIrreducible_restriction_of_isIrreducible_unitization
        rho hrho hnz
    intro T hT
    obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range pi).1
      (hA.compact_le_range pi hpi hT)
    exact (NonUnitalStarAlgHom.mem_range phi.gnsRepresentation).2
      ⟨Unitization.inr a, ha⟩
  · have hzero (a : A) : rho (Unitization.inr a) = 0 := by
      by_contra ha
      exact hnz ⟨a, ha⟩
    let sigma : NonUnitalCStarRepresentation ℂ phi.GNS :=
      rho.toNonUnitalStarAlgHom.comp
        (StarAlgHom.ofId ℂ (Unitization ℂ A)).toNonUnitalStarAlgHom
    have heq (z : Unitization ℂ A) : rho z = sigma z.fst := by
      calc
        rho z = rho (Unitization.inl z.fst + Unitization.inr z.snd) :=
          congrArg rho (Unitization.inl_fst_add_inr_snd_eq z).symm
        _ = rho (Unitization.inl z.fst) := by rw [map_add, hzero, add_zero]
        _ = sigma z.fst := rfl
    have hsigma : sigma.IsIrreducible := by
      refine ⟨?_, ?_⟩
      · obtain ⟨z, hz⟩ := hrho.1
        exact ⟨z.fst, by rwa [heq z] at hz⟩
      · intro L hL
        apply hrho.2 L
        refine ⟨hL.1, ?_⟩
        intro z x hx
        rw [heq z]
        exact hL.2 z.fst x hx
    have hscalar : IsGCR ℂ := isGCR_of_finiteDimensional
    intro T hT
    obtain ⟨c, hc⟩ := (NonUnitalStarAlgHom.mem_range sigma).1
      (hscalar.compact_le_range sigma hsigma hT)
    exact (NonUnitalStarAlgHom.mem_range phi.gnsRepresentation).2
      ⟨Unitization.inl c, hc⟩

/-- Removing the adjoined unit preserves GCR, using the actual compact
intersection of each original irreducible image. -/
theorem isGCR_of_unitization (hU : IsGCR (Unitization ℂ A)) : IsGCR A := by
  intro phi
  have hpi : NonUnitalCStarRepresentation.IsIrreducible phi.gnsRepresentation.unitization.toNonUnitalStarAlgHom :=
    phi.gnsRepresentation.isIrreducible_unitization phi.isIrreducible_gnsRepresentation
  exact phi.gnsRepresentation.compact_le_range_of_unitization
    phi.isIrreducible_gnsRepresentation
    (hU.compact_le_range phi.gnsRepresentation.unitization.toNonUnitalStarAlgHom hpi)

/-- The original nonunital algebra is GCR exactly when its minimal unitization
is GCR. Neither direction uses closed-subalgebra permanence as an assumption. -/
theorem isGCR_unitization_iff : IsGCR (Unitization ℂ A) ↔ IsGCR A :=
  ⟨isGCR_of_unitization, IsGCR.unitization⟩

/-- GCR passes through every surjective nonunital complex star homomorphism.
The compact operator is lifted through the same represented range. -/
theorem IsGCR.of_surjective (hA : IsGCR A)
    (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q) : IsGCR B := by
  intro phi
  have hpull : NonUnitalCStarRepresentation.IsIrreducible (phi.gnsRepresentation.comp q) :=
    (NonUnitalCStarRepresentation.isIrreducible_comp_iff_of_surjective
      phi.gnsRepresentation q hq).2 phi.isIrreducible_gnsRepresentation
  have hcompact := hA.compact_le_range (phi.gnsRepresentation.comp q) hpull
  intro T hT
  obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range
    (phi.gnsRepresentation.comp q)).1 (hcompact hT)
  exact (NonUnitalStarAlgHom.mem_range phi.gnsRepresentation).2 ⟨q a, ha⟩

/-- The predicate is invariant under an actual complex star-algebra equivalence. -/
theorem isGCR_iff_of_starAlgEquiv (e : A ≃⋆ₐ[ℂ] B) : IsGCR A ↔ IsGCR B := by
  constructor
  · intro hA
    exact hA.of_surjective e.toNonUnitalStarAlgHom e.surjective
  · intro hB
    exact hB.of_surjective e.symm.toNonUnitalStarAlgHom e.symm.surjective

/-- Permanence for the existing complete C-star quotient by a homomorphism
kernel, using its actual surjective quotient map. -/
theorem IsGCR.hom_kernel_quotient (hA : IsGCR A) (q : A →⋆ₙₐ[ℂ] B) :
    IsGCR (HomKernelQuotient q) :=
  hA.of_surjective (HomKernelQuotient.mkHom q) (HomKernelQuotient.mkHom_surjective q)

/-- GCR passes to the actual complete C-star quotient by every norm-closed
two-sided ideal, including the zero quotient. -/
theorem IsGCR.closed_ideal_quotient (hA : IsGCR A) (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) : IsGCR (ClosedIdealQuotient.Quotient J hJ) :=
  hA.of_surjective (ClosedIdealQuotient.mkHom J hJ)
    (ClosedIdealQuotient.mkHom_surjective J hJ)

/-- Permanence for the actual closed image with its original subspace norm. -/
theorem IsGCR.range (hA : IsGCR A) (q : A →⋆ₙₐ[ℂ] B) :
    letI := HomKernelQuotient.imageCStarAlgebra q
    IsGCR (NonUnitalStarAlgHom.range q) := by
  letI := HomKernelQuotient.imageCStarAlgebra q
  apply hA.of_surjective (NonUnitalStarAlgHom.rangeRestrict q)
  intro b
  obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range q).1 b.property
  exact ⟨a, Subtype.ext ha⟩

/-- The compact containment conclusion supplies an actual nonzero compact
image of an element of the original algebra. -/
theorem IsGCR.exists_nonzero_compact_image (hA : IsGCR A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    ∃ a : A, pi a ≠ 0 ∧ IsCompactOperator (pi a) := by
  letI : Nontrivial H := pi.nontrivial_of_isNonzero hpi.1
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hcompact : IsCompactOperator (rankOne ℂ x x) := isCompactOperator_rankOne x x
  obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range pi).1
    (hA.compact_le_range pi hpi hcompact)
  refine ⟨a, ?_, ?_⟩
  · rw [ha]
    exact rankOne_ne_zero (𝕜 := ℂ) hx hx
  · rw [ha]
    exact hcompact

/-- A displayed compact-free nonzero irreducible representation obstructs GCR.
The hypothesis is about actual represented operators. -/
theorem not_isGCR_of_compact_free_irreducible
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hzero : ∀ a : A, IsCompactOperator (pi a) → pi a = 0) : ¬ IsGCR A := by
  intro hA
  obtain ⟨a, ha, hcompact⟩ := hA.exists_nonzero_compact_image pi hpi
  exact ha (hzero a hcompact)

set_option maxHeartbeats 1200000 in
/-- The concrete compact operators are GCR on an arbitrary Hilbert space.
The zero-space case is handled by the nonzero condition in irreducibility. -/
theorem isGCR_compactOperatorStarSubalgebra
    (K : Type v) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] :
    IsGCR (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K) := by
  letI := _root_.CStarAlgebra.spectralOrder (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K)
  letI := _root_.CStarAlgebra.spectralOrderedRing (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K)
  intro phi
  have hK : ¬ Subsingleton K := by
    intro hsub
    letI : Subsingleton K := hsub
    obtain ⟨a, ha⟩ := phi.isIrreducible_gnsRepresentation.1
    have ha0 : a = 0 := Subtype.ext (Subsingleton.elim _ _)
    exact ha (by rw [ha0, map_zero])
  letI : Nontrivial K := not_subsingleton_iff_nontrivial.mp hK
  have hU := unitaryEquivalent_compactOperatorRepresentation
    phi.gnsRepresentation phi.isIrreducible_gnsRepresentation
  apply hU.compactOperatorStarSubalgebra_le_range
  intro T hT
  exact (NonUnitalStarAlgHom.mem_range (compactOperatorRepresentation K)).2
    ⟨⟨T, hT⟩, rfl⟩

end MathlibAnnex.Analysis.CStarAlgebra
