/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartHomeomorph
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.SpectralComparison

/-!
# Closed components and full normal parts of representation images

The two image homeomorphisms act by the SAME inverse-image map. The full
image GSS maps onto the closure of a coefficient component, whereas its
normal part maps onto the component itself. Comparing these sets proves
Theorem 7.1 without equating functionals whose kernels happen to agree.

All representations are genuine nonzero irreducible representations. The
transfer statement allows independently quantified Hilbert universes; only
the explicit all/some-representatives statements use the small GNS list.
No statement identifies unitary equivalence from representation kernels.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] HomKernelQuotient.imageCStarAlgebra HomKernelQuotient.isClosed_image

open NonUnitalCStarRepresentation

/-- The normal-part map is the restriction of the full image-GSS map,
after forgetting the two different target subtypes. -/
theorem imageNormalPartHomeomorph_eq_coefficientImageGeometricStructureHomeomorph
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) (J : normalPart (NonUnitalStarAlgHom.range pi)) :
    ((imageNormalPartHomeomorph pi hpi x y hx hy).toEquiv J).val =
      ((coefficientImageGeometricStructureHomeomorph pi hpi x y hx hy).toEquiv J.val).val := by
  apply Subtype.ext
  rfl

/-- Membership in the normal part is reflected by the actual full-image map.
This is a point statement, not an assertion about a representative functional. -/
theorem mem_normalPart_iff_image_mem_component
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0)
    (J : NormedSpace.GeometricStructureSpace ℂ (NonUnitalStarAlgHom.range pi)) :
    J ∈ normalPart (NonUnitalStarAlgHom.range pi) ↔
      ((coefficientImageGeometricStructureHomeomorph pi hpi x y hx hy).toEquiv J).val ∈
        (NormedSpace.geometricStructureClosure ℂ A).component
          (matrixCoefficientKernel pi hpi x y hx hy) := by
  let h := coefficientImageGeometricStructureHomeomorph pi hpi x y hx hy
  have hinj : Function.Injective (fun L => (h.toEquiv L).val) := by
    intro L M heq
    exact h.toEquiv.injective (Subtype.ext heq)
  have hrange := image_normalPart_eq_component pi hpi x y hx hy
  constructor
  · intro hJ
    exact (Set.ext_iff.mp hrange _).1 ⟨J, hJ, rfl⟩
  · intro hJ
    have hJ' := (Set.ext_iff.mp hrange _).2 hJ
    obtain ⟨L, hL, hLJ⟩ := hJ'
    exact hinj hLJ ▸ hL

/-- The ambient range of the full-image homeomorphism is exactly the
component closure, not necessarily the component. -/
theorem range_coefficientImageGeometricStructureHomeomorph
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    Set.range (fun J : NormedSpace.GeometricStructureSpace ℂ (NonUnitalStarAlgHom.range pi) =>
      ((coefficientImageGeometricStructureHomeomorph pi hpi x y hx hy).toEquiv J).val) =
        (NormedSpace.geometricStructureClosure ℂ A).closure
          ((NormedSpace.geometricStructureClosure ℂ A).component
            (matrixCoefficientKernel pi hpi x y hx hy)) := by
  let h := coefficientImageGeometricStructureHomeomorph pi hpi x y hx hy
  ext I
  constructor
  · rintro ⟨J, rfl⟩
    exact (h.toEquiv J).property
  · intro hI
    exact ⟨h.toEquiv.symm ⟨I, hI⟩,
      congrArg Subtype.val (h.toEquiv.apply_symm_apply ⟨I, hI⟩)⟩

/-- Theorem 7.1 for an actual coefficient seed in an arbitrary Hilbert universe. -/
theorem isClosed_component_matrixCoefficientKernel_iff_normalPart_eq_univ
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (NormedSpace.geometricStructureClosure ℂ A).IsClosed
      ((NormedSpace.geometricStructureClosure ℂ A).component
        (matrixCoefficientKernel pi hpi x y hx hy)) ↔ normalPart (NonUnitalStarAlgHom.range pi) = Set.univ := by
  let c := NormedSpace.geometricStructureClosure ℂ A
  let I := matrixCoefficientKernel pi hpi x y hx hy
  let h := coefficientImageGeometricStructureHomeomorph pi hpi x y hx hy
  rw [c.isClosed_iff_closure_subset]
  constructor
  · intro hclosed
    apply Set.eq_univ_iff_forall.mpr
    intro J
    exact (mem_normalPart_iff_image_mem_component pi hpi x y hx hy J).2
      (hclosed (h.toEquiv J).property)
  · intro hnormal J hJ
    let L := h.toEquiv.symm ⟨J, hJ⟩
    have hL : L ∈ normalPart (NonUnitalStarAlgHom.range pi) := by rw [hnormal]; trivial
    have hm := (mem_normalPart_iff_image_mem_component pi hpi x y hx hy L).1 hL
    change (h.toEquiv L).val ∈ c.component I at hm
    have heq : (h.toEquiv L).val = J :=
      congrArg Subtype.val (h.toEquiv.apply_symm_apply ⟨J, hJ⟩)
    exact heq ▸ hm

/-- Changing to a genuinely unitarily equivalent action preserves and reflects
full normality. It uses the actual equivalence of coefficient components. -/
theorem normalPart_range_eq_univ_iff_of_unitaryEquivalent
    (pi : NonUnitalCStarRepresentation A H) (sigma : NonUnitalCStarRepresentation A K)
    (hpi : pi.IsIrreducible) (hsigma : sigma.IsIrreducible)
    (h : pi.UnitaryEquivalent sigma) :
    normalPart (NonUnitalStarAlgHom.range pi) = Set.univ ↔ normalPart (NonUnitalStarAlgHom.range sigma) = Set.univ := by
  letI : Nontrivial H := nontrivial_of_isNonzero pi hpi.1
  letI : Nontrivial K := nontrivial_of_isNonzero sigma hsigma.1
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  obtain ⟨z, hz⟩ := exists_ne (0 : K)
  rw [← isClosed_component_matrixCoefficientKernel_iff_normalPart_eq_univ pi hpi x x hx hx,
    ← isClosed_component_matrixCoefficientKernel_iff_normalPart_eq_univ sigma hsigma z z hz hz]
  have hrel := related_matrixCoefficientKernel_of_unitaryEquivalent
    pi sigma hpi hsigma h x x z z hx hx hz hz
  rw [(NormedSpace.geometricStructureClosure ℂ A).component_eq_of_related hrel]

/-- A pure state's ACTUAL GNS representation gives the equivalence of 7.1(i),(ii). -/
theorem isClosed_component_geometricPoint_iff_normalPart_eq_univ (phi : NonUnitalPureState A) :
    (NormedSpace.geometricStructureClosure ℂ A).IsClosed
      ((NormedSpace.geometricStructureClosure ℂ A).component phi.geometricPoint) ↔
        normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation) = Set.univ := by
  rw [phi.geometricPoint_eq_matrixCoefficientKernel]
  exact isClosed_component_matrixCoefficientKernel_iff_normalPart_eq_univ
    phi.gnsRepresentation phi.isIrreducible_gnsRepresentation phi.gnsVector phi.gnsVector
    phi.gnsVector_ne_zero phi.gnsVector_ne_zero

/-- Each representation in the unitary class gives the same criterion,
including representations on a different Hilbert universe. -/
theorem isClosed_component_geometricPoint_iff_of_unitaryEquivalent
    (phi : NonUnitalPureState A) (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsIrreducible) (h : phi.gnsRepresentation.UnitaryEquivalent pi) :
    (NormedSpace.geometricStructureClosure ℂ A).IsClosed
      ((NormedSpace.geometricStructureClosure ℂ A).component phi.geometricPoint) ↔
        normalPart (NonUnitalStarAlgHom.range pi) = Set.univ :=
  (isClosed_component_geometricPoint_iff_normalPart_eq_univ phi).trans
    (normalPart_range_eq_univ_iff_of_unitaryEquivalent
      phi.gnsRepresentation pi phi.isIrreducible_gnsRepresentation hpi h)

/-- The all-representatives version on the small, genuine GNS family.
The preceding arbitrary-universe theorem supplies each external representative. -/
theorem isClosed_component_geometricPoint_iff_forall_equivalent_pureState
    (phi : NonUnitalPureState A) :
    (NormedSpace.geometricStructureClosure ℂ A).IsClosed
      ((NormedSpace.geometricStructureClosure ℂ A).component phi.geometricPoint) ↔
    ∀ psi : NonUnitalPureState A, phi.gnsRepresentation.UnitaryEquivalent psi.gnsRepresentation →
      normalPart (NonUnitalStarAlgHom.range psi.gnsRepresentation) = Set.univ := by
  constructor
  · intro hclosed psi h
    exact (isClosed_component_geometricPoint_iff_of_unitaryEquivalent
      phi psi.gnsRepresentation psi.isIrreducible_gnsRepresentation h).1 hclosed
  · intro hall
    exact (isClosed_component_geometricPoint_iff_normalPart_eq_univ phi).2
      (hall phi (unitaryEquivalent_refl phi.gnsRepresentation))

/-- The some-representative version includes an actual pure state as witness. -/
theorem isClosed_component_geometricPoint_iff_exists_equivalent_pureState
    (phi : NonUnitalPureState A) :
    (NormedSpace.geometricStructureClosure ℂ A).IsClosed
      ((NormedSpace.geometricStructureClosure ℂ A).component phi.geometricPoint) ↔
    ∃ psi : NonUnitalPureState A, phi.gnsRepresentation.UnitaryEquivalent psi.gnsRepresentation ∧
      normalPart (NonUnitalStarAlgHom.range psi.gnsRepresentation) = Set.univ := by
  constructor
  · intro hclosed
    exact ⟨phi, unitaryEquivalent_refl phi.gnsRepresentation,
      (isClosed_component_geometricPoint_iff_normalPart_eq_univ phi).1 hclosed⟩
  · rintro ⟨psi, h, hnormal⟩
    exact (isClosed_component_geometricPoint_iff_of_unitaryEquivalent
      phi psi.gnsRepresentation psi.isIrreducible_gnsRepresentation h).2 hnormal

/-- Corollary 7.2, first using the small family of actual GNS representations.
Every geometric component, not just a dense subfamily, has such a representative. -/
theorem forall_isClosed_component_iff_forall_pureState_normalPart_eq_univ :
    (∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      (NormedSpace.geometricStructureClosure ℂ A).IsClosed
        ((NormedSpace.geometricStructureClosure ℂ A).component I)) ↔
    ∀ phi : NonUnitalPureState A, normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation) = Set.univ := by
  constructor
  · intro hall phi
    exact (isClosed_component_geometricPoint_iff_normalPart_eq_univ phi).1
      (hall phi.geometricPoint)
  · intro hall I
    obtain ⟨phi, hphi⟩ := NonUnitalPureState.toGeometricSpectrum_surjective
      (NormedSpace.toGeometricSpectrum ℂ A I)
    have hcomp : (NormedSpace.geometricStructureClosure ℂ A).component phi.geometricPoint =
        (NormedSpace.geometricStructureClosure ℂ A).component I := congrArg Subtype.val hphi
    rw [← hcomp]
    exact (isClosed_component_geometricPoint_iff_normalPart_eq_univ phi).2 (hall phi)

/-- The small-family condition supplies the result for ANY represented Hilbert
space. The representative theorem constructs a unitary, not only an equal kernel. -/
theorem normalPart_range_eq_univ_of_forall_pureState
    (hall : ∀ phi : NonUnitalPureState A, normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation) = Set.univ)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    normalPart (NonUnitalStarAlgHom.range pi) = Set.univ := by
  obtain ⟨phi, hphi⟩ := exists_pureState_unitaryEquivalent_gnsRepresentation pi hpi
  exact (normalPart_range_eq_univ_iff_of_unitaryEquivalent
    pi phi.gnsRepresentation hpi phi.isIrreducible_gnsRepresentation hphi).2 (hall phi)

/-- Corollary 7.2 in a fixed representative universe. The preceding theorem
extends this condition to each independently quantified Hilbert universe.
No type of representations from all universes is formed. -/
theorem forall_isClosed_component_iff_forall_representation_normalPart_eq_univ :
    (∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      (NormedSpace.geometricStructureClosure ℂ A).IsClosed
        ((NormedSpace.geometricStructureClosure ℂ A).component I)) ↔
    ∀ (H' : Type u) [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      [CompleteSpace H'] (pi : NonUnitalCStarRepresentation A H'),
      pi.IsIrreducible → normalPart (NonUnitalStarAlgHom.range pi) = Set.univ := by
  rw [forall_isClosed_component_iff_forall_pureState_normalPart_eq_univ]
  constructor
  · intro hall H' instN instI instC pi hpi
    exact normalPart_range_eq_univ_of_forall_pureState hall pi hpi
  · intro hall phi
    exact hall phi.GNS phi.gnsRepresentation phi.isIrreducible_gnsRepresentation

/-- Translate `normalPart = univ` to the literal unit-vector kernel FAMILY
in 7.1. The left side is a subset of GSS points; the right side is a family
of subsets of the algebra, so the coercions are deliberately explicit. -/
theorem normalPart_eq_univ_iff_geometricStructureFamily_eq_unit_coefficients
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S)) :
    normalPart S = Set.univ ↔
      NormedSpace.geometricStructureFamily ℂ S =
        {J : Set S | ∃ x y : H, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
          {a : S | inner ℂ y ((a : H →L[ℂ] H) x) = 0} = J} := by
  constructor
  · intro hnormal
    ext J
    constructor
    · intro hJ
      exact (mem_normalPart_iff_exists_unit_vectors S ⟨J, hJ⟩).1 (by
        rw [hnormal]; trivial)
    · rintro ⟨x, y, hx, hy, rfl⟩
      exact setOf_inner_apply_eq_zero_mem_geometricStructureFamily S hS x y
        (norm_ne_zero_iff.mp (by rw [hx]; exact one_ne_zero))
        (norm_ne_zero_iff.mp (by rw [hy]; exact one_ne_zero))
  · intro hfamily
    apply Set.eq_univ_iff_forall.mpr
    intro I
    apply (mem_normalPart_iff_exists_unit_vectors S I).2
    exact (Set.ext_iff.mp hfamily I.val).1 I.property

/-- Theorem 7.1(iii) in a representative universe containing the actual GNS.
The arbitrary-universe transfer theorem above handles each larger or smaller
Hilbert model individually; there is no all-universes representation type. -/
theorem isClosed_component_geometricPoint_iff_forall_equivalent_representation
    (phi : NonUnitalPureState A) :
    (NormedSpace.geometricStructureClosure ℂ A).IsClosed
      ((NormedSpace.geometricStructureClosure ℂ A).component phi.geometricPoint) ↔
    ∀ (H' : Type u) [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      [CompleteSpace H'] (pi : NonUnitalCStarRepresentation A H'),
      pi.IsIrreducible → phi.gnsRepresentation.UnitaryEquivalent pi →
        normalPart (NonUnitalStarAlgHom.range pi) = Set.univ := by
  constructor
  · intro hclosed H' instN instI instC pi hpi h
    exact (isClosed_component_geometricPoint_iff_of_unitaryEquivalent phi pi hpi h).1 hclosed
  · intro hall
    exact (isClosed_component_geometricPoint_iff_normalPart_eq_univ phi).2
      (hall phi.GNS phi.gnsRepresentation phi.isIrreducible_gnsRepresentation
        (unitaryEquivalent_refl phi.gnsRepresentation))

/-- Theorem 7.1(iv), with an actual represented Hilbert space as existential
witness. Local structures ensure that every operation has its intended type. -/
theorem isClosed_component_geometricPoint_iff_exists_equivalent_representation
    (phi : NonUnitalPureState A) :
    (NormedSpace.geometricStructureClosure ℂ A).IsClosed
      ((NormedSpace.geometricStructureClosure ℂ A).component phi.geometricPoint) ↔
    (∃ (H' : Type u) (instN : NormedAddCommGroup H'),
      letI := instN
      ∃ instI : InnerProductSpace ℂ H',
        letI := instI
        ∃ instC : CompleteSpace H',
          letI := instC
          ∃ pi : NonUnitalCStarRepresentation A H', pi.IsIrreducible ∧
            phi.gnsRepresentation.UnitaryEquivalent pi ∧ normalPart (NonUnitalStarAlgHom.range pi) = Set.univ) := by
  constructor
  · intro hclosed
    exact ⟨phi.GNS, inferInstance, inferInstance, inferInstance, phi.gnsRepresentation,
      phi.isIrreducible_gnsRepresentation, unitaryEquivalent_refl phi.gnsRepresentation,
      (isClosed_component_geometricPoint_iff_normalPart_eq_univ phi).1 hclosed⟩
  · rintro ⟨H', instN, h⟩
    letI := instN
    obtain ⟨instI, h⟩ := h
    letI := instI
    obtain ⟨instC, h⟩ := h
    letI := instC
    obtain ⟨pi, hpi, h, hnormal⟩ := h
    exact (isClosed_component_geometricPoint_iff_of_unitaryEquivalent phi pi hpi h).2 hnormal

end MathlibAnnex.Analysis.CStarAlgebra
