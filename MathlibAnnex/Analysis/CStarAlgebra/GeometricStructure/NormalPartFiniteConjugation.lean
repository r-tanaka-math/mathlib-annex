/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CStarFiniteConjugation
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartComponentClosed

/-!
# Finite-conjugation tests on normal parts of actual representation images

The full image GSS identifies with the CLOSURE of a component; its normal part
identifies with the component ITSELF. We use the existing restriction and its
literal preimage formula, not an identification of primitive kernels with
unitary-equivalence classes. The GNS component representative is a genuine
nonzero irreducible representation in the algebra's carrier universe.

Every separately specified Hilbert universe is admitted in the forward theorem.
The converse uses all representations in the algebra universe, which already
contains the actual GNS witnesses. No type of representations over all universes
is formed and no arbitrary large Hilbert space is silently shrunk.

All tests assume only forward full continuity of f and g. This is a test
reduction for Theorem 7.7(ii), not the compact/ideal argument or its conclusion.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uA uH uX uL

attribute [local instance] HomKernelQuotient.imageCStarAlgebra HomKernelQuotient.isClosed_image

/-- Every actual GSS component has a genuine small irreducible-image normal-part
model. The homeomorphism acts by inverse image on the literal kernel sets.
The representation need not be faithful. -/
theorem exists_representation_normalPart_homeomorph_component
    (A : Type uA) [NonUnitalCStarAlgebra A] [Nontrivial A]
    (I : NormedSpace.GeometricStructureSpace ℂ A) :
    ∃ (H : Type uA) (instN : NormedAddCommGroup H),
      letI := instN
      ∃ instI : InnerProductSpace ℂ H,
        letI := instI
        ∃ instC : CompleteSpace H,
          letI := instC
          ∃ (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible),
            ∃ a : ClosureSpace.Homeomorph
                ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)).subspace (normalPart (NonUnitalStarAlgHom.range pi)))
                ((NormedSpace.geometricStructureClosure ℂ A).subspace
                  ((NormedSpace.geometricStructureClosure ℂ A).component I)),
              ∀ J : normalPart (NonUnitalStarAlgHom.range pi),
                (a.toEquiv J).val.val = (NonUnitalStarAlgHom.rangeRestrict pi) ⁻¹' J.val.val := by
  letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
  obtain ⟨phi, hphi⟩ := NonUnitalPureState.toGeometricSpectrum_surjective
    (NormedSpace.toGeometricSpectrum ℂ A I)
  let d := NormedSpace.geometricStructureClosure ℂ A
  let p := NonUnitalCStarRepresentation.matrixCoefficientKernel phi.gnsRepresentation
    phi.isIrreducible_gnsRepresentation phi.gnsVector phi.gnsVector
    phi.gnsVector_ne_zero phi.gnsVector_ne_zero
  have hcomp : d.component p = d.component I := by
    have h := congrArg Subtype.val hphi
    change d.component phi.geometricPoint = d.component I at h
    rw [phi.geometricPoint_eq_matrixCoefficientKernel] at h
    exact h
  let b := imageNormalPartHomeomorph phi.gnsRepresentation
    phi.isIrreducible_gnsRepresentation phi.gnsVector phi.gnsVector
    phi.gnsVector_ne_zero phi.gnsVector_ne_zero
  let a : ClosureSpace.Homeomorph (d.subspace (d.component p))
      (d.subspace (d.component I)) :=
    (ClosureSpace.Homeomorph.refl d).subspace (d.component p) (d.component I)
      (fun J => by change J ∈ d.component p ↔ J ∈ d.component I; rw [hcomp])
  refine ⟨phi.GNS, inferInstance, inferInstance, inferInstance,
    phi.gnsRepresentation, phi.isIrreducible_gnsRepresentation, b.trans a, ?_⟩
  intro J
  exact imageNormalPartHomeomorph_val phi.gnsRepresentation
    phi.isIrreducible_gnsRepresentation phi.gnsVector phi.gnsVector
    phi.gnsVector_ne_zero phi.gnsVector_ne_zero J

end MathlibAnnex.Analysis.CStarAlgebra

namespace ClosureSpace

open MathlibAnnex.Analysis.CStarAlgebra

/-- All actual nonzero irreducible representation-image normal parts, with
algebra and represented-Hilbert carrier universes specified separately. -/
def HasImageNormalPartFiniteConjugation.{uA, uH, uX} {X : Type uX}
    (c : ClosureSpace X) : Prop :=
  ∀ (A : Type uA) [NonUnitalCStarAlgebra A] [Nontrivial A],
    ∀ (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
      ∀ pi : NonUnitalCStarRepresentation A H, pi.IsIrreducible →
        let d := (NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)).subspace (normalPart (NonUnitalStarAlgHom.range pi))
        ∀ f : FiniteHomeomorph d c, d.Continuous c f.toEquiv →
          ∀ g : FiniteHomeomorph d d, d.Continuous d g.toEquiv →
            c.Continuous c (f.conjugate g).toEquiv ∧
              c.Continuous c (f.conjugate g).toEquiv.symm

universe uA uH uX uL
variable {X : Type uX} {c : ClosureSpace X}

attribute [local instance] HomKernelQuotient.imageCStarAlgebra HomKernelQuotient.isClosed_image

/-- Actual-algebra component tests cover every nonzero irreducible action on
any separately specified Hilbert universe, by the genuine normal restriction. -/
theorem HasCStarComponentFiniteConjugation.hasImageNormalPartFiniteConjugation
    (hc : HasCStarComponentFiniteConjugation.{uA, uX} c) :
    HasImageNormalPartFiniteConjugation.{uA, uH, uX} c := by
  intro A instA hA H instN instI instC pi hpi
  dsimp only
  intro f hf g hg
  letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
  letI : Nontrivial H := NonUnitalCStarRepresentation.nontrivial_of_isNonzero pi hpi.1
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  let I := NonUnitalCStarRepresentation.matrixCoefficientKernel pi hpi x x hx hx
  let d := (NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)).subspace (normalPart (NonUnitalStarAlgHom.range pi))
  let k := (NormedSpace.geometricStructureClosure ℂ A).subspace
    ((NormedSpace.geometricStructureClosure ℂ A).component I)
  let a : Homeomorph k d := (imageNormalPartHomeomorph pi hpi x x hx hx).symm
  let f' := a.toFiniteHomeomorph.trans f
  let g' := a.symm.toFiniteHomeomorph.conjugate g
  have hf' : k.Continuous c f'.toEquiv := hf.comp a.continuous_toFun
  have hg' : k.Continuous k g'.toEquiv :=
    a.continuous_invFun.comp (hg.comp a.continuous_toFun)
  have hh := hc A I f' hf' g' hg'
  have heq : (f'.conjugate g').toEquiv = (f.conjugate g).toEquiv :=
    FiniteHomeomorph.conjugate_reparam_toEquiv a f g
  rw [heq] at hh
  exact hh

/-- The actual GNS representatives suffice for the converse, without assuming
that every separately specified Hilbert carrier belongs to the algebra universe. -/
theorem HasImageNormalPartFiniteConjugation.hasCStarComponentFiniteConjugation
    (hc : HasImageNormalPartFiniteConjugation.{uA, uA, uX} c) :
    HasCStarComponentFiniteConjugation.{uA, uX} c := by
  intro A instA hA I f hf g hg
  obtain ⟨H, instN, h⟩ := exists_representation_normalPart_homeomorph_component A I
  letI := instN
  obtain ⟨instI, h⟩ := h
  letI := instI
  obtain ⟨instC, pi, hpi, a, ha⟩ := h
  letI := instC
  let d := (NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)).subspace (normalPart (NonUnitalStarAlgHom.range pi))
  let k := (NormedSpace.geometricStructureClosure ℂ A).subspace
    ((NormedSpace.geometricStructureClosure ℂ A).component I)
  let f' := a.toFiniteHomeomorph.trans f
  let g' := a.symm.toFiniteHomeomorph.conjugate g
  have hf' : d.Continuous c f'.toEquiv := hf.comp a.continuous_toFun
  have hg' : d.Continuous d g'.toEquiv :=
    a.continuous_invFun.comp (hg.comp a.continuous_toFun)
  have hh := hc A H pi hpi f' hf' g' hg'
  have heq : (f'.conjugate g').toEquiv = (f.conjugate g).toEquiv :=
    FiniteHomeomorph.conjugate_reparam_toEquiv a f g
  rw [heq] at hh
  exact hh

/-- Exact two-way reduction to all representation images in the algebra
universe. The forward implication above remains valid for arbitrary uH. -/
theorem hasCStarComponentFiniteConjugation_iff_image_normal_parts :
    HasCStarComponentFiniteConjugation.{uA, uX} c ↔
      HasImageNormalPartFiniteConjugation.{uA, uA, uX} c :=
  ⟨HasCStarComponentFiniteConjugation.hasImageNormalPartFiniteConjugation,
    HasImageNormalPartFiniteConjugation.hasCStarComponentFiniteConjugation⟩

/-- The class-relative property with a sufficiently large source-carrier
universe is exactly the actual normal-part test family. -/
theorem hasContinuousFiniteConjugation_iff_image_normal_parts :
    c.HasContinuousFiniteConjugation
        (ClosureCat.IsCStarRealizable.{uA, max uA uL}) ↔
      HasImageNormalPartFiniteConjugation.{uA, uA, uX} c :=
  hasContinuousFiniteConjugation_iff_cstar_components_max.trans
    hasCStarComponentFiniteConjugation_iff_image_normal_parts

/-- Testing genuine small GNS models also supplies every larger (or otherwise
independently specified) actual irreducible representation as a test source. -/
theorem HasImageNormalPartFiniteConjugation.of_algebra_universe_tests
    (hc : HasImageNormalPartFiniteConjugation.{uA, uA, uX} c) :
    HasImageNormalPartFiniteConjugation.{uA, uH, uX} c :=
  hc.hasCStarComponentFiniteConjugation.hasImageNormalPartFiniteConjugation

/-- No source-carrier lower bound is needed in this direction: an actual
realization itself supplies the homeomorphism into any requested carrier. -/
theorem HasImageNormalPartFiniteConjugation.hasContinuousFiniteConjugation
    (hc : HasImageNormalPartFiniteConjugation.{uA, uA, uX} c) :
    c.HasContinuousFiniteConjugation (ClosureCat.IsCStarRealizable.{uA, uL}) :=
  hc.hasCStarComponentFiniteConjugation.hasContinuousFiniteConjugation

end ClosureSpace

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uA uX

attribute [local instance] HomKernelQuotient.imageCStarAlgebra HomKernelQuotient.isClosed_image

/-- Extract BOTH the actual algebra and an actual nonzero irreducible image
from a realizable source/component. The algebra remains in its witness universe;
its GNS carrier remains in that same universe, independently of the source X.
The formula retains the original realization map, rather than replacing its
component by a primitive kernel or by its closure. -/
theorem exists_representation_normalPart_homeomorph_of_isCStarRealizable
    (L : ClosureCat.{uX}) (hL : ClosureCat.IsCStarRealizable.{uA, uX} L) (t : L) :
    ∃ (A : Type uA) (instA : NonUnitalCStarAlgebra A),
      letI := instA
      Nontrivial A ∧
      ∃ r : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A) L.str,
        ∃ (H : Type uA) (instN : NormedAddCommGroup H),
          letI := instN
          ∃ instI : InnerProductSpace ℂ H,
            letI := instI
            ∃ instC : CompleteSpace H,
              letI := instC
              ∃ (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible),
                ∃ a : ClosureSpace.Homeomorph
                    ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)).subspace (normalPart (NonUnitalStarAlgHom.range pi)))
                    (L.str.subspace (L.str.component t)),
                  ∀ J : normalPart (NonUnitalStarAlgHom.range pi),
                    (r.toEquiv.symm (a.toEquiv J).val).val = (NonUnitalStarAlgHom.rangeRestrict pi) ⁻¹' J.val.val := by
  obtain ⟨A, instA, hA, ⟨r⟩⟩ := hL
  letI : NonUnitalCStarAlgebra A := instA
  letI : Nontrivial A := hA
  let I := r.toEquiv.symm t
  obtain ⟨H, instN, h⟩ := exists_representation_normalPart_homeomorph_component A I
  letI := instN
  obtain ⟨instI, h⟩ := h
  letI := instI
  obtain ⟨instC, pi, hpi, a, ha⟩ := h
  letI := instC
  let d := NormedSpace.geometricStructureClosure ℂ A
  let b : ClosureSpace.Homeomorph (d.subspace (d.component I))
      (L.str.subspace (L.str.component t)) :=
    r.subspace (d.component I) (L.str.component t) (fun J => by
      change d.Related (r.toEquiv.symm t) J ↔ L.str.Related t (r.toEquiv J)
      have hrel : L.str.Related (r.toEquiv (r.toEquiv.symm t)) (r.toEquiv J) ↔
          d.Related (r.toEquiv.symm t) J :=
        r.toFiniteHomeomorph.related_iff (r.toEquiv.symm t) J
      rw [r.toEquiv.apply_symm_apply] at hrel
      exact hrel.symm)
  refine ⟨A, instA, hA, r, H, instN, instI, instC, pi, hpi, a.trans b, ?_⟩
  intro J
  change (r.toEquiv.symm (r.toEquiv (a.toEquiv J).val)).val = _
  rw [Equiv.symm_apply_apply]
  exact ha J

/-- The inherited full image and normal restriction still have precisely the
same underlying preimage map in the test reduction. This records the two target
subtypes without assuming that the coefficient component is closed. -/
theorem imageNormalPartHomeomorph_eq_full_image_and_preimage
    {A : Type uA} [NonUnitalCStarAlgebra A] [Nontrivial A]
    [PartialOrder A] [StarOrderedRing A]
    {H : Type uX} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) (J : normalPart (NonUnitalStarAlgHom.range pi)) :
    ((imageNormalPartHomeomorph pi hpi x y hx hy).toEquiv J).val =
        ((NonUnitalCStarRepresentation.coefficientImageGeometricStructureHomeomorph
          pi hpi x y hx hy).toEquiv J.val).val ∧
      ((imageNormalPartHomeomorph pi hpi x y hx hy).toEquiv J).val.val =
        (NonUnitalStarAlgHom.rangeRestrict pi) ⁻¹' J.val.val :=
  ⟨MathlibAnnex.Analysis.CStarAlgebra.imageNormalPartHomeomorph_eq_coefficientImageGeometricStructureHomeomorph
      pi hpi x y hx hy J,
    imageNormalPartHomeomorph_val pi hpi x y hx hy J⟩

end MathlibAnnex.Analysis.CStarAlgebra
