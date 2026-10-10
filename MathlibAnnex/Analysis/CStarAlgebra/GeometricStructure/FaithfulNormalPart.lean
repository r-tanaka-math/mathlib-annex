/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.SpectrumSingleton

/-!
# Faithful normal-part transport along a specified GSS homeomorphism

Faithfulness is equivalent to DENSITY of the coefficient component. This is
not the full-component criterion, which additionally requires full normality.
A specified GSS homeomorphism transports that dense component. A genuine
pure GNS representative of the transported component is consequently faithful.
The full image homeomorphism retains its literal inverse-image formula, and
its inverse composed with the specified map transports the normal parts.

This is the local content of Lemma 8.8. No compact-intersection dichotomy,
Type I identification, or arbitrary closed-ideal quotient is used.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] HomKernelQuotient.imageCStarAlgebra HomKernelQuotient.isClosed_image
open NonUnitalCStarRepresentation

private def faithfulContinuousMap (pi : NonUnitalCStarRepresentation A H) :
    A →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := pi, map_add' := map_add pi, map_smul' := map_smul pi }
    1 (fun a => by
      change ‖pi a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le pi a)

/-- Zero component kernel means a dense component, not a component equal to
all points. Faithfulness is deduced from the actual representation kernel. -/
theorem closure_component_matrixCoefficientKernel_eq_univ_iff
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (NormedSpace.geometricStructureClosure ℂ A).closure
      ((NormedSpace.geometricStructureClosure ℂ A).component
        (matrixCoefficientKernel pi hpi x y hx hy)) = Set.univ ↔
      Function.Injective pi := by
  have hkernel : ClosureSpace.HullKernel.kernel (NormedSpace.geometricStructureFamily ℂ A)
      ((NormedSpace.geometricStructureClosure ℂ A).component
        (matrixCoefficientKernel pi hpi x y hx hy)) =
      ((faithfulContinuousMap pi).ker : Set A) :=
    geometricSpectrumKernel_toGeometricSpectrum_matrixCoefficientKernel pi hpi x y hx hy
  rw [NormedSpace.geometricStructureClosure_eq_univ_iff_kernel_eq_singleton_zero, hkernel]
  constructor
  · intro hk a b hab
    have hz : a - b ∈ ((faithfulContinuousMap pi).ker : Set A) := by
      change pi (a - b) = 0
      rw [map_sub, hab, sub_self]
    rw [hk] at hz
    exact sub_eq_zero.mp (Set.mem_singleton_iff.mp hz)
  · intro hinj
    ext a
    change pi a = 0 ↔ a = 0
    exact ⟨fun ha => hinj (ha.trans (map_zero pi).symm), fun ha => ha ▸ map_zero pi⟩

/-- The pure-state version still asserts density, with no full normality
assumption or conclusion. -/
theorem closure_component_geometricPoint_eq_univ_iff (phi : NonUnitalPureState A) :
    (NormedSpace.geometricStructureClosure ℂ A).closure
      ((NormedSpace.geometricStructureClosure ℂ A).component phi.geometricPoint) = Set.univ ↔
      Function.Injective phi.gnsRepresentation := by
  rw [phi.geometricPoint_eq_matrixCoefficientKernel]
  exact closure_component_matrixCoefficientKernel_eq_univ_iff
    phi.gnsRepresentation phi.isIrreducible_gnsRepresentation
    phi.gnsVector phi.gnsVector phi.gnsVector_ne_zero phi.gnsVector_ne_zero

/-- The full image GSS reaches the full original GSS when the representation
is faithful. The intermediate codomain is still the closure of a component. -/
def faithfulImageGeometricStructureHomeomorph
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hfaith : Function.Injective pi) (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi))
      (NormedSpace.geometricStructureClosure ℂ A) := by
  let c := NormedSpace.geometricStructureClosure ℂ A
  let I := matrixCoefficientKernel pi hpi x y hx hy
  have hd : c.closure (c.component I) = Set.univ :=
    (closure_component_matrixCoefficientKernel_eq_univ_iff pi hpi x y hx hy).2 hfaith
  let a : c.closure (c.component I) ≃ NormedSpace.GeometricStructureSpace ℂ A :=
    { toFun := Subtype.val
      invFun := fun J => ⟨J, by rw [hd]; trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (coefficientImageGeometricStructureHomeomorph pi hpi x y hx hy).trans
    (ClosureSpace.homeomorphInduced c a)

@[simp]
theorem faithfulImageGeometricStructureHomeomorph_val
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hfaith : Function.Injective pi) (x y : H) (hx : x ≠ 0) (hy : y ≠ 0)
    (J : NormedSpace.GeometricStructureSpace ℂ (NonUnitalStarAlgHom.range pi)) :
    ((faithfulImageGeometricStructureHomeomorph pi hpi hfaith x y hx hy).toEquiv J).val =
      (NonUnitalStarAlgHom.rangeRestrict pi) ⁻¹' J.val := rfl

/-- The inverse formula keeps the same range restriction and the same map. -/
theorem faithfulImageGeometricStructureHomeomorph_symm_preimage
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hfaith : Function.Injective pi) (x y : H) (hx : x ≠ 0) (hy : y ≠ 0)
    (I : NormedSpace.GeometricStructureSpace ℂ A) :
    (NonUnitalStarAlgHom.rangeRestrict pi) ⁻¹'
      ((faithfulImageGeometricStructureHomeomorph pi hpi hfaith x y hx hy).toEquiv.symm I).val =
        I.val := by
  let r := faithfulImageGeometricStructureHomeomorph pi hpi hfaith x y hx hy
  exact congrArg Subtype.val (r.toEquiv.apply_symm_apply I)

/-- Restricting this full map recovers the same coefficient component. -/
theorem image_normalPart_faithfulImageGeometricStructureHomeomorph
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hfaith : Function.Injective pi) (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (faithfulImageGeometricStructureHomeomorph pi hpi hfaith x y hx hy).toEquiv ''
      normalPart (NonUnitalStarAlgHom.range pi) = (NormedSpace.geometricStructureClosure ℂ A).component
        (matrixCoefficientKernel pi hpi x y hx hy) :=
  image_normalPart_eq_component pi hpi x y hx hy

section Transport
variable {B : Type w} [NonUnitalCStarAlgebra B] [hB : Nontrivial B]
variable [PartialOrder B] [StarOrderedRing B]

include hB in
/-- A specified homeomorphism carries a faithful coefficient component to
the component of a genuine faithful pure GNS of B. Both the original map and
the literal preimage homeomorphism occur in the conclusion. -/
theorem exists_faithful_pureState_image_transport
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hfaith : Function.Injective pi) (x y : H) (hx : x ≠ 0) (hy : y ≠ 0)
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B)) :
    ∃ phi : NonUnitalPureState B, Function.Injective phi.gnsRepresentation ∧
      ∃ r : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range phi.gnsRepresentation))
          (NormedSpace.geometricStructureClosure ℂ B),
        (∀ J, (r.toEquiv J).val = (NonUnitalStarAlgHom.rangeRestrict phi.gnsRepresentation) ⁻¹' J.val) ∧
        (∀ I, (NonUnitalStarAlgHom.rangeRestrict phi.gnsRepresentation) ⁻¹' (r.toEquiv.symm I).val = I.val) ∧
        (e.trans r.symm).toEquiv ''
          ((NormedSpace.geometricStructureClosure ℂ A).component
            (matrixCoefficientKernel pi hpi x y hx hy)) = normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation) := by
  let c := NormedSpace.geometricStructureClosure ℂ A
  let d := NormedSpace.geometricStructureClosure ℂ B
  let I := matrixCoefficientKernel pi hpi x y hx hy
  have hd : c.closure (c.component I) = Set.univ :=
    (closure_component_matrixCoefficientKernel_eq_univ_iff pi hpi x y hx hy).2 hfaith
  have heC : e.toEquiv '' c.component I = d.component (e.toEquiv I) :=
    e.toFiniteHomeomorph.image_component I
  have hd' : d.closure (d.component (e.toEquiv I)) = Set.univ := by
    rw [← heC, ← e.image_closure, hd, Set.image_univ]
    exact Set.range_eq_univ.mpr e.toEquiv.surjective
  obtain ⟨phi, hphi⟩ := NonUnitalPureState.toGeometricSpectrum_surjective
    (NormedSpace.toGeometricSpectrum ℂ B (e.toEquiv I))
  have hC : d.component phi.geometricPoint = d.component (e.toEquiv I) :=
    congrArg Subtype.val hphi
  have hphiFaith : Function.Injective phi.gnsRepresentation :=
    (closure_component_geometricPoint_eq_univ_iff phi).1 (by rw [hC]; exact hd')
  let r := faithfulImageGeometricStructureHomeomorph
    phi.gnsRepresentation phi.isIrreducible_gnsRepresentation hphiFaith
    phi.gnsVector phi.gnsVector phi.gnsVector_ne_zero phi.gnsVector_ne_zero
  have hr : r.toEquiv '' normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation) = d.component phi.geometricPoint := by
    rw [phi.geometricPoint_eq_matrixCoefficientKernel]
    exact image_normalPart_faithfulImageGeometricStructureHomeomorph
      phi.gnsRepresentation phi.isIrreducible_gnsRepresentation hphiFaith
      phi.gnsVector phi.gnsVector phi.gnsVector_ne_zero phi.gnsVector_ne_zero
  refine ⟨phi, hphiFaith, r, ?_, ?_, ?_⟩
  · intro J
    exact faithfulImageGeometricStructureHomeomorph_val _ _ _ _ _ _ _ J
  · intro J
    exact faithfulImageGeometricStructureHomeomorph_symm_preimage _ _ _ _ _ _ _ J
  · have hsets : e.toEquiv '' c.component I = r.toEquiv '' normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation) :=
      heC.trans (hC.symm.trans hr.symm)
    have h := congrArg (fun s => r.toEquiv.symm '' s) hsets
    change (r.toEquiv.symm ∘ e.toEquiv) '' c.component I = _
    simpa [Set.image_image] using h

end Transport

section ActualOperatorAlgebra
variable {B : Type w} [NonUnitalCStarAlgebra B]
variable [PartialOrder B] [StarOrderedRing B]

/-- Lemma 8.8 for an actual closed irreducible operator algebra. The source
is its normal part, not all its GSS points and not a primitive-kernel label.
The GNS Hilbert witness is in the universe of B; the original H is independent.
Nontriviality of B is derived from the specified bijection and an actual source point. -/
theorem exists_faithful_normalPart_transport
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ S)
      (NormedSpace.geometricStructureClosure ℂ B)) :
    ∃ phi : NonUnitalPureState B, Function.Injective phi.gnsRepresentation ∧
      ∃ r : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range phi.gnsRepresentation))
          (NormedSpace.geometricStructureClosure ℂ B),
        (∀ J, (r.toEquiv J).val = (NonUnitalStarAlgHom.rangeRestrict phi.gnsRepresentation) ⁻¹' J.val) ∧
        (∀ I, (NonUnitalStarAlgHom.rangeRestrict phi.gnsRepresentation) ⁻¹' (r.toEquiv.symm I).val = I.val) ∧
        (e.trans r.symm).toEquiv '' normalPart S = normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation) := by
  let pi := NonUnitalStarSubalgebraClass.subtype S
  letI : Nontrivial H := nontrivial_of_isNonzero pi hS.1
  letI : Nontrivial S := by
    obtain ⟨a, ha⟩ := hS.1
    refine ⟨⟨a, 0, ?_⟩⟩
    intro h
    exact ha (by simpa only [h, map_zero])
  letI : PartialOrder S := _root_.CStarAlgebra.spectralOrder S
  letI : StarOrderedRing S := _root_.CStarAlgebra.spectralOrderedRing S
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  let J := e.toEquiv (matrixCoefficientKernel pi hS x x hx hx)
  letI : Nontrivial B := not_subsingleton_iff_nontrivial.mp (by
    intro hB
    letI : Subsingleton B := hB
    letI := NormedSpace.isEmpty_geometricStructureSpace_of_subsingleton ℂ B
    exact isEmptyElim J)
  have hC : (NormedSpace.geometricStructureClosure ℂ S).component
      (matrixCoefficientKernel pi hS x x hx hx) = normalPart S := by
    have hseed : matrixCoefficientKernel pi hS x x hx hx =
        restrictedMatrixCoefficientKernel S hS x x hx hx := Subtype.ext rfl
    rw [hseed]
    exact component_restrictedMatrixCoefficientKernel_eq_normalPart S hS x x hx hx
  obtain ⟨phi, hfaith, r, hpre, hinv, hnorm⟩ :=
    exists_faithful_pureState_image_transport pi hS (fun a b h => Subtype.ext h) x x hx hx e
  rw [hC] at hnorm
  exact ⟨phi, hfaith, r, hpre, hinv, hnorm⟩

end ActualOperatorAlgebra
end MathlibAnnex.Analysis.CStarAlgebra
