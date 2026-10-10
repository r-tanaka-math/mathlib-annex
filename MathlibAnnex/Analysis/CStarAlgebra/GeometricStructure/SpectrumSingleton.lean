/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartComponentClosed
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.SpectralHomeomorph
import MathlibAnnex.Analysis.Normed.GeometricStructure.Separation

/-!
# Singleton irreducible spectra and faithful images with full normal part

Singleton means `∃ q, ∀ r, r = q`, so existence is not lost. The spectrum
is the independently defined pure-state GNS quotient, not the primitive
kernel quotient. Its proved homeomorphism with GS is used on actual points.

Faithfulness is DERIVED from the intersection of all GSS points being zero
and the whole-component identity J_C = ker(pi). In the converse direction
faithfulness gives density, while full normality gives closedness. Neither
condition alone is substituted for the other. No elementary-algebra claim
or result about the zero algebra is made here.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] HomKernelQuotient.imageCStarAlgebra HomKernelQuotient.isClosed_image

attribute [local instance] geometricSpectrumTopology

open NonUnitalCStarRepresentation

private def singletonContinuousMap (pi : NonUnitalCStarRepresentation A H) :
    A →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := pi, map_add' := map_add pi, map_smul' := map_smul pi }
    1 (fun a => by
      change ‖pi a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le pi a)

/-- An entire coefficient component fills S(A) precisely when its representation
is faithful and its ACTUAL image GSS is all normal. -/
theorem component_matrixCoefficientKernel_eq_univ_iff
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (NormedSpace.geometricStructureClosure ℂ A).component
      (matrixCoefficientKernel pi hpi x y hx hy) = Set.univ ↔
      Function.Injective pi ∧ normalPart (NonUnitalStarAlgHom.range pi) = Set.univ := by
  let c := NormedSpace.geometricStructureClosure ℂ A
  let I := matrixCoefficientKernel pi hpi x y hx hy
  have hkernel : ClosureSpace.HullKernel.kernel (NormedSpace.geometricStructureFamily ℂ A)
      (c.component I) = ((singletonContinuousMap pi).ker : Set A) :=
    geometricSpectrumKernel_toGeometricSpectrum_matrixCoefficientKernel pi hpi x y hx hy
  constructor
  · intro hC
    have hk : ((singletonContinuousMap pi).ker : Set A) = ({0} : Set A) := by
      rw [← hkernel, hC]
      exact NormedSpace.kernel_geometricStructureFamily_univ ℂ A
    have hfaith : Function.Injective pi := by
      intro a b hab
      have hz : a - b ∈ ((singletonContinuousMap pi).ker : Set A) := by
        change pi (a - b) = 0
        rw [map_sub, hab, sub_self]
      rw [hk] at hz
      exact sub_eq_zero.mp (Set.mem_singleton_iff.mp hz)
    refine ⟨hfaith, ?_⟩
    apply (isClosed_component_matrixCoefficientKernel_iff_normalPart_eq_univ
      pi hpi x y hx hy).1
    rw [hC]
    exact c.isClosed_univ
  · rintro ⟨hfaith, hnormal⟩
    have hk : ((singletonContinuousMap pi).ker : Set A) = ({0} : Set A) := by
      ext a
      change pi a = 0 ↔ a = 0
      exact ⟨fun ha => hfaith (ha.trans (map_zero pi).symm),
        fun ha => ha ▸ map_zero pi⟩
    have hdense : c.closure (c.component I) = Set.univ :=
      (NormedSpace.geometricStructureClosure_eq_univ_iff_kernel_eq_singleton_zero
        ℂ A (c.component I)).2 (hkernel.trans hk)
    have hc : c.IsClosed (c.component I) :=
      (isClosed_component_matrixCoefficientKernel_iff_normalPart_eq_univ
        pi hpi x y hx hy).2 hnormal
    exact ((c.isClosed_iff _).1 hc).symm.trans hdense

/-- Specialization to the actual GNS of a pure state. -/
theorem component_geometricPoint_eq_univ_iff (phi : NonUnitalPureState A) :
    (NormedSpace.geometricStructureClosure ℂ A).component phi.geometricPoint = Set.univ ↔
      Function.Injective phi.gnsRepresentation ∧
        normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation) = Set.univ := by
  rw [phi.geometricPoint_eq_matrixCoefficientKernel]
  exact component_matrixCoefficientKernel_eq_univ_iff
    phi.gnsRepresentation phi.isIrreducible_gnsRepresentation
    phi.gnsVector phi.gnsVector phi.gnsVector_ne_zero phi.gnsVector_ne_zero

/-- The independently defined spectrum is a singleton exactly when one actual
component fills the original GSS. The proved ordinary spectral homeomorphism
supplies the equivalence, with its point formula unchanged. -/
theorem exists_forall_eq_irreducibleSpectrum_iff_exists_component_eq_univ :
    (∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q) ↔
      ∃ I : NormedSpace.GeometricStructureSpace ℂ A,
        (NormedSpace.geometricStructureClosure ℂ A).component I = Set.univ := by
  let c := NormedSpace.geometricStructureClosure ℂ A
  let e := (irreducibleSpectrumHomeomorph A).toEquiv
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨I, hI⟩ := NormedSpace.toGeometricSpectrum_surjective ℂ A (e q)
    refine ⟨I, Set.eq_univ_iff_forall.mpr (fun J => ?_)⟩
    have heJ := e.apply_symm_apply (NormedSpace.toGeometricSpectrum ℂ A J)
    have hIJ : NormedSpace.toGeometricSpectrum ℂ A I =
        NormedSpace.toGeometricSpectrum ℂ A J :=
      hI.trans ((congrArg e (hq (e.symm (NormedSpace.toGeometricSpectrum ℂ A J)))).symm.trans heJ)
    exact (c.toComponentPoint_eq_iff I J).1 hIJ
  · rintro ⟨I, hI⟩
    let q := e.symm (NormedSpace.toGeometricSpectrum ℂ A I)
    refine ⟨q, fun r => e.injective ?_⟩
    obtain ⟨J, hJ⟩ := NormedSpace.toGeometricSpectrum_surjective ℂ A (e r)
    have hrel : c.Related I J := by
      change J ∈ c.component I
      rw [hI]
      trivial
    have hIJ := (c.toComponentPoint_eq_iff I J).2 hrel
    exact hJ.symm.trans (hIJ.symm.trans
      (e.apply_symm_apply (NormedSpace.toGeometricSpectrum ℂ A I)).symm)

/-- Corollary 7.3 with a small, genuine GNS witness. Faithfulness in the
forward implication is proved from the total intersection, not assumed. -/
theorem exists_forall_eq_irreducibleSpectrum_iff_exists_faithful_pureState :
    (∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q) ↔
      ∃ phi : NonUnitalPureState A, Function.Injective phi.gnsRepresentation ∧
        normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation) = Set.univ := by
  rw [exists_forall_eq_irreducibleSpectrum_iff_exists_component_eq_univ]
  constructor
  · rintro ⟨I, hI⟩
    obtain ⟨phi, hphi⟩ := NonUnitalPureState.toGeometricSpectrum_surjective
      (NormedSpace.toGeometricSpectrum ℂ A I)
    have hcomp : (NormedSpace.geometricStructureClosure ℂ A).component phi.geometricPoint =
        (NormedSpace.geometricStructureClosure ℂ A).component I := congrArg Subtype.val hphi
    exact ⟨phi, (component_geometricPoint_eq_univ_iff phi).1 (hcomp.trans hI)⟩
  · rintro ⟨phi, hfaith, hnormal⟩
    exact ⟨phi.geometricPoint, (component_geometricPoint_eq_univ_iff phi).2 ⟨hfaith, hnormal⟩⟩

/-- A faithful nonzero irreducible action in ANY Hilbert universe with full
normal part forces a singleton of the independent small spectrum. -/
theorem exists_forall_eq_irreducibleSpectrum_of_faithful_representation
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hfaith : Function.Injective pi) (hnormal : normalPart (NonUnitalStarAlgHom.range pi) = Set.univ) :
    ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q := by
  letI : Nontrivial H := nontrivial_of_isNonzero pi hpi.1
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  apply exists_forall_eq_irreducibleSpectrum_iff_exists_component_eq_univ.2
  exact ⟨matrixCoefficientKernel pi hpi x x hx hx,
    (component_matrixCoefficientKernel_eq_univ_iff pi hpi x x hx hx).2 ⟨hfaith, hnormal⟩⟩

/-- In a singleton spectrum, EVERY nonzero irreducible representation is
faithful and has full normal part. This includes arbitrary Hilbert universes. -/
theorem faithful_and_normalPart_eq_univ_of_singleton_irreducibleSpectrum
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    Function.Injective pi ∧ normalPart (NonUnitalStarAlgHom.range pi) = Set.univ := by
  obtain ⟨q, hq⟩ := hsingle
  letI : Nontrivial H := nontrivial_of_isNonzero pi hpi.1
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  let c := NormedSpace.geometricStructureClosure ℂ A
  let I := matrixCoefficientKernel pi hpi x x hx hx
  apply (component_matrixCoefficientKernel_eq_univ_iff pi hpi x x hx hx).1
  apply Set.eq_univ_iff_forall.mpr
  intro J
  let e := (irreducibleSpectrumHomeomorph A).toEquiv
  have heq : e.symm (NormedSpace.toGeometricSpectrum ℂ A I) =
      e.symm (NormedSpace.toGeometricSpectrum ℂ A J) :=
    (hq _).trans (hq _).symm
  have hIJ : NormedSpace.toGeometricSpectrum ℂ A I =
      NormedSpace.toGeometricSpectrum ℂ A J := e.symm.injective heq
  exact (c.toComponentPoint_eq_iff I J).1 hIJ

/-- The literal existence-of-faithful-representation formulation of 7.3.
The witness lives in the universe of A because the actual GNS construction
does. The previous two theorems handle every separately specified universe.
The local structures are actual structures, not certificates containing
faithfulness, normality, or the desired singleton conclusion. -/
theorem exists_forall_eq_irreducibleSpectrum_iff_exists_faithful_representation :
    (∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q) ↔
    (∃ (H' : Type u) (instN : NormedAddCommGroup H'),
      letI := instN
      ∃ instI : InnerProductSpace ℂ H',
        letI := instI
        ∃ instC : CompleteSpace H',
          letI := instC
          ∃ pi : NonUnitalCStarRepresentation A H',
            pi.IsIrreducible ∧ Function.Injective pi ∧ normalPart (NonUnitalStarAlgHom.range pi) = Set.univ) := by
  constructor
  · intro hsingle
    obtain ⟨phi, hfaith, hnormal⟩ :=
      exists_forall_eq_irreducibleSpectrum_iff_exists_faithful_pureState.1 hsingle
    exact ⟨phi.GNS, inferInstance, inferInstance, inferInstance, phi.gnsRepresentation,
      phi.isIrreducible_gnsRepresentation, hfaith, hnormal⟩
  · rintro ⟨H', instN, h⟩
    letI := instN
    obtain ⟨instI, h⟩ := h
    letI := instI
    obtain ⟨instC, h⟩ := h
    letI := instC
    obtain ⟨pi, hpi, hfaith, hnormal⟩ := h
    exact exists_forall_eq_irreducibleSpectrum_of_faithful_representation pi hpi hfaith hnormal

end MathlibAnnex.Analysis.CStarAlgebra
