/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.SpectrumSingleton
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartFiniteConjugation

/-!
# Singleton spectra and the same faithful normal-part target

The singleton is existence together with uniqueness in the independent
`IrreducibleSpectrum`, not in the primitive-kernel quotient. The representation
is the actual pure-state GNS supplied by the established singleton theorem.
Its faithfulness and full normality are conclusions. All component subspaces
use the original GSS closure, and the homeomorphism retains the literal
preimage map of that same representation.

The source algebra universe in the conjugation tests is independent of the
fixed target algebra. The max-universe endpoint uses the established source
reduction; it does not shrink an arbitrary large representation carrier.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uA uH uD uB uL
variable {A : Type uA} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] HomKernelQuotient.imageCStarAlgebra HomKernelQuotient.isClosed_image

/-- Existence in the singleton condition supplies a component; uniqueness
then makes EVERY component the whole actual GSS. -/
theorem component_eq_univ_of_singleton_irreducibleSpectrum
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (J : NormedSpace.GeometricStructureSpace ℂ A) :
    (NormedSpace.geometricStructureClosure ℂ A).component J = Set.univ := by
  obtain ⟨I, hI⟩ :=
    exists_forall_eq_irreducibleSpectrum_iff_exists_component_eq_univ.mp hsingle
  let c := NormedSpace.geometricStructureClosure ℂ A
  have hIJ : c.Related I J := by
    change J ∈ c.component I
    rw [hI]
    trivial
  exact (c.component_eq_of_related hIJ).symm.trans hI

/-- Forget the component membership proof, using the proved full-component
identity. The inverse attaches that proof to the SAME GSS point. -/
def singletonComponentHomeomorph
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (I : NormedSpace.GeometricStructureSpace ℂ A) :
    ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I))
      (NormedSpace.geometricStructureClosure ℂ A) := by
  let c := NormedSpace.geometricStructureClosure ℂ A
  let e : c.component I ≃ NormedSpace.GeometricStructureSpace ℂ A :=
    { toFun := Subtype.val
      invFun := fun J => ⟨J, by
        rw [component_eq_univ_of_singleton_irreducibleSpectrum hsingle I]
        trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ClosureSpace.homeomorphInduced c e

@[simp]
theorem singletonComponentHomeomorph_apply
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (I : NormedSpace.GeometricStructureSpace ℂ A)
    (J : (NormedSpace.geometricStructureClosure ℂ A).component I) :
    (singletonComponentHomeomorph hsingle I).toEquiv J = J.val := rfl

@[simp]
theorem singletonComponentHomeomorph_symm_val
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (I J : NormedSpace.GeometricStructureSpace ℂ A) :
    ((singletonComponentHomeomorph hsingle I).toEquiv.symm J).val = J := rfl

/-- The same representation's normal restriction now reaches ALL of S(A).
No faithful or full-normal hypothesis is added to the singleton input. -/
def singletonImageNormalPartHomeomorph
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)).subspace (normalPart (NonUnitalStarAlgHom.range pi)))
      (NormedSpace.geometricStructureClosure ℂ A) := by
  letI : Nontrivial H := NonUnitalCStarRepresentation.nontrivial_of_isNonzero pi hpi.1
  let x : H := Classical.choose (exists_ne (0 : H))
  have hx : x ≠ 0 := Classical.choose_spec (exists_ne (0 : H))
  exact (imageNormalPartHomeomorph pi hpi x x hx hx).trans
    (singletonComponentHomeomorph hsingle
      (NonUnitalCStarRepresentation.matrixCoefficientKernel pi hpi x x hx hx))

/-- The forward map is exactly inverse image under the actual range restriction. -/
@[simp]
theorem singletonImageNormalPartHomeomorph_val
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (J : normalPart (NonUnitalStarAlgHom.range pi)) :
    ((singletonImageNormalPartHomeomorph hsingle pi hpi).toEquiv J).val =
      (NonUnitalStarAlgHom.rangeRestrict pi) ⁻¹' J.val.val := rfl

/-- Inverse evaluation is stated as the corresponding preimage equation,
not as an unjustified direct image by a map on vectors. -/
theorem singletonImageNormalPartHomeomorph_symm_preimage
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (I : NormedSpace.GeometricStructureSpace ℂ A) :
    (NonUnitalStarAlgHom.rangeRestrict pi) ⁻¹'
        ((singletonImageNormalPartHomeomorph hsingle pi hpi).toEquiv.symm I).val.val = I.val := by
  exact congrArg (fun J : NormedSpace.GeometricStructureSpace ℂ A => J.val)
    ((singletonImageNormalPartHomeomorph hsingle pi hpi).toEquiv.apply_symm_apply I)

/-- The two ends of the target change have the same class-relative property. -/
theorem singleton_component_hasContinuousFiniteConjugation_iff
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (I : NormedSpace.GeometricStructureSpace ℂ A) (D : ClosureCat.{uD} → Prop) :
    ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I)).HasContinuousFiniteConjugation D ↔
      ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)).subspace
        (normalPart (NonUnitalStarAlgHom.range pi))).HasContinuousFiniteConjugation D :=
  ((singletonComponentHomeomorph hsingle I).trans
    (singletonImageNormalPartHomeomorph hsingle pi hpi).symm).hasContinuousFiniteConjugation_iff

/-- The existential component clause is equivalent to the condition on this
same representation's normal part. Existence of a component is retained. -/
theorem exists_singleton_component_hasContinuousFiniteConjugation_iff
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (D : ClosureCat.{uD} → Prop) :
    (∃ I : NormedSpace.GeometricStructureSpace ℂ A,
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I)).HasContinuousFiniteConjugation D) ↔
      ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)).subspace
        (normalPart (NonUnitalStarAlgHom.range pi))).HasContinuousFiniteConjugation D := by
  constructor
  · rintro ⟨I, hI⟩
    exact (singleton_component_hasContinuousFiniteConjugation_iff hsingle pi hpi I D).mp hI
  · intro hN
    obtain ⟨I, _⟩ :=
      exists_forall_eq_irreducibleSpectrum_iff_exists_component_eq_univ.mp hsingle
    exact ⟨I, (singleton_component_hasContinuousFiniteConjugation_iff hsingle pi hpi I D).mpr hN⟩

/-- Universe-exact normal-part test version. Algebra witnesses of all tests
lie in uB; eligible realizable source carriers lie in max(uB,uL). -/
theorem exists_singleton_component_iff_image_normal_part_tests
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    (∃ I : NormedSpace.GeometricStructureSpace ℂ A,
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I)).HasContinuousFiniteConjugation
          (ClosureCat.IsCStarRealizable.{uB, max uB uL})) ↔
      ClosureSpace.HasImageNormalPartFiniteConjugation.{uB, uB, uH}
        ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range pi)).subspace (normalPart (NonUnitalStarAlgHom.range pi))) :=
  (exists_singleton_component_hasContinuousFiniteConjugation_iff hsingle pi hpi
    (ClosureCat.IsCStarRealizable.{uB, max uB uL})).trans
      ClosureSpace.hasContinuousFiniteConjugation_iff_image_normal_parts

/-- A genuine small faithful model with its literal preimage homeomorphism,
all full-component identities, and the exact target-test equivalence. -/
theorem exists_singleton_normalPart_finiteConjugation_model
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q) :
    ∃ phi : NonUnitalPureState A,
      Function.Injective phi.gnsRepresentation ∧
      normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation) = Set.univ ∧
      (∀ I : NormedSpace.GeometricStructureSpace ℂ A,
        (NormedSpace.geometricStructureClosure ℂ A).component I = Set.univ) ∧
      ∃ r : ClosureSpace.Homeomorph
          ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range phi.gnsRepresentation)).subspace
            (normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation)))
          (NormedSpace.geometricStructureClosure ℂ A),
        (∀ J : normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation),
          (r.toEquiv J).val = (NonUnitalStarAlgHom.rangeRestrict phi.gnsRepresentation) ⁻¹' J.val.val) ∧
        ((∃ I : NormedSpace.GeometricStructureSpace ℂ A,
          ((NormedSpace.geometricStructureClosure ℂ A).subspace
            ((NormedSpace.geometricStructureClosure ℂ A).component I)).HasContinuousFiniteConjugation
              (ClosureCat.IsCStarRealizable.{uA, max uA uL})) ↔
          ClosureSpace.HasImageNormalPartFiniteConjugation.{uA, uA, uA}
            ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range phi.gnsRepresentation)).subspace
              (normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation)))) := by
  obtain ⟨phi, hfaith, hnormal⟩ :=
    exists_forall_eq_irreducibleSpectrum_iff_exists_faithful_pureState.mp hsingle
  exact ⟨phi, hfaith, hnormal, component_eq_univ_of_singleton_irreducibleSpectrum hsingle,
    singletonImageNormalPartHomeomorph hsingle phi.gnsRepresentation phi.isIrreducible_gnsRepresentation,
    singletonImageNormalPartHomeomorph_val hsingle phi.gnsRepresentation phi.isIrreducible_gnsRepresentation,
    exists_singleton_component_iff_image_normal_part_tests hsingle phi.gnsRepresentation
      phi.isIrreducible_gnsRepresentation⟩

end MathlibAnnex.Analysis.CStarAlgebra
