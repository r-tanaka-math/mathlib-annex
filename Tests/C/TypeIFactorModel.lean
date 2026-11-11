import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.TypeIFactorModel

/-! Typed consumers of the constructed full operator model. -/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra
open VonNeumannAlgebra
open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.RepresentedBidual

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Direct use of the containing-algebra provider for the canonical inclusion. -/
example (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (StrongDual ℂ M.toStarSubalgebra)) :
    extension M.toStarSubalgebra.subtype.toNonUnitalStarAlgHom F ∈ M :=
  extension_mem_vonNeumannAlgebra M.toStarSubalgebra.subtype.toNonUnitalStarAlgHom
    M (fun a ↦ a.property) F

/-- The reducing inclusion is an actual intertwiner, also for the zero subspace. -/
example (M : VonNeumannAlgebra H) (K : Submodule ℂ H) [CompleteSpace K]
    (hK : Representation.Reduces M.toStarSubalgebra.subtype K)
    (F : StrongDual ℂ (StrongDual ℂ M.toStarSubalgebra)) :
    (extension M.toStarSubalgebra.subtype.toNonUnitalStarAlgHom F).comp K.subtypeL =
      K.subtypeL.comp (extension
        (Representation.restrictToReducing M.toStarSubalgebra.subtype K hK).toNonUnitalStarAlgHom
        F) :=
  intertwines_extension
    (Representation.restrictToReducing M.toStarSubalgebra.subtype K hK).toNonUnitalStarAlgHom
    M.toStarSubalgebra.subtype.toNonUnitalStarAlgHom K.subtypeL
    (fun a ↦ by
      apply ContinuousLinearMap.ext
      intro ξ
      rfl) F

example (M : VonNeumannAlgebra H) (K : Submodule ℂ H) [CompleteSpace K] [Nontrivial K]
    (hK : Representation.Reduces M.toStarSubalgebra.subtype K)
    (hirr : StarAlgHom.IsIrreducible
      (Representation.restrictToReducing M.toStarSubalgebra.subtype K hK)) :
    Function.Surjective
      (Representation.restrictToReducing M.toStarSubalgebra.subtype K hK) :=
  surjective_restrict_to_reducing_of_irreducible M K hK hirr

example (M : VonNeumannAlgebra H) (hM : IsFactor M) (hI : IsTypeI M) :
    ∃ (K : Type u) (instN : NormedAddCommGroup K),
      letI := instN
      ∃ instI : InnerProductSpace ℂ K,
        letI := instI
        ∃ instC : CompleteSpace K,
          letI := instC
          ∃ instNT : Nontrivial K,
            letI := instNT
            ∃ e : M.toStarSubalgebra ≃⋆ₐ[ℂ] (K →L[ℂ] K),
              Isometry e ∧
              (∀ (S : Set M.toStarSubalgebra) (a : M.toStarSubalgebra),
                IsLUB S a → IsLUB (e '' S) (e a)) ∧
              (∀ (S : Set (K →L[ℂ] K)) (a : K →L[ℂ] K),
                IsLUB S a → IsLUB (e.symm '' S) (e.symm a)) := by
  obtain ⟨K, instN, instI, instC, instNT, e, he, hforward, hbackward⟩ :=
    exists_starAlgEquiv_continuousLinearMap_of_isFactor_of_isTypeI
      (M := M) (hM := hM) (hI := hI)
  letI := instN
  letI := instI
  letI := instC
  letI := instNT
  exact ⟨K, instN, instI, instC, instNT, e, he,
    fun S a h ↦ (hforward S a).mp h, fun S a h ↦ (hbackward S a).mp h⟩

example (M : VonNeumannAlgebra H) (hM : IsFactor M) (hI : IsTypeI M) :
    ∃ (K : Type u) (instN : NormedAddCommGroup K),
      letI := instN
      ∃ instI : InnerProductSpace ℂ K,
        letI := instI
        ∃ instC : CompleteSpace K,
          letI := instC
          ∃ instNT : Nontrivial K,
            letI := instNT
            ∃ pi : NonUnitalCStarRepresentation M.toStarSubalgebra K,
              Function.Injective pi ∧ Function.Surjective pi := by
  obtain ⟨K, instN, instI, instC, instNT, pi, hpi, _⟩ :=
    exists_isBoundedOperatorModel_of_isFactor_of_isTypeI (M := M) (hM := hM) (hI := hI)
  letI := instN
  letI := instI
  letI := instC
  letI := instNT
  exact ⟨K, instN, instI, instC, instNT, pi, hpi.1, hpi.surjective⟩

/-- Consumer of the pre-existing GSS theorem: the new input is the actual
model constructed from the intrinsic type I factor hypotheses. -/
example {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (M : VonNeumannAlgebra H) (hM : IsFactor M) (hI : IsTypeI M)
    (hG : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ M.toStarSubalgebra)
      (NormedSpace.geometricStructureClosure ℂ B)) :
    Nonempty (M.toStarSubalgebra ≃⋆ₐ[ℂ] B) := by
  have hone : (1 : M.toStarSubalgebra) ≠ 0 := fun h ↦ hM.1 (congrArg Subtype.val h)
  letI : Nontrivial M.toStarSubalgebra := ⟨⟨1, 0, hone⟩⟩
  obtain ⟨K, instN, instI, instC, instNT, pi, hpi, _⟩ :=
    exists_isBoundedOperatorModel_of_isFactor_of_isTypeI M hM hI
  letI := instN
  letI := instI
  letI := instC
  letI := instNT
  exact nonempty_starAlgEquiv_of_boundedOperatorModel_of_geometricStructure_homeomorph pi hpi hG
