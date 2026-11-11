/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.Factor
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.TypeIFactorRigidity

/-!
# Intrinsic type I factors supply the existing bounded-operator model

The factor model is constructed from `IsFactor` and `IsTypeI`. This bridge
then supplies the pre-existing `IsBoundedOperatorModel` predicate for the
same algebra subtype. No new competing model predicate is introduced and
the converse direction is not smuggled in as a representation parameter.
-/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- An intrinsic type I factor has a faithful literal full-range bounded
operator model, in the existing geometric-structure interface. -/
theorem exists_isBoundedOperatorModel_of_isFactor_of_isTypeI
    (M : VonNeumannAlgebra H) (hM : VonNeumannAlgebra.IsFactor M)
    (hI : VonNeumannAlgebra.IsTypeI M) :
    ∃ (K : Type u) (instN : NormedAddCommGroup K),
      letI := instN
      ∃ instI : InnerProductSpace ℂ K,
        letI := instI
        ∃ instC : CompleteSpace K,
          letI := instC
          ∃ instNT : Nontrivial K,
            letI := instNT
            ∃ pi : NonUnitalCStarRepresentation M.toStarSubalgebra K,
              IsBoundedOperatorModel pi ∧ Isometry pi := by
  obtain ⟨K, instN, instI, instC, instNT, e, he, _, _⟩ :=
    VonNeumannAlgebra.exists_starAlgEquiv_continuousLinearMap_of_isFactor_of_isTypeI
      M hM hI
  letI := instN
  letI := instI
  letI := instC
  letI := instNT
  let pi : NonUnitalCStarRepresentation M.toStarSubalgebra K := e.toNonUnitalStarAlgHom
  refine ⟨K, instN, instI, instC, instNT, pi, ⟨e.injective, ?_⟩, he⟩
  apply SetLike.ext
  intro T
  exact ⟨fun _ => trivial, fun _ => (NonUnitalStarAlgHom.mem_range pi).mpr (e.surjective T)⟩

end MathlibAnnex.Analysis.CStarAlgebra
