/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceTypeII1
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CARConstruction
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.DiffuseFactor
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.Sakai
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.UnitizationSubquotient

/-!
# Consuming the original CAR trace model in the diffuse test

The Hilbert space, representation, unit vector and II₁ algebra below are
the existing CAR trace objects. Surjectivity of an actual CAR quotient
supplies weak density and cyclicity on exactly that Hilbert space.

The displayed positive map is the precise external input assigned to the
CAR provider. Its CAR restriction and two-sided CAR bimodule identities
are required; normality on all bounded operators is not. This module
does not construct that map, declare it as an axiom, or claim the final
unconditional reverse Sakai theorem. It proves the concrete application
which will consume the provider's actual map once it is supplied.
-/

set_option autoImplicit false
noncomputable section

open Set Topology
open MathlibAnnex.CStarAlgebra
open scoped CStarAlgebra InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

section Unital

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A genuine surjection of a closed same-unit subalgebra onto the existing
CAR completion supplies a non-type-I factor state, provided the assigned
positive CAR bimodule map on the original trace Hilbert space is given.
The proof discharges density, cyclicity, normalization and the II₁ premise
using actual CAR providers; none is a new assumption on the ambient algebra. -/
theorem Representation.exists_factor_state_not_isTypeI_of_surjective_car
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    [PartialOrder D] [StarOrderedRing D]
    (q : D →⋆ₐ[ℂ] CAR.Limit) (hq : Function.Surjective q)
    (E : (CAR.TraceHilbertSpace →L[ℂ] CAR.TraceHilbertSpace) →ₚ[ℂ]
      CAR.traceVonNeumannAlgebra.toStarSubalgebra)
    (hEcar : ∀ a : CAR.Limit, E (CAR.traceRepresentation a) =
      ⟨CAR.traceRepresentation a, CAR.traceRepresentation_mem_traceVonNeumannAlgebra a⟩)
    (hEbi : ∀ (a b : CAR.Limit) (T : CAR.TraceHilbertSpace →L[ℂ] CAR.TraceHilbertSpace),
      E (CAR.traceRepresentation a * T * CAR.traceRepresentation b) =
        (⟨CAR.traceRepresentation a, CAR.traceRepresentation_mem_traceVonNeumannAlgebra a⟩ :
          CAR.traceVonNeumannAlgebra.toStarSubalgebra) * E T *
        ⟨CAR.traceRepresentation b, CAR.traceRepresentation_mem_traceVonNeumannAlgebra b⟩) :
    ∃ (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A),
      (VonNeumannAlgebra.generated
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsFactor ∧
      ¬ (VonNeumannAlgebra.generated
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsTypeI := by
  let M := CAR.traceVonNeumannAlgebra
  let sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra :=
    (CAR.traceRepresentation.comp q).codRestrict M.toStarSubalgebra
      (fun d ↦ CAR.traceRepresentation_mem_traceVonNeumannAlgebra (q d))
  have hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun d : D ↦ ContinuousLinearMapWOT.ofCLM
        (sigma d : CAR.TraceHilbertSpace →L[ℂ] CAR.TraceHilbertSpace))) := by
    intro T hT
    have h := (VonNeumannAlgebra.mem_generated_iff_mem_wotClosure
      CAR.traceRepresentation.range T).mp hT
    apply closure_mono (s := ContinuousLinearMapWOT.ofCLM ''
      (CAR.traceRepresentation.range : Set
        (CAR.TraceHilbertSpace →L[ℂ] CAR.TraceHilbertSpace))) ?_ h
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    obtain ⟨d, rfl⟩ := hq a
    exact ⟨d, rfl⟩
  have hcyclic : DenseRange
      (StarAlgHom.orbitMap (M.toStarSubalgebra.subtype.comp sigma) CAR.traceVector) := by
    apply CAR.denseRange_traceRepresentation_orbit.mono
    rintro _ ⟨a, rfl⟩
    obtain ⟨d, rfl⟩ := hq a
    exact ⟨d, rfl⟩
  have hED (d : D) : E (sigma d : CAR.TraceHilbertSpace →L[ℂ] CAR.TraceHilbertSpace) =
      sigma d := hEcar (q d)
  have hEbiD (d e : D) (T : CAR.TraceHilbertSpace →L[ℂ] CAR.TraceHilbertSpace) :
      E ((sigma d : CAR.TraceHilbertSpace →L[ℂ] CAR.TraceHilbertSpace) * T *
        (sigma e : CAR.TraceHilbertSpace →L[ℂ] CAR.TraceHilbertSpace)) =
      sigma d * E T * sigma e := hEbi (q d) (q e) T
  obtain ⟨_P, phi, hphi, _hPone, _hPD, _hPbi, _hcoeff, _hext, hfactor, hnotI⟩ :=
    Representation.exists_positive_bimodule_non_typeI_factor_extension_of_positive_map
      D M CAR.isTypeII1_traceVonNeumannAlgebra sigma hdense
      CAR.traceVector CAR.norm_traceVector hcyclic E hED hEbiD
  exact ⟨phi, hphi, hfactor, hnotI⟩

end Unital

section NonUnital

variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- A nonzero antiliminal algebra supplies the actual CAR subquotient through
the independent construction. Its closed unitization image and actual
surjective quotient then give a non-type-I factor state of the ambient
unitization, on the same trace test model as above.

The test-model input here is the displayed positive bimodule map.
TypeI.Equivalences supplies CAR.traceBimoduleMap to this theorem. There is no separability or unit
assumption on `A`, and nontriviality is explicit at this obstruction step. -/
theorem IsAntiliminal.exists_factor_state_not_isTypeI_of_trace_map
    (hA : IsAntiliminal A) [Nontrivial A]
    (E : (CAR.TraceHilbertSpace →L[ℂ] CAR.TraceHilbertSpace) →ₚ[ℂ]
      CAR.traceVonNeumannAlgebra.toStarSubalgebra)
    (hEcar : ∀ a : CAR.Limit, E (CAR.traceRepresentation a) =
      ⟨CAR.traceRepresentation a, CAR.traceRepresentation_mem_traceVonNeumannAlgebra a⟩)
    (hEbi : ∀ (a b : CAR.Limit) (T : CAR.TraceHilbertSpace →L[ℂ] CAR.TraceHilbertSpace),
      E (CAR.traceRepresentation a * T * CAR.traceRepresentation b) =
        (⟨CAR.traceRepresentation a, CAR.traceRepresentation_mem_traceVonNeumannAlgebra a⟩ :
          CAR.traceVonNeumannAlgebra.toStarSubalgebra) * E T *
        ⟨CAR.traceRepresentation b, CAR.traceRepresentation_mem_traceVonNeumannAlgebra b⟩) :
    ∃ (phi : Unitization ℂ A →L[ℂ] ℂ)
        (hphi : phi ∈ stateSpace (Unitization ℂ A)),
      (VonNeumannAlgebra.generated
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsFactor ∧
      ¬ (VonNeumannAlgebra.generated
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsTypeI := by
  obtain ⟨D, hD, q, hq⟩ := hA.exists_car_subquotient
  letI : IsClosed (D : Set A) := hD
  obtain ⟨F, hF, _e, r, hr, _hinclude, _hquotient, _horiginal⟩ :=
    D.exists_unitization_subquotient q hq
  letI : IsClosed (F : Set (Unitization ℂ A)) := hF
  letI := Subtype.starOrderedRing (𝕜 := ℂ) F
  exact Representation.exists_factor_state_not_isTypeI_of_surjective_car
    F r hr E hEcar hEbi

end NonUnital

end MathlibAnnex.Analysis.CStarAlgebra
