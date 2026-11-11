/-
New typed consumers; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CARTraceTest

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open MathlibAnnex.CStarAlgebra
open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra InnerProduct

universe u

-- This consumes the actual existing II₁ model, with no auxiliary-map input.
example {p : CAR.traceVonNeumannAlgebra.toStarSubalgebra}
    (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : ℕ → CAR.traceVonNeumannAlgebra.toStarSubalgebra,
      (∀ n, IsStarProjection (q n) ∧ q n ≤ p ∧ ‖q n‖ = 1) ∧
      Pairwise (fun i j ↦ q i * q j = 0) ∧
      ContinuousLinearMap.StronglyConverges
        (fun n ↦ (q n : CAR.TraceHilbertSpace →L[ℂ] CAR.TraceHilbertSpace)) atTop 0 := by
  exact CAR.isTypeII1_traceVonNeumannAlgebra.exists_stronglyConverges_zero_projection_sequence
    hp hp0

-- The zero source is handled independently; it never enters a nonzero test.
example {A : Type u} [NonUnitalCStarAlgebra A] [Subsingleton A] :
    IsInternalTypeI A ∧ IsGCR A ∧ IsTypeIBidual A := by
  have hA : IsInternalTypeI A := isInternalTypeI_of_subsingleton
  exact ⟨hA, hA.isGCR, hA.isTypeIBidual⟩

section SuppliedTraceMap

-- These are explicit provider inputs. No concrete E is declared or presumed
-- to have arrived, and these consumers are not unconditional final endpoints.
variable
    (E : (CAR.TraceHilbertSpace →L[ℂ] CAR.TraceHilbertSpace) →ₚ[ℂ]
      CAR.traceVonNeumannAlgebra.toStarSubalgebra)
    (hEcar : ∀ a : CAR.Limit, E (CAR.traceRepresentation a) =
      ⟨CAR.traceRepresentation a, CAR.traceRepresentation_mem_traceVonNeumannAlgebra a⟩)
    (hEbi : ∀ (a b : CAR.Limit) (T : CAR.TraceHilbertSpace →L[ℂ] CAR.TraceHilbertSpace),
      E (CAR.traceRepresentation a * T * CAR.traceRepresentation b) =
        (⟨CAR.traceRepresentation a, CAR.traceRepresentation_mem_traceVonNeumannAlgebra a⟩ :
          CAR.traceVonNeumannAlgebra.toStarSubalgebra) * E T *
        ⟨CAR.traceRepresentation b, CAR.traceRepresentation_mem_traceVonNeumannAlgebra b⟩)

include E hEcar hEbi

example {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)] [PartialOrder D] [StarOrderedRing D]
    (q : D →⋆ₐ[ℂ] CAR.Limit) (hq : Function.Surjective q) :
    ∃ (phi : A →L[ℂ] ℂ) (hphi : phi ∈ MathlibAnnex.Analysis.CStarAlgebra.stateSpace A),
      (VonNeumannAlgebra.generated
        (MathlibAnnex.Analysis.CStarAlgebra.positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsFactor ∧
      ¬ (VonNeumannAlgebra.generated
        (MathlibAnnex.Analysis.CStarAlgebra.positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsTypeI := by
  exact Representation.exists_factor_state_not_isTypeI_of_surjective_car
    D q hq E hEcar hEbi

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

example {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
    (hA : IsAntiliminal A) :
    ∃ (phi : Unitization ℂ A →L[ℂ] ℂ)
        (hphi : phi ∈ MathlibAnnex.Analysis.CStarAlgebra.stateSpace (Unitization ℂ A)),
      (VonNeumannAlgebra.generated
        (MathlibAnnex.Analysis.CStarAlgebra.positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsFactor ∧
      ¬ (VonNeumannAlgebra.generated
        (MathlibAnnex.Analysis.CStarAlgebra.positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsTypeI := by
  exact hA.exists_factor_state_not_isTypeI_of_trace_map E hEcar hEbi

-- End-to-end conditional wiring: the supplied A W03 quotient and CAR
-- subquotient, the actual trace test, the unitization restriction and the
-- literal-bidual quotient transport are consumed here. The missing A W04
-- construction is exactly E with the two displayed identities above.
example {A : Type u} [NonUnitalCStarAlgebra A]
    (hA : ¬ IsInternalTypeI A) (hbidual : IsTypeIBidual A) : False := by
  obtain ⟨J, hJ, hproper, hanti⟩ := not_isInternalTypeI_iff.mp hA
  letI : Nontrivial (ClosedIdealQuotient.Quotient J hJ) :=
    ClosedIdealQuotient.nontrivial_quotient J hJ hproper
  obtain ⟨phi, hphi, hfactor, hnotI⟩ :=
    hanti.exists_factor_state_not_isTypeI_of_trace_map E hEcar hEbi
  let rho := (MathlibAnnex.Analysis.CStarAlgebra.positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom
  exact not_isTypeIBidual_of_not_isTypeI_quotient (ClosedIdealQuotient.mkHom J hJ)
    (ClosedIdealQuotient.mkHom_surjective J hJ) rho hfactor hnotI hbidual

end SuppliedTraceMap
