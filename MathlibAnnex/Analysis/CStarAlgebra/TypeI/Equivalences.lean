/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceBimoduleMap
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CARTraceTest

/-!
# Internal type I, the literal bidual, and GCR

The concrete CAR trace bimodule map supplies the previously displayed input
to the diffuse factor test. Failure of the internal quotient condition then
produces an actual proper closed-ideal quotient and a non-type-I factor
representation of its formal unitization. The existing restriction and
surjective-quotient diagram contradict type I of the original Banach bidual.

The internal/GCR equivalence is reused from its independent CAR-subquotient
proof. That provider does not depend on this module or on reverse Sakai.
No positivity map, separability, unit, or nontriviality is an input to the
classification results. Nontriviality is obtained only for the proper
quotient in the contradiction. `IsTypeIBidual` retains its established
all-state realization and its proved literal `StrongDual` Arens criterion.
-/

set_option autoImplicit false
noncomputable section

open Set
open MathlibAnnex.CStarAlgebra
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- Every nonzero antiliminal C-star algebra admits a non-type-I factor
state of its formal unitization. The concrete map on the existing CAR
trace Hilbert space is supplied here, with no extra input to this theorem. -/
theorem IsAntiliminal.exists_factor_state_not_isTypeI
    (hA : IsAntiliminal A) [Nontrivial A] :
    ∃ (phi : Unitization ℂ A →L[ℂ] ℂ)
        (hphi : phi ∈ stateSpace (Unitization ℂ A)),
      (VonNeumannAlgebra.generated
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsFactor ∧
      ¬ (VonNeumannAlgebra.generated
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsTypeI := by
  exact hA.exists_factor_state_not_isTypeI_of_trace_map
    CAR.traceBimoduleMap CAR.traceBimoduleMap_traceRepresentation
    CAR.traceBimoduleMap_mul_mul

/-- Reverse Sakai for an arbitrary nonunital, possibly nonseparable C-star
algebra, including the zero algebra. The test representation is constructed
from a proper quotient, not assumed as a classification hypothesis. -/
theorem IsTypeIBidual.isInternalTypeI (hA : IsTypeIBidual A) :
    IsInternalTypeI A := by
  by_contra hnot
  obtain ⟨J, hJ, hproper, hanti⟩ := not_isInternalTypeI_iff.mp hnot
  letI : Nontrivial (ClosedIdealQuotient.Quotient J hJ) :=
    ClosedIdealQuotient.nontrivial_quotient J hJ hproper
  obtain ⟨phi, hphi, hfactor, hnotI⟩ :=
    hanti.exists_factor_state_not_isTypeI
  let rho := (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom
  exact not_isTypeIBidual_of_not_isTypeI_quotient
    (ClosedIdealQuotient.mkHom J hJ)
    (ClosedIdealQuotient.mkHom_surjective J hJ) rho hfactor hnotI hA

/-- The independent internal quotient condition is equivalent to type I
of the actual Banach bidual, through its established enveloping realization. -/
theorem isInternalTypeI_iff_isTypeIBidual :
    IsInternalTypeI A ↔ IsTypeIBidual A :=
  ⟨IsInternalTypeI.isTypeIBidual, IsTypeIBidual.isInternalTypeI⟩

/-- Type I of the literal bidual implies the existing pure-GNS
compact-containment condition through the independent internal theorem. -/
theorem IsTypeIBidual.isGCR (hA : IsTypeIBidual A) : IsGCR A :=
  hA.isInternalTypeI.isGCR

/-- The bidual condition and the independently defined GCR condition are
equivalent for arbitrary nonunital C-star algebras. Together with the existing
internal/GCR theorem and the preceding internal/bidual theorem, this gives
the three independent characterizations without a new bundled predicate. -/
theorem isTypeIBidual_iff_isGCR : IsTypeIBidual A ↔ IsGCR A :=
  isInternalTypeI_iff_isTypeIBidual.symm.trans isInternalTypeI_iff_isGCR

end MathlibAnnex.Analysis.CStarAlgebra
