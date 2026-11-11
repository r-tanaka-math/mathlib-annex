/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CARConstruction
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CARObstruction

/-!
# Internal type I and GCR for arbitrary C-star algebras

The converse uses the constructed CAR subquotient of every nonzero antiliminal
algebra, together with the independently proved quotient and closed-subalgebra
permanence of GCR. A failure of the internal condition gives an actual proper
closed-ideal quotient to which that construction applies.

The accepted forward proof remains in `GCRCharacterization`; this module adds
the converse above the CAR obstruction without introducing an import cycle.
No bidual classification or final Glimm--Sakai equivalence is used.
-/

set_option autoImplicit false
noncomputable section

open Set
open MathlibAnnex.CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- A nonzero antiliminal algebra cannot be GCR, by its constructed actual
closed-subalgebra quotient onto the fixed CAR algebra. -/
theorem IsAntiliminal.not_isGCR (hA : IsAntiliminal A) [Nontrivial A] : ¬ IsGCR A := by
  obtain ⟨D, hD, q, hq⟩ := hA.exists_car_subquotient
  letI : IsClosed (D : Set A) := hD
  exact CAR.not_isGCR_of_subquotient D q hq

/-- GCR implies the independent internal quotient condition. This proof works
for arbitrary nonunital and nonseparable algebras, including the zero algebra. -/
theorem IsGCR.isInternalTypeI (hA : IsGCR A) : IsInternalTypeI A := by
  by_contra h
  obtain ⟨J, hJ, hproper, hanti⟩ := not_isInternalTypeI_iff.mp h
  letI : NonUnitalCStarAlgebra (ClosedIdealQuotient.Quotient J hJ) :=
    HomKernelQuotient.instNonUnitalCStarAlgebra (ClosedIdealQuotient.representation J hJ)
  letI : Nontrivial (ClosedIdealQuotient.Quotient J hJ) :=
    ClosedIdealQuotient.nontrivial_quotient J hJ hproper
  exact hanti.not_isGCR (hA.closed_ideal_quotient J hJ)

/-- The internal definition and the actual pure-GNS compact-containment
definition are equivalent, without unit or separability hypotheses. -/
theorem isInternalTypeI_iff_isGCR : IsInternalTypeI A ↔ IsGCR A :=
  ⟨IsInternalTypeI.isGCR, IsGCR.isInternalTypeI⟩

end MathlibAnnex.Analysis.CStarAlgebra
