import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceVonNeumann
import MathlibAnnex.Analysis.CStarAlgebra.CAR.SeparableFaithful
import MathlibAnnex.Analysis.CStarAlgebra.AtomicConstruction.GeneratedExt
import MathlibAnnex.Analysis.VonNeumannAlgebra.TracialState
import MathlibAnnex.Analysis.VonNeumannAlgebra.Bicommutant
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology

/-!
# Weak closure of the same CAR shell-family model

The existing shell sums place the added generators in the CAR double
commutant. Norm generation then places the entire represented target there.
Since the target contains the original represented CAR algebra, the two
double commutants, strong closures, and weak closures agree.

Traciality of the same vector functional is extended one variable at a time
by weak continuity of matrix coefficients. Faithfulness uses the existing
tracial cyclic-vector theorem.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped CStarAlgebra ComplexOrder InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra

local notation "toSOT" => ContinuousLinearMap.toPointwiseConvergenceCLM
  ℂ (RingHom.id ℂ) TraceHilbertSpace TraceHilbertSpace
local notation "toWOT" =>
  (ContinuousLinearMapWOT.ofCLM : (TraceHilbertSpace →L[ℂ] TraceHilbertSpace) →
    (TraceHilbertSpace →WOT[ℂ] TraceHilbertSpace))

/-- Every shell generator is a strong limit of operators in the fixed CAR image. -/
theorem traceModelRepresentation_shellFamilyGenerator_mem_traceVonNeumannAlgebra
    (family : RepresentativeShellFamily)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    traceModelRepresentation family (shellFamilyGenerator family i) ∈
      traceVonNeumannAlgebra := by
  apply VonNeumannAlgebra.mem_of_stronglyConverges traceVonNeumannAlgebra
    (f := ContinuousLinearMap.partialSum
      (fun n ↦ traceRepresentation ((representativeShellData family i).link n)))
    (l := atTop) ?_ (stronglyConverges_traceRepresentation_shell_sums family i).1
  intro N
  change (∑ n ∈ Finset.range N,
    traceRepresentation ((representativeShellData family i).link n)) ∈
      traceVonNeumannAlgebra.toStarSubalgebra
  exact _root_.sum_mem (fun n _ ↦ traceRepresentation_mem_traceVonNeumannAlgebra _)

set_option maxHeartbeats 800000 in
/-- Norm generation transfers the shell-generator inclusions to the entire
unchanged shell-family target. -/
theorem traceModelRepresentation_mem_traceVonNeumannAlgebra
    (family : RepresentativeShellFamily) (a : ShellFamilyTarget family) :
    traceModelRepresentation family a ∈ traceVonNeumannAlgebra := by
  let C : StarSubalgebra ℂ (ShellFamilyTarget family) :=
    traceVonNeumannAlgebra.toStarSubalgebra.comap (traceModelRepresentation family)
  have hclosed : IsClosed (C : Set (ShellFamilyTarget family)) :=
    (VonNeumannAlgebra.isClosed traceVonNeumannAlgebra).preimage
      (map_continuous (traceModelRepresentation family))
  have hsource (b : Limit) : shellFamilySourceHom family b ∈ C := by
    change traceModelRepresentation family (shellFamilySourceHom family b) ∈
      traceVonNeumannAlgebra
    rw [traceModelRepresentation_shellFamilySourceHom]
    exact traceRepresentation_mem_traceVonNeumannAlgebra b
  have hgenerator (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
      shellFamilyGenerator family i ∈ C :=
    traceModelRepresentation_shellFamilyGenerator_mem_traceVonNeumannAlgebra family i
  have htop : C = ⊤ :=
    AtomicConstruction.eq_top_of_source_mem_of_generator_mem
      selectedAtomicRepresentation (shellFamilyLinks family) C hclosed hsource hgenerator
  have ha : a ∈ C := by rw [htop]; trivial
  exact ha

/-- The exact CAR image lies inside the exact shell-family image. -/
theorem traceRepresentation_range_le_traceModelRepresentation_range
    (family : RepresentativeShellFamily) :
    traceRepresentation.range ≤ (traceModelRepresentation family).range := by
  rintro _ ⟨a, rfl⟩
  exact ⟨shellFamilySourceHom family a,
    traceModelRepresentation_shellFamilySourceHom family a⟩

private theorem generated_traceModelRepresentation_range
    (family : RepresentativeShellFamily) :
    VonNeumannAlgebra.generated (traceModelRepresentation family).range =
      traceVonNeumannAlgebra := by
  apply le_antisymm
  · apply VonNeumannAlgebra.generated_le
    rintro _ ⟨a, rfl⟩
    exact traceModelRepresentation_mem_traceVonNeumannAlgebra family a
  · apply VonNeumannAlgebra.generated_le
    intro T hT
    exact VonNeumannAlgebra.subset_generated (traceModelRepresentation family).range
      (traceRepresentation_range_le_traceModelRepresentation_range family hT)

/-- The raw double commutant agrees for every already fixed shell family. -/
theorem traceModelRepresentation_bicommutant_eq (family : RepresentativeShellFamily) :
    Set.centralizer (Set.centralizer (Set.range (traceModelRepresentation family))) =
      (traceVonNeumannAlgebra : Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)) := by
  calc
    _ = (VonNeumannAlgebra.generated (traceModelRepresentation family).range :
        Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)) := rfl
    _ = _ := congrArg
      (fun M : VonNeumannAlgebra TraceHilbertSpace ↦ (M : Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)))
      (generated_traceModelRepresentation_range family)

/-- The concrete inclusion chain for the single selected counterexample. -/
theorem separableCounterexampleRepresentation_range_sandwich :
    traceRepresentation.range ≤ separableCounterexampleRepresentation.range ∧
    separableCounterexampleRepresentation.range ≤
      traceVonNeumannAlgebra.toStarSubalgebra := by
  refine ⟨traceRepresentation_range_le_traceModelRepresentation_range
    homogeneityShellFamily, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact traceModelRepresentation_mem_traceVonNeumannAlgebra homogeneityShellFamily a

/-- The original selected faithful representation has precisely the CAR
trace double commutant on its original Hilbert space. -/
theorem separableCounterexampleRepresentation_bicommutant_eq :
    Set.centralizer (Set.centralizer (Set.range separableCounterexampleRepresentation)) =
      (traceVonNeumannAlgebra : Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)) :=
  traceModelRepresentation_bicommutant_eq homogeneityShellFamily

/-- Strong density is expressed in the standard pointwise-convergence type copy. -/
theorem closure_sot_traceModelRepresentation_range (family : RepresentativeShellFamily) :
    closure (toSOT '' Set.range (traceModelRepresentation family)) =
      toSOT '' (traceVonNeumannAlgebra : Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)) := by
  apply Set.Subset.antisymm
  · intro T hT
    refine ⟨T, ?_, rfl⟩
    rw [← generated_traceModelRepresentation_range family]
    exact (VonNeumannAlgebra.mem_generated_iff_mem_sotClosure
      (traceModelRepresentation family).range T).mpr hT
  · rintro _ ⟨T, hT, rfl⟩
    apply (VonNeumannAlgebra.mem_generated_iff_mem_sotClosure
      (traceModelRepresentation family).range T).mp
    rwa [generated_traceModelRepresentation_range family]

/-- Weak density is expressed in the standard weak-operator type copy. -/
theorem closure_wot_traceModelRepresentation_range (family : RepresentativeShellFamily) :
    closure (toWOT '' Set.range (traceModelRepresentation family)) =
      toWOT '' (traceVonNeumannAlgebra : Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)) := by
  apply Set.Subset.antisymm
  · intro T hT
    refine ⟨T.toCLM, ?_, ContinuousLinearMapWOT.ofCLM_toCLM T⟩
    rw [← generated_traceModelRepresentation_range family]
    apply (VonNeumannAlgebra.mem_generated_iff_mem_wotClosure
      (traceModelRepresentation family).range T.toCLM).mpr
    change toWOT T.toCLM ∈ closure (toWOT '' Set.range (traceModelRepresentation family))
    simpa only [ContinuousLinearMapWOT.ofCLM_toCLM] using hT
  · rintro _ ⟨T, hT, rfl⟩
    apply (VonNeumannAlgebra.mem_generated_iff_mem_wotClosure
      (traceModelRepresentation family).range T).mp
    rwa [generated_traceModelRepresentation_range family]

/-- The original vector functional is tracial on the entire weak closure. -/
theorem traceVonNeumannTrace_mul_comm (S T : traceVonNeumannAlgebra.toStarSubalgebra) :
    traceVonNeumannTrace (S * T) = traceVonNeumannTrace (T * S) := by
  apply VonNeumannAlgebra.vectorFunctional_mul_comm_of_wotDense
    traceVonNeumannAlgebra (Set.range traceRepresentation) traceVector
    (P := S.val) (Q := T.val) (hP := S.property) (hQ := T.property)
  · intro U hU
    exact (VonNeumannAlgebra.mem_generated_iff_mem_wotClosure traceRepresentation.range U).mp hU
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    change inner ℂ traceVector ((traceRepresentation a * traceRepresentation b) traceVector) =
      inner ℂ traceVector ((traceRepresentation b * traceRepresentation a) traceVector)
    rw [← map_mul, ← map_mul, inner_traceVector_traceRepresentation,
      inner_traceVector_traceRepresentation]
    exact trace_mul_comm a b

/-- Faithfulness of the vector trace on the weak closure. -/
theorem traceVonNeumannTrace_star_mul_self_eq_zero_iff
    (T : traceVonNeumannAlgebra.toStarSubalgebra) :
    traceVonNeumannTrace (star T * T) = 0 ↔ T = 0 := by
  have h := VonNeumannAlgebra.vectorFunctional_star_mul_self_eq_zero_iff
    traceVonNeumannAlgebra traceVector norm_traceVector
    (fun P hP Q hQ ↦ traceVonNeumannTrace_mul_comm ⟨P, hP⟩ ⟨Q, hQ⟩)
    denseRange_traceVonNeumannAlgebra_orbit T.property
  exact h.trans ⟨fun hT ↦ Subtype.ext hT, fun hT ↦ congrArg Subtype.val hT⟩

end MathlibAnnex.CStarAlgebra.CAR
