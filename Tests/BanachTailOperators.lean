import BanachGeometry.AlmostIsometric.Existence
import BanachGeometry.AlmostIsometric.Consequences
import BanachGeometry.LipschitzFreeSpace.PositiveTailLocality

/-! Direct consumer statements for the actual Banach tail operators. Elaboration and
axiom evidence are recorded in external receipts, separately from these source types.
Execution evidence is recorded in the external receipts. -/

noncomputable section
open BanachGeometry

example (V : ℕ → Type*) [∀ n, NormedAddCommGroup (V n)]
    [∀ n, NormedSpace ℝ (V n)] [∀ n, CompleteSpace (V n)] :
    CompleteSpace (C0Sum V) := inferInstance

example (V : ℕ → Type*) [∀ n, NormedAddCommGroup (V n)]
    [∀ n, NormedSpace ℝ (V n)] [∀ n, TopologicalSpace.SeparableSpace (V n)] :
    TopologicalSpace.SeparableSpace (C0Sum V) := inferInstance

example (d : AlmostIsometricFamily) : CompleteSpace d.FixedX := inferInstance
example (d : AlmostIsometricFamily) : CompleteSpace d.FixedY := inferInstance
example (d : AlmostIsometricFamily) : TopologicalSpace.SeparableSpace d.FixedY := inferInstance
example (d : AlmostIsometricFamily) : Nontrivial d.FixedY := inferInstance
example (d : AlmostIsometricFamily) :
    AlmostIsometricAtEveryTolerance d.fixedXBanach d.fixedYBanach := d.almostIsometricAtEveryTolerance_fixedXBanach_fixedYBanach

example (V : ℕ → Type*) [∀ n, NormedAddCommGroup (V n)]
    [∀ n, NormedSpace ℝ (V n)] (x : L1Sum V) :
    Filter.Tendsto (fun m => ‖L1Tails.tail V m x‖) Filter.atTop (nhds 0) :=
  L1Tails.tendsto_norm_tail V x

#print axioms isClosed_c0Submodule
#print axioms c0SumCompleteSpace
#print axioms C0Sum.tendsto_head
#print axioms C0Sum.separableSpace
#print axioms l1SeparableSpace
#print axioms AlmostIsometricFamily.fixedXBanach
#print axioms AlmostIsometricFamily.almostIsometricAtEveryTolerance_fixedXBanach_fixedYBanach
#print axioms L1Tails.tendsto_norm_tail
#print axioms L1Tails.hasUniformlySmallTails_of_isCompact
#print axioms L1Tails.hasUniformlySmallTails_of_subsequence
#print axioms L1Tails.tendsto_opNorm_tail_comp_of_weaklyCauchy_subseq
