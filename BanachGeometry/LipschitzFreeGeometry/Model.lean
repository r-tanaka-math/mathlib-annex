/-
Derived from openai/math@4eaee87548250b2682affda7d05d947c05554bae.
Original: lean/OAI/Analysis/LipschitzEquivalence/Model.lean
Apache-2.0; see LICENSES/OPENAI_MATH_APACHE_2_0.txt and THIRD_PARTY_NOTICES.md.
Modified: reduced port, documented proof repairs, mathematical namespace/import migration.
Exact original/port/current lineage is in the L02 provenance registry.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

namespace BanachGeometry

universe uE uF

noncomputable section
namespace LipschitzFreeGeometry

abbrev RealL2 := lp (fun _ : ℕ => ℝ) 2
abbrev C0L2 := ZeroAtInftyContinuousMap ℕ RealL2

structure SeparableRealBanach where
  Carrier : Type
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [normedSpace : NormedSpace ℝ Carrier]
  [completeSpace : CompleteSpace Carrier]
  [separableSpace : TopologicalSpace.SeparableSpace Carrier]

attribute [instance] SeparableRealBanach.normedAddCommGroup
  SeparableRealBanach.normedSpace SeparableRealBanach.completeSpace
  SeparableRealBanach.separableSpace

def ContainsLinearCopy (E : Type uE) (F : Type uF) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∃ (T : E →L[ℝ] F) (a : ℝ), 0 < a ∧ ∀ x : E, a * ‖x‖ ≤ ‖T x‖

end LipschitzFreeGeometry
end

end BanachGeometry
