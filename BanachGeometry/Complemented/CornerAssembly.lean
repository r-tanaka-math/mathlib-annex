import BanachGeometry.Complemented.Localization
import BanachGeometry.WeakSequences.L1Shifts
import BanachGeometry.AlmostIsometric.CriterionAssembly

/-! Conditional corner localization and its connection to the fixed pair.
The joint corner estimate hcorner and finite-head exclusions hheads are
ordinary theorem hypotheses here. Corner proves the joint estimate, and
HeadSplitting derives finite-head exclusions from H3/H4. -/

noncomputable section
namespace BanachGeometry
namespace Localization
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (V : ℕ → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]

/-- Exact two-index residual in R6 Lemma 5.1; the two tail operations act
on different spaces and may not be interchanged. -/
def JointCorner (T : C0Sum V →L[ℝ] L1Shifts.F E) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ m₀ n₀ : ℕ,
    ∀ m, m₀ ≤ m → ∀ n, n₀ ≤ n →
      ‖(L1Tails.tail (fun _ : ℕ => E) m).comp (T.comp (C0Sum.tailCLM V n))‖ < η

theorem finite_head_of_joint_corner
    (J : L1Shifts.F E →L[ℝ] C0Sum V) (T : C0Sum V →L[ℝ] L1Shifts.F E)
    (hTJ : T.comp J = ContinuousLinearMap.id ℝ (L1Shifts.F E))
    (hcorner : JointCorner E V T) :
    ∃ n : ℕ, ContainsComplementedCopy (L1Shifts.F E) (C0Sum.FiniteHead V n) := by
  have hden : 0 < ‖J‖ + 1 := by positivity
  obtain ⟨m, n, hmn⟩ := hcorner ((‖J‖ + 1)⁻¹) (inv_pos.mpr hden)
  have hc := hmn m le_rfl n le_rfl
  have hsmall :
      ‖(L1Shifts.downCLM E m).comp (T.comp (C0Sum.tailCLM V n))‖ * ‖J‖ < 1 := by
    rw [L1Shifts.norm_down_comp]
    calc
      _ ≤ (‖J‖ + 1)⁻¹ * ‖J‖ := mul_le_mul_of_nonneg_right hc.le (norm_nonneg J)
      _ = ‖J‖ / (‖J‖ + 1) := by ring
      _ < 1 := (div_lt_iff₀ hden).2 (by linarith)
  exact ⟨n, finite_head_localization V J T hTJ
    (L1Shifts.upCLM E m) (L1Shifts.downCLM E m)
    (L1Shifts.down_up E m) (L1Shifts.opNorm_upCLM_le E m) n hsmall⟩

theorem no_complemented_of_corner_and_heads
    (hcorner : ∀ T : C0Sum V →L[ℝ] L1Shifts.F E, JointCorner E V T)
    (hheads : ∀ n : ℕ, ¬ ContainsComplementedCopy (L1Shifts.F E) (C0Sum.FiniteHead V n)) :
    ¬ ContainsComplementedCopy (L1Shifts.F E) (C0Sum V) := by
  rintro ⟨J, T, hTJ⟩
  obtain ⟨n, hn⟩ := finite_head_of_joint_corner E V J T hTJ (hcorner T)
  exact hheads n hn

end Localization

namespace AlmostIsometricFamily
/-- Assemble the fixed pair from h2, a joint corner estimate hcorner and
finite-head exclusions hheads. These are explicit local hypotheses.
Corner.jointCorner supplies hcorner; HeadSplitting.no_complemented_finiteHead
supplies hheads from coordinate splitting H3 and finite-sum exclusion H4. -/
theorem exists_almostIsometric_nonisomorphic_pair_of_corner_and_head_exclusions (d : AlmostIsometricFamily) (h2 : d.HasContractivelyComplementedCopy)
    (hcorner : ∀ T : d.FixedY →L[ℝ] L1C0L2,
      Localization.JointCorner C0L2 (fun k => d.Z k) T)
    (hheads : ∀ n : ℕ, ¬ ContainsComplementedCopy L1C0L2
      (C0Sum.FiniteHead (fun k => d.Z k) n)) : ExistsAlmostIsometricNonisomorphicPair := by
  apply d.exists_almostIsometric_nonisomorphic_pair_of_complemented_obstruction h2
  exact Localization.no_complemented_of_corner_and_heads C0L2 (fun k => d.Z k) hcorner hheads

end AlmostIsometricFamily
end BanachGeometry
