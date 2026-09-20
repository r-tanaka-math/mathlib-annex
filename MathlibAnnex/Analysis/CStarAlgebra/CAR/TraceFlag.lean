import MathlibAnnex.Analysis.CStarAlgebra.CAR.Trace
import MathlibAnnex.Analysis.CStarAlgebra.CAR.AtomicSource
import MathlibAnnex.Analysis.CStarAlgebra.GNS.TracialProjection
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Trace of the fixed transported flags

No automorphism is reselected, and no trace-invariance axiom for the chosen
automorphisms is needed. The exact initial/final shell identities force the
trace of every transported flag by a finite telescoping induction.
-/

set_option autoImplicit false

open Filter Topology

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra

private theorem trace_transportedFlag_sub (family : RepresentativeShellFamily)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
    trace (transportedFlag family i n) - trace (transportedFlag family i (n + 1)) =
      trace (rootFlag n) - trace (rootFlag (n + 1)) := by
  rw [← map_sub, ← map_sub, ← representativeLink_initial family i n,
    ← representativeLink_final family i n]
  exact trace_mul_comm _ _

/-- The trace of a transported flag agrees with the trace of the root flag. -/
theorem trace_transportedFlag_eq_trace_rootFlag (family : RepresentativeShellFamily)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
    trace (transportedFlag family i n) = trace (rootFlag n) := by
  induction n with
  | zero => rw [transportedFlag_zero, rootFlag_zero]
  | succ n ih =>
      have h := trace_transportedFlag_sub family i n
      rw [ih] at h
      have h' := congrArg (fun z : ℂ ↦ trace (rootFlag n) - z) h
      simpa only [sub_sub_cancel] using h'

@[simp]
theorem trace_transportedFlag (family : RepresentativeShellFamily)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (n : ℕ) :
    trace (transportedFlag family i n) = (2 ^ n : ℂ)⁻¹ := by
  rw [trace_transportedFlag_eq_trace_rootFlag, trace_rootFlag]

private theorem tendsto_inv_pow_two_atTop_nhds_zero :
    Tendsto (fun n : ℕ ↦ (2 ^ n : ℝ)⁻¹) atTop (nhds 0) := by
  simp_rw [← inv_pow]
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)

universe v
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem tendsto_rootFlag_orbit_zero (σ : Representation Limit H) (ξ : H)
    (hξ : ∀ a, Representation.vectorFunctional σ ξ a = trace a) (b : Limit) :
    Tendsto (fun n ↦ σ (rootFlag n) (σ b ξ)) atTop (nhds 0) := by
  apply tendsto_projection_orbit_zero tracePositive trace_mul_comm σ ξ hξ
    rootFlag isStarProjection_rootFlag (fun n ↦ (2 ^ n : ℝ)⁻¹)
  · intro n
    simp only [tracePositive_apply, trace_rootFlag, Complex.ofReal_inv,
      Complex.ofReal_pow, Complex.ofReal_ofNat]
  · exact tendsto_inv_pow_two_atTop_nhds_zero

theorem tendsto_transportedFlag_orbit_zero (family : RepresentativeShellFamily)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit)
    (σ : Representation Limit H) (ξ : H)
    (hξ : ∀ a, Representation.vectorFunctional σ ξ a = trace a) (b : Limit) :
    Tendsto (fun n ↦ σ (transportedFlag family i n) (σ b ξ)) atTop (nhds 0) := by
  apply tendsto_projection_orbit_zero tracePositive trace_mul_comm σ ξ hξ
    (transportedFlag family i) (isStarProjection_transportedFlag family i)
    (fun n ↦ (2 ^ n : ℝ)⁻¹)
  · intro n
    simp only [tracePositive_apply, trace_transportedFlag, Complex.ofReal_inv,
      Complex.ofReal_pow, Complex.ofReal_ofNat]
  · exact tendsto_inv_pow_two_atTop_nhds_zero

end MathlibAnnex.CStarAlgebra.CAR
