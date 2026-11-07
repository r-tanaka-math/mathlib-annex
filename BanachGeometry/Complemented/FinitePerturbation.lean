import BanachGeometry.WeakSequences.L1Shifts
import BanachGeometry.WeakSequences.OperatorTails
import BanachGeometry.Complemented.Factorization
import Mathlib.Analysis.Normed.Operator.Prod

open scoped ENNReal

/-! R6 5.3: remove the separable-dual factor by an actual homogeneous ℓ₁
shift and Neumann repair. The separable-dual assumption on D is exactly the
mathematical hypothesis of the lemma and is given as an explicit parameter. -/

noncomputable section
open Filter TopologicalSpace
namespace BanachGeometry
namespace FinitePerturbation
variable (E G D : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem no_complemented_l1 (hG : ¬ ContainsLinearCopy E G)
    (hdual : SeparableSpace (D →L[ℝ] ℝ)) :
    ¬ ContainsComplementedCopy (L1Shifts.F E) (G × D) := by
  letI : SeparableSpace (D →L[ℝ] ℝ) := hdual
  rintro ⟨J, T, hTJ⟩
  let JG := (ContinuousLinearMap.fst ℝ G D).comp J
  let JD := (ContinuousLinearMap.snd ℝ G D).comp J
  let TG := T.comp (ContinuousLinearMap.inl ℝ G D)
  let TD := T.comp (ContinuousLinearMap.inr ℝ G D)
  have hsplit : TG.comp JG + TD.comp JD = ContinuousLinearMap.id ℝ (L1Shifts.F E) := by
    apply ContinuousLinearMap.ext
    intro x
    change T ((J x).1, 0) + T (0, (J x).2) = x
    rw [← map_add]
    have hz : ((J x).1, (0 : D)) + (0, (J x).2) = J x := by
      apply Prod.ext <;> simp
    rw [hz]
    exact congrArg (fun f : L1Shifts.F E →L[ℝ] L1Shifts.F E => f x) hTJ
  have ht := (L1Tails.tendsto_opNorm_tail_comp (fun _ : ℕ => E) TD).mul_const ‖JD‖
  have ht' : Tendsto (fun m => ‖(L1Shifts.downCLM E m).comp TD‖ * ‖JD‖)
      atTop (nhds 0) := by
    simpa only [L1Shifts.norm_down_comp, zero_mul] using ht
  obtain ⟨m, hm⟩ := (ht'.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).exists
  let Sp := L1Shifts.upCLM E m
  let Sm := L1Shifts.downCLM E m
  let A := JG.comp Sp
  let B := Sm.comp TG
  let K := JD.comp Sp
  let Q := Sm.comp TD
  have hsplit' : B.comp A + Q.comp K = ContinuousLinearMap.id ℝ (L1Shifts.F E) := by
    apply ContinuousLinearMap.ext
    intro x
    change Sm (TG (JG (Sp x))) + Sm (TD (JD (Sp x))) = x
    rw [← map_add]
    have hx := congrArg (fun f : L1Shifts.F E →L[ℝ] L1Shifts.F E => f (Sp x)) hsplit
    change TG (JG (Sp x)) + TD (JD (Sp x)) = Sp x at hx
    rw [hx]
    exact congrArg (fun f : L1Shifts.F E →L[ℝ] L1Shifts.F E => f x) (L1Shifts.down_up E m)
  have hsmall : ‖Q.comp K‖ < 1 := by
    calc
      ‖Q.comp K‖ ≤ ‖Q‖ * ‖K‖ := Q.opNorm_comp_le K
      _ ≤ ‖Q‖ * (‖JD‖ * ‖Sp‖) :=
        mul_le_mul_of_nonneg_left (JD.opNorm_comp_le Sp) (norm_nonneg Q)
      _ ≤ ‖Q‖ * (‖JD‖ * 1) := by
        have hSp : ‖Sp‖ ≤ 1 := L1Shifts.opNorm_upCLM_le E m
        gcongr
      _ = ‖Q‖ * ‖JD‖ := by rw [mul_one]
      _ < 1 := hm
  obtain ⟨A', B', hBA⟩ := Factorization.discard_small_factor A B K Q hsplit' hsmall
  obtain ⟨U, a, ha, hU⟩ := Factorization.linearCopy_of_split A' B' hBA
  apply hG
  let I : E →L[ℝ] L1Shifts.F E := lp.singleContinuousLinearMap ℝ (fun _ : ℕ => E) 1 0
  refine ⟨U.comp I, a, ha, ?_⟩
  intro x
  have hx : ‖I x‖ = ‖x‖ := by
    change ‖lp.single (E := fun _ : ℕ => E) 1 0 x‖ = ‖x‖
    exact lp.norm_single (E := fun _ : ℕ => E) (by norm_num : (0 : ℝ≥0∞) < 1) 0 x
  simpa only [ContinuousLinearMap.comp_apply, hx] using hU (I x)

end FinitePerturbation
end BanachGeometry
