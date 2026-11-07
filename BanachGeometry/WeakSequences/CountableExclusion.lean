import BanachGeometry.WeakSequences.OperatorTails
import BanachGeometry.AlmostIsometric.CriterionAssembly
import Mathlib.Algebra.BigOperators.Fin

/-! R6 Corollary 4.3: the truncation argument retains dual separability
as an explicit hypothesis hdual. Complemented/ConcreteDual proves the
concrete C0L2 dual fact and applies this argument. Finite products below
have their usual maximum norm, linearly equivalent to the finite ℓ₁ norm;
this comparison is used only for linear exclusion. -/

noncomputable section
open Filter TopologicalSpace
namespace BanachGeometry
namespace L1FiniteHead
variable (V : ℕ → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]

def firstPi (m : ℕ) : L1Sum V →L[ℝ] (∀ r : Fin m, V r.val) where
  toFun x r := x r.val
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl
  cont := continuous_pi (fun r => (lp.evalCLM ℝ V 1 r.val).continuous)

@[simp] theorem firstPi_apply (m : ℕ) (x : L1Sum V) (r : Fin m) :
    firstPi V m x r = x r.val := rfl

def finiteEval (m : ℕ) (r : Fin m) : (∀ s : Fin m, V s.val) →L[ℝ] V r.val where
  toFun z := z r
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := continuous_apply r

def fromPi (m : ℕ) : (∀ r : Fin m, V r.val) →L[ℝ] L1Sum V :=
  ∑ r : Fin m, (lp.singleContinuousLinearMap ℝ V 1 r.val).comp (finiteEval V m r)

theorem fromPi_apply (m : ℕ) (z : ∀ r : Fin m, V r.val) :
    fromPi V m z = ∑ r : Fin m, lp.single 1 r.val (z r) := by
  simp only [fromPi, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply, finiteEval]
  rfl

theorem fromPi_firstPi (m : ℕ) (x : L1Sum V) :
    fromPi V m (firstPi V m x) = L1Tails.head V m x := by
  rw [fromPi_apply, L1Tails.head_eq_sum]
  simpa only [firstPi_apply] using
    (Finset.sum_range (n := m) (fun i => lp.single 1 i (x i))).symm

end L1FiniteHead

namespace LinearExclusion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (V : ℕ → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]

/-- Countable linear exclusion from explicit dual separability hdual
and all finite-head exclusions hfinite. ConcreteDual supplies the C0L2
specialization; this local theorem retains hdual for the general space E. -/
theorem countable_of_finite (hdual : SeparableSpace (E →L[ℝ] ℝ))
    (hfinite : ∀ m : ℕ, ¬ ContainsLinearCopy E (∀ r : Fin m, V r.val)) :
    ¬ ContainsLinearCopy E (L1Sum V) := by
  letI : SeparableSpace (E →L[ℝ] ℝ) := hdual
  rintro ⟨T, a, ha, hT⟩
  have ht := L1Tails.tendsto_opNorm_tail_comp V T
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.1
    (ht.eventually (eventually_lt_nhds (half_pos ha)))
  have hsmall : ‖(L1Tails.tail V m).comp T‖ < a / 2 := hm m le_rfl
  let U := (L1FiniteHead.firstPi V m).comp T
  let F := L1FiniteHead.fromPi V m
  have hden : 0 < ‖F‖ + 1 := by positivity
  apply hfinite m
  refine ⟨U, (a / 2) / (‖F‖ + 1), div_pos (half_pos ha) hden, ?_⟩
  intro x
  have htail : ‖L1Tails.tail V m (T x)‖ ≤ (a / 2) * ‖x‖ := by
    exact (((L1Tails.tail V m).comp T).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hsmall.le (norm_nonneg x))
  have hdecomp : T x = L1Tails.head V m (T x) + L1Tails.tail V m (T x) := by
    rw [L1Tails.tail_eq_sub_head]
    abel
  have hhead : (a / 2) * ‖x‖ ≤ ‖L1Tails.head V m (T x)‖ := by
    have hnorm := norm_add_le (L1Tails.head V m (T x)) (L1Tails.tail V m (T x))
    rw [← hdecomp] at hnorm
    have hlow := hT x
    linarith
  have hFU : F (U x) = L1Tails.head V m (T x) :=
    L1FiniteHead.fromPi_firstPi V m (T x)
  have hb : (a / 2) * ‖x‖ ≤ ‖F‖ * ‖U x‖ := by
    rw [← hFU] at hhead
    exact hhead.trans (F.le_opNorm _)
  calc
    ((a / 2) / (‖F‖ + 1)) * ‖x‖ = ((a / 2) * ‖x‖) / (‖F‖ + 1) := by ring
    _ ≤ ‖U x‖ := (div_le_iff₀ hden).2 (by nlinarith [norm_nonneg (U x)])

end LinearExclusion

namespace AlmostIsometricFamily
/-- R6 4.3 for a family with finite-sum exclusion h4, including repeated
indices. The local type retains hdual for C0L2; ConcreteDual proves that
separability fact and applies countable_noCopy. -/
theorem countable_noCopy (d : AlmostIsometricFamily) (h4 : d.ExcludesFiniteSumCopy)
    (hdual : SeparableSpace (C0L2 →L[ℝ] ℝ)) (indices : ℕ → ℕ) :
    ¬ ContainsLinearCopy C0L2 (L1Sum (fun i => (d.Y (indices i)).Carrier)) := by
  apply LinearExclusion.countable_of_finite _ hdual
  intro m
  exact h4 m (fun r => indices r.val)

end AlmostIsometricFamily
end BanachGeometry
