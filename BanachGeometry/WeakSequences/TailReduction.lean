import BanachGeometry.WeakSequences.L1Tails

/-!
# Explicit reductions for R6 §4

The operator-norm argument uses uniform tails on the image of the unit ball.
The sequential reductions retain hweak and hsub as explicit theorem parameters.
WeakTailGliding proves uniform tails for weakly Cauchy ℓ₁ sequences, and
SeparableDualSubsequence gives hsub when the domain has separable dual.
OperatorTails combines them under that domain assumption; the local reductions
here do not assert hsub for every normed space B.
-/

noncomputable section
open Filter
namespace BanachGeometry

def WeaklyCauchy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) : Prop := ∀ f : E →L[ℝ] ℝ, CauchySeq (fun n => f (u n))

theorem weaklyCauchy_map {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) {u : ℕ → E} (hu : WeaklyCauchy u) :
    WeaklyCauchy (T ∘ u) := by
  intro f
  exact hu (f.comp T)

namespace L1Tails
variable (V : ℕ → Type*) [∀ n, NormedAddCommGroup (V n)]
    [∀ n, NormedSpace ℝ (V n)]

/-- Sequential transport from explicit hweak and hsub. WeakTailGliding
supplies hweak; hsub is retained for the particular set K in this reduction. -/
theorem hasUniformlySmallTails_of_weaklyCauchy_subseq {K : Set (L1Sum V)}
    (hweak : ∀ u : ℕ → L1Sum V, WeaklyCauchy u → HasUniformlySmallTails V (Set.range u))
    (hsub : ∀ u : ℕ → L1Sum V, (∀ n, u n ∈ K) →
      ∃ s : ℕ → ℕ, StrictMono s ∧ WeaklyCauchy (u ∘ s)) : HasUniformlySmallTails V K := by
  apply hasUniformlySmallTails_of_subsequence V
  intro u hu
  obtain ⟨s, hs, hws⟩ := hsub u hu
  exact ⟨s, hs, hweak (u ∘ s) hws⟩

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- A bound on the actual closed unit ball gives the operator norm bound. -/
theorem opNorm_le_of_unit_bound (S : B →L[ℝ] L1Sum V) (a : ℝ) (ha : 0 ≤ a)
    (hunit : ∀ x : B, ‖x‖ ≤ 1 → ‖S x‖ ≤ a) : ‖S‖ ≤ a := by
  apply S.opNorm_le_bound ha
  intro x
  by_cases hx : x = 0
  · subst x; simp
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hu : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
      simp only [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hxpos.ne']
      exact le_rfl
    have hdiv : ‖S x‖ / ‖x‖ ≤ a := by
      calc
        ‖S x‖ / ‖x‖ = ‖S (‖x‖⁻¹ • x)‖ := by
          simp only [map_smul, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), div_eq_mul_inv]
          exact mul_comm _ _
        _ ≤ a := hunit _ hu
    exact (div_le_iff₀ hxpos).1 hdiv

/-- The exact operator-norm tail conclusion, from a visible uniform-tail
hypothesis on the image of the unit ball. No separable-dual result is assumed
through an instance. -/
theorem tendsto_opNorm_tail_comp_of_hasUniformlySmallTails (T : B →L[ℝ] L1Sum V)
    (hUniform : HasUniformlySmallTails V (T '' {x : B | ‖x‖ ≤ 1})) :
    Tendsto (fun m => ‖(tail V m).comp T‖) atTop (nhds 0) := by
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  obtain ⟨N, hN⟩ := hasUniformlySmallTails_eventually V hUniform (ε / 2) (half_pos hε)
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro m hm
  have hb : ‖(tail V m).comp T‖ ≤ ε / 2 := by
    apply opNorm_le_of_unit_bound V _ (ε / 2) (le_of_lt (half_pos hε))
    intro x hx
    exact (hN m hm (T x) ⟨x, hx, rfl⟩).le
  simpa only [Real.dist_eq, sub_zero, abs_norm] using hb.trans_lt (half_lt_self hε)

/-- R6 Lemma 4.2 from explicit hweak (uniform tails for weakly Cauchy ℓ₁
sequences) and hsub (weakly Cauchy subsequences of unit-ball sequences in B).
WeakTailGliding proves hweak; SeparableDualSubsequence proves hsub for domains
with separable dual, as used by OperatorTails. Both hypotheses remain in this
local theorem; no assertion is made for an arbitrary B without hsub. -/
theorem tendsto_opNorm_tail_comp_of_weaklyCauchy_subseq (T : B →L[ℝ] L1Sum V)
    (hweak : ∀ u : ℕ → L1Sum V, WeaklyCauchy u → HasUniformlySmallTails V (Set.range u))
    (hsub : ∀ u : ℕ → B, (∀ n, ‖u n‖ ≤ 1) →
      ∃ s : ℕ → ℕ, StrictMono s ∧ WeaklyCauchy (u ∘ s)) :
    Tendsto (fun m => ‖(tail V m).comp T‖) atTop (nhds 0) := by
  apply tendsto_opNorm_tail_comp_of_hasUniformlySmallTails V T
  apply hasUniformlySmallTails_of_weaklyCauchy_subseq V hweak
  intro u hu
  have hpre : ∀ n, ∃ x : B, ‖x‖ ≤ 1 ∧ T x = u n := fun n => hu n
  choose v hv hvT using hpre
  obtain ⟨s, hs, hvs⟩ := hsub v hv
  refine ⟨s, hs, ?_⟩
  have hmap := weaklyCauchy_map T hvs
  simpa only [Function.comp_def, hvT] using hmap

end L1Tails
end BanachGeometry
