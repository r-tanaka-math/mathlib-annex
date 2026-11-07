import BanachGeometry.NoC0.BasisSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Quotient

/-! Finite-dimensional norming and separation used in BP-basis.
Compactness is used only on a finite-dimensional subspace's sphere.
No completeness or separability of the ambient space is assumed.
Local execution status is recorded in the external qualification receipts. -/
noncomputable section
open Filter TopologicalSpace
namespace BanachGeometry
namespace BP
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def quotientMap (V : Submodule ℝ E) : E →L[ℝ] (E ⧸ V) :=
  V.mkQ.mkContinuous 1 (by
    intro x
    change ‖Submodule.Quotient.mk x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using Submodule.Quotient.norm_mk_le V x)

theorem exists_finite_norming (V : Submodule ℝ E) [FiniteDimensional ℝ V] :
    ∃ (s : Finset V) (f : V → E →L[ℝ] ℝ),
      (∀ i, ‖f i‖ ≤ 1) ∧ ∀ v : V, v ≠ 0 → ∃ i ∈ s, ‖v‖ ≤ 2 * |f i v| := by
  classical
  choose f hf hfv using fun v : V => exists_dual_vector'' ℝ (v : E)
  let U : V → Set V := fun v => {w | (1/2 : ℝ) < |f v w|}
  have hopen (v : V) : IsOpen (U v) :=
    isOpen_lt continuous_const ((f v).continuous.comp continuous_subtype_val).abs
  have hcover : Metric.sphere (0 : V) 1 ⊆ ⋃ v : V, U v := by
    intro v hv
    have hn : ‖v‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
    apply Set.mem_iUnion.mpr
    refine ⟨v, ?_⟩
    change (1/2 : ℝ) < |f v v|
    rw [hfv v]
    change (1/2 : ℝ) < |‖v‖|
    rw [hn]; norm_num
  obtain ⟨s,hs⟩ := (isCompact_sphere (0 : V) 1).elim_finite_subcover U hopen hcover
  refine ⟨s,f,hf,?_⟩
  intro v hv
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : V := ‖v‖⁻¹ • v
  have hwn : ‖w‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),inv_mul_cancel₀ hp.ne']
  have hw : w ∈ Metric.sphere (0 : V) 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using hwn
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hs hw)
  obtain ⟨his,hwi⟩ := Set.mem_iUnion.mp hi
  have he : |f i w| = ‖v‖⁻¹ * |f i v| := by
    change |f i (‖v‖⁻¹ • (v : E))| = _
    rw [map_smul,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hp)]
  change (1/2 : ℝ) < |f i w| at hwi
  rw [he] at hwi
  have hh := mul_lt_mul_of_pos_left hwi hp
  have hc : ‖v‖ * (‖v‖⁻¹ * |f i v|) = |f i v| := by
    rw [← mul_assoc,mul_inv_cancel₀ hp.ne',one_mul]
  rw [hc] at hh
  exact ⟨i,his,by linarith⟩

theorem eventually_norm_sub_ge_of_mem_finiteDimensional (u : ℕ → E) (hu : WeakNull u)
    (V : Submodule ℝ E) [FiniteDimensional ℝ V] (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, δ ≤ ‖u n‖ → ∀ v : E, v ∈ V → δ/4 ≤ ‖u n-v‖ := by
  classical
  obtain ⟨s,f,hf,hnorm⟩ := exists_finite_norming V
  have he : ∀ᶠ n in atTop, ∀ i ∈ s, |f i (u n)| < δ/8 := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    simpa only [Real.norm_eq_abs,norm_zero] using
      (hu (f i)).norm.eventually
        (eventually_lt_nhds (by simpa only [norm_zero] using (show 0 < δ/8 by positivity)))
  filter_upwards [he] with n hn
  intro hnu v hv
  by_contra hbad
  have hc : ‖u n-v‖ < δ/4 := lt_of_not_ge hbad
  have hvsmall : ‖v‖ < 3*δ/4 := by
    by_cases hvzero : v = 0
    · rw [hvzero,norm_zero]; positivity
    · obtain ⟨i,his,hiv⟩ := hnorm ⟨v,hv⟩ (by intro h; apply hvzero; exact congrArg Subtype.val h)
      have hfv : |f i v| ≤ |f i (u n)| + ‖u n-v‖ := by
        have hlin : f i v = f i (u n) - f i (u n-v) := by rw [map_sub]; ring
        calc
          _ = ‖f i (u n) - f i (u n-v)‖ := by rw [hlin,Real.norm_eq_abs]
          _ ≤ ‖f i (u n)‖ + ‖f i (u n-v)‖ := norm_sub_le _ _
          _ ≤ |f i (u n)| + ‖u n-v‖ := by
            have hb : ‖f i (u n-v)‖ ≤ ‖u n-v‖ := (f i).le_opNorm _ |>.trans (by
              simpa only [one_mul] using mul_le_mul_of_nonneg_right (hf i) (norm_nonneg _))
            simpa only [Real.norm_eq_abs] using add_le_add (le_refl ‖f i (u n)‖) hb
      change ‖v‖ ≤ 2 * |f i v| at hiv
      linarith [hn i his]
  have htri : ‖u n‖ ≤ ‖u n-v‖ + ‖v‖ := by
    calc
      _ = ‖(u n-v)+v‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  linarith

/-- A functional that annihilates V and detects distance from V. The
quotient is only seminormed when V is not closed; Hahn–Banach still applies. -/
theorem exists_annihilating_functional (V : Submodule ℝ E) (x : E) (d : ℝ)
    (hfar : ∀ v : E, v ∈ V → d ≤ ‖x-v‖) :
    ∃ f : E →L[ℝ] ℝ, ‖f‖ ≤ 1 ∧ (∀ v : E, v ∈ V → f v = 0) ∧ d ≤ f x := by
  have hnorm : d ≤ ‖quotientMap V x‖ := by
    by_contra hbad
    have hp : 0 < d-‖quotientMap V x‖ := sub_pos.mpr (lt_of_not_ge hbad)
    obtain ⟨y,hy,hyn⟩ := Submodule.Quotient.norm_mk_lt (quotientMap V x) hp
    have hmem : x-y ∈ V := by
      apply (Submodule.Quotient.mk_eq_zero V).mp
      change V.mkQ (x-y) = 0
      rw [map_sub]
      change quotientMap V x - Submodule.Quotient.mk y = 0
      rw [hy,sub_self]
    have hb := hfar (x-y) hmem
    rw [sub_sub_cancel] at hb
    linarith
  obtain ⟨g,hgn,hgx⟩ := exists_dual_vector'' ℝ (quotientMap V x)
  let f := g.comp (quotientMap V)
  have hf : ‖f‖ ≤ 1 := by
    apply f.opNorm_le_bound zero_le_one
    intro v
    apply (g.le_opNorm _).trans
    have hv := Submodule.Quotient.norm_mk_le V v
    change ‖quotientMap V v‖ ≤ ‖v‖ at hv
    exact mul_le_mul hgn hv (norm_nonneg _) zero_le_one
  refine ⟨f,hf,?_,?_⟩
  · intro v hv
    change g (Submodule.Quotient.mk v) = 0
    rw [(Submodule.Quotient.mk_eq_zero V).mpr hv,map_zero]
  · change d ≤ g (quotientMap V x)
    rw [hgx]
    exact hnorm

end BP
end BanachGeometry
