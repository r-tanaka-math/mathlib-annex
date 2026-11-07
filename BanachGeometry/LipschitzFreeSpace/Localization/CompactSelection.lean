/- R6 8.1: all countability is confined to the chosen compact subset.
Uses the countable-family subsequence API from upstream LocalLipschitz (Apache-2.0),
then the new arbitrary-Hilbert increment exceptional-set estimate.
No ambient second-countability hypothesis.
Execution evidence is recorded in the external receipts. -/
import BanachGeometry.LipschitzFreeSpace.Localization.ExceptionalSet

noncomputable section
open scoped Topology NNReal InnerProductSpace
open Filter Set
namespace BanachGeometry.LipschitzFreeLocalization
open BanachGeometry.LipschitzFreeGeometry.LocalLipschitz
open BanachGeometry.LipschitzFreeGeometry.CoordinateLocality

universe uM uH
variable {M : Type uM} {H : Type uH} [MetricSpace M]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- One subsequence makes all relative-basis constants converge; its good neighborhoods
are then available for every positive eta. The ambient M can be nonseparable. -/
theorem exists_compact_good_subsequence (D : M → H) {L : ℝ≥0}
    (hD : LipschitzWith L D) (hL : 0 < L) (hloc : IncrementLocality D)
    (b : ℕ → H) (hbn : ∀ i, ‖b i‖ ≤ 1) (hb : BanachGeometry.WeakNull b)
    {K : Set M} (hK : IsCompact K) :
    ∃ t : ℕ → ℕ, StrictMono t ∧ ∀ η : ℝ≥0, 0 < η → ∃ Z : Set M, Z.Finite ∧
      ∀ p ∈ K, p ∉ Z → ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
        ∀ᶠ i in atTop, LipschitzOnWith η (fun x => ⟪D x, b (t i)⟫_ℝ) (K ∩ U) := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : SecondCountableTopology K := inferInstance
  let DK : K → H := fun x => D x.val
  have hDK : LipschitzWith L DK := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hD.dist_le_mul x.val y.val
  have hlocK : IncrementLocality DK := hloc.comp Subtype.val continuous_subtype_val Subtype.val_injective
  let d : ℕ → K → ℝ := fun i x => ⟪DK x, b i⟫_ℝ
  have hd (i : ℕ) : LipschitzWith L (d i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← inner_sub_left]
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left (hbn i) (norm_nonneg _)).trans (by
        simpa only [mul_one, ← dist_eq_norm] using hDK.dist_le_mul x y))
  obtain ⟨B, hBc, hBne, hB⟩ := TopologicalSpace.exists_countable_basis K
  let O : B → Set K := Subtype.val
  letI : Countable B := hBc.to_subtype
  obtain ⟨a, t, ht, ha, halim⟩ := subsequence_constants O d hd
  have hbase : ∀ z : K, ∀ U : Set K, IsOpen U → z ∈ U → ∃ j, z ∈ O j ∧ O j ⊆ U := by
    intro z U hU hz
    obtain ⟨P, hPB, hzP, hPU⟩ := hB.exists_subset_of_mem_open hz hU
    exact ⟨⟨P, hPB⟩, hzP, hPU⟩
  refine ⟨t, ht, ?_⟩
  intro η hη
  have hbt : BanachGeometry.WeakNull (fun i => b (t i)) := fun f => (hb f).comp ht.tendsto_atTop
  have hbad : (badSet O a (η : ℝ)).Finite :=
    badSet_finite_of_incrementLocality DK hL hDK hlocK (fun i => b (t i))
      (fun i => hbn (t i)) hbt O hbase a halim hη
  let W : Set K := badSet O a (η : ℝ)
  let Z : Set M := Subtype.val '' W
  refine ⟨Z, hbad.image Subtype.val, ?_⟩
  intro p hp hpZ
  let pK : K := ⟨p, hp⟩
  have hpW : pK ∉ W := fun h => hpZ ⟨pK, h, rfl⟩
  change ¬ (∀ j, pK ∈ O j → (η : ℝ) ≤ a j) at hpW
  push_neg at hpW
  obtain ⟨j, hpj, haj⟩ := hpW
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hB.isOpen j.property) pK hpj
  refine ⟨Metric.ball p r, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_⟩
  have hevent := (halim j).eventually (eventually_lt_nhds haj)
  filter_upwards [hevent] with i hi
  have hlocal := ((lipschitzOn_constant (hd (t i)).lipschitzOnWith).weaken hi.le)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let xK : K := ⟨x, hx.1⟩
  let yK : K := ⟨y, hy.1⟩
  have hxK : xK ∈ O j := hball hx.2
  have hyK : yK ∈ O j := hball hy.2
  exact hlocal.dist_le_mul xK hxK yK hyK

end BanachGeometry.LipschitzFreeLocalization
