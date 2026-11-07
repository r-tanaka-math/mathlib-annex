import BanachGeometry.AlmostIsometric.LipschitzDistance
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Optimal Lipschitz constants as actual least constants, followed by
the equality of the two multiplicative-distance infima in R6. Attainment
of each map's least constant is proved from all distance quotients.
No least constant or infimum-attainment axiom is supplied as data.
Local execution status is recorded in the external qualification receipts. -/
noncomputable section
open scoped NNReal
namespace BanachGeometry
namespace OptimalLipschitz
variable {E F : Type*} [MetricSpace E] [MetricSpace F]

def bounds (f : E → F) : Set ℝ :=
  {a | 0 ≤ a ∧ ∀ x y, dist (f x) (f y) ≤ a * dist x y}

/-- Total real infimum. Its interpretation as the least Lipschitz constant requires
`(bounds f).Nonempty`, as in `isLeast_bounds`; no claim is made for non-Lipschitz maps. -/
def finiteConstant (f : E → F) : ℝ := sInf (bounds f)

theorem bounds_nonempty_of_lipschitzWith (f : E → F) {K : ℝ≥0}
    (hf : LipschitzWith K f) : (bounds f).Nonempty := ⟨K, K.coe_nonneg, hf.dist_le_mul⟩

theorem bddBelow_bounds (f : E → F) : BddBelow (bounds f) := ⟨0,fun a ha => ha.1⟩

theorem finiteConstant_le (f : E → F) {a : ℝ} (ha : a ∈ bounds f) : finiteConstant f ≤ a :=
  csInf_le (bddBelow_bounds f) ha

theorem finiteConstant_mem_bounds (f : E → F) (hf : (bounds f).Nonempty) : finiteConstant f ∈ bounds f := by
  have hnonneg : 0 ≤ finiteConstant f := le_csInf hf (fun a ha => ha.1)
  refine ⟨hnonneg,?_⟩
  intro x y
  by_cases hxy : x = y
  · subst y; simp
  · have hp : 0 < dist x y := dist_pos.mpr hxy
    have hquot : dist (f x) (f y) / dist x y ≤ finiteConstant f := by
      apply le_csInf hf
      intro a ha
      exact (div_le_iff₀ hp).mpr (ha.2 x y)
    exact (div_le_iff₀ hp).mp hquot

theorem isLeast_bounds (f : E → F) (hf : (bounds f).Nonempty) : IsLeast (bounds f) (finiteConstant f) :=
  ⟨finiteConstant_mem_bounds f hf,fun a ha => finiteConstant_le f ha⟩

theorem mem_bounds_iff_lipschitzWith (f : E → F) (a : ℝ) (ha : 0 ≤ a) :
    a ∈ bounds f ↔ LipschitzWith (⟨a,ha⟩ : ℝ≥0) f := by
  constructor
  · intro h; exact LipschitzWith.of_dist_le_mul h.2
  · intro h; exact ⟨ha,h.dist_le_mul⟩

theorem isLeast_lipschitzConstants (f : E → F) (hf : (bounds f).Nonempty) :
    IsLeast {K : ℝ≥0 | LipschitzWith K f}
      (⟨finiteConstant f,(finiteConstant_mem_bounds f hf).1⟩ : ℝ≥0) := by
  refine ⟨(mem_bounds_iff_lipschitzWith f _ _).mp (finiteConstant_mem_bounds f hf),?_⟩
  intro K hK
  exact_mod_cast finiteConstant_le f ((mem_bounds_iff_lipschitzWith f K K.2).mpr hK)

theorem finiteConstant_eq_of_isLeast (f : E → F) (K : ℝ≥0)
    (hK : IsLeast {L : ℝ≥0 | LipschitzWith L f} K) : finiteConstant f = K := by
  have hmem : (K : ℝ) ∈ bounds f := (mem_bounds_iff_lipschitzWith f K K.2).mpr hK.1
  have hf : (bounds f).Nonempty := ⟨K,hmem⟩
  apply le_antisymm (finiteConstant_le f hmem)
  have he := hK.2 (isLeast_lipschitzConstants f hf).1
  exact_mod_cast he

theorem finiteConstant_pos_of_injective [Nontrivial E] (f : E → F) (hinj : Function.Injective f)
    (hf : (bounds f).Nonempty) : 0 < finiteConstant f := by
  obtain ⟨x,y,hxy⟩ := exists_pair_ne E
  have hp : 0 < dist (f x) (f y) := dist_pos.mpr (hinj.ne hxy)
  have hb := (finiteConstant_mem_bounds f hf).2 x y
  by_contra hbad
  have hnonpos : finiteConstant f ≤ 0 := le_of_not_gt hbad
  have hmul := mul_nonpos_of_nonpos_of_nonneg hnonpos (show 0 ≤ dist x y from dist_nonneg)
  linarith

end OptimalLipschitz

namespace LipschitzDistance
variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

def optimalDistortions : Set ℝ := {D | ∃ f : E ≃ F,
  (OptimalLipschitz.bounds (f : E → F)).Nonempty ∧
  (OptimalLipschitz.bounds (f.symm : F → E)).Nonempty ∧
    D = OptimalLipschitz.finiteConstant (f : E → F) * OptimalLipschitz.finiteConstant (f.symm : F → E)}

/-- Finite-case real infimum; its distance interpretation requires a nonempty
bi-Lipschitz distortion set and nontrivial spaces. It is not an infinity-valued distance. -/
def finiteOptimalDistance : ℝ := sInf (optimalDistortions E F)

theorem optimalDistortions_subset_distortions [Nontrivial E] [Nontrivial F] :
    optimalDistortions E F ⊆ distortions E F := by
  rintro D ⟨f,hf,hg,rfl⟩
  refine ⟨f,OptimalLipschitz.finiteConstant (f : E → F),OptimalLipschitz.finiteConstant (f.symm : F → E),
    OptimalLipschitz.finiteConstant_pos_of_injective _ f.injective hf,
    OptimalLipschitz.finiteConstant_pos_of_injective _ f.symm.injective hg,rfl,?_,?_⟩
  · intro x y
    simpa only [dist_eq_norm] using (OptimalLipschitz.finiteConstant_mem_bounds _ hf).2 x y
  · intro x y
    simpa only [dist_eq_norm] using (OptimalLipschitz.finiteConstant_mem_bounds _ hg).2 x y

theorem exists_optimal_distortion_le {D : ℝ} (hD : D ∈ distortions E F) :
    ∃ D', D' ∈ optimalDistortions E F ∧ D' ≤ D := by
  obtain ⟨f,a,b,ha,hb,rfl,hf,hg⟩ := hD
  have hfa : a ∈ OptimalLipschitz.bounds (f : E → F) := by
    refine ⟨ha.le,?_⟩
    intro x y; simpa only [dist_eq_norm] using hf x y
  have hgb : b ∈ OptimalLipschitz.bounds (f.symm : F → E) := by
    refine ⟨hb.le,?_⟩
    intro x y; simpa only [dist_eq_norm] using hg x y
  have hfn : (OptimalLipschitz.bounds (f : E → F)).Nonempty := ⟨a,hfa⟩
  have hgn : (OptimalLipschitz.bounds (f.symm : F → E)).Nonempty := ⟨b,hgb⟩
  refine ⟨_,⟨f,hfn,hgn,rfl⟩,?_⟩
  exact mul_le_mul (OptimalLipschitz.finiteConstant_le _ hfa) (OptimalLipschitz.finiteConstant_le _ hgb)
    (OptimalLipschitz.finiteConstant_mem_bounds _ hgn).1 ha.le

theorem finiteOptimalDistance_eq_finiteDistance [Nontrivial E] [Nontrivial F]
    (hne : (distortions E F).Nonempty) : finiteOptimalDistance E F = finiteDistance E F := by
  have hoptne : (optimalDistortions E F).Nonempty := by
    obtain ⟨D,hD⟩ := hne
    obtain ⟨D',hD',hle⟩ := exists_optimal_distortion_le E F hD
    exact ⟨D',hD'⟩
  have hoptbdd : BddBelow (optimalDistortions E F) :=
    ⟨1,fun D hD => one_le_distortion E F (optimalDistortions_subset_distortions E F hD)⟩
  apply le_antisymm
  · apply le_csInf hne
    intro D hD
    obtain ⟨D',hD',hle⟩ := exists_optimal_distortion_le E F hD
    exact (csInf_le hoptbdd hD').trans hle
  · apply le_csInf hoptne
    intro D hD
    exact csInf_le (bddBelow_distortions E F) (optimalDistortions_subset_distortions E F hD)

theorem finiteOptimalDistance_eq_one (X Y : SeparableRealBanach)
    (h : AlmostIsometricAtEveryTolerance X Y) : finiteOptimalDistance X.Carrier Y.Carrier = 1 := by
  have hne : (distortions X.Carrier Y.Carrier).Nonempty := by
    obtain ⟨f,hzero,hf,hg⟩ := h 1 zero_lt_one
    have htwo : (1 : ℝ) + 1 = 2 := by norm_num
    refine ⟨4,f,2,2,by norm_num,by norm_num,by norm_num,?_,?_⟩
    · simpa only [htwo] using hf
    · simpa only [htwo] using hg
  rw [finiteOptimalDistance_eq_finiteDistance X.Carrier Y.Carrier hne]
  exact finiteDistance_eq_one X Y h

end LipschitzDistance
end BanachGeometry
