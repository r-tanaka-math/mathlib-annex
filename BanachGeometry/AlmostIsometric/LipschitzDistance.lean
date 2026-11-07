import BanachGeometry.Complemented.HeadSplitting
import Mathlib.Analysis.Normed.Affine.MazurUlam

/-! The multiplicative (not logarithmic) Lipschitz distance of R6, defined
as the infimum over positive forward/inverse Lipschitz bounds. Taking all
admissible bounds gives the same infimum as taking the optimal constants.
The lower bound uses a nontrivial domain. Distortion one is excluded via
normalization to an isometric bijection and the real Mazur–Ulam theorem.
This is separate from escape/nonconvergence of the constructed maps f_N.
Local execution status is recorded in the external qualification receipts. -/
noncomputable section
namespace BanachGeometry
namespace LipschitzDistance
variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

def distortions : Set ℝ := {D | ∃ (f : E ≃ F) (a b : ℝ),
  0 < a ∧ 0 < b ∧ D = a*b ∧
  (∀ x y, ‖f x-f y‖ ≤ a*‖x-y‖) ∧ (∀ x y, ‖f.symm x-f.symm y‖ ≤ b*‖x-y‖)}

/-- Total real infimum used only as a finite-distance helper when `distortions E F`
is nonempty (and, for the lower-bound interpretation, `E` is nontrivial).
This does not encode the extended distance of a pair with no bi-Lipschitz equivalence. -/
def finiteDistance : ℝ := sInf (distortions E F)

theorem one_le_distortion [Nontrivial E] {D : ℝ} (hD : D ∈ distortions E F) : 1 ≤ D := by
  obtain ⟨f,a,b,ha,hb,rfl,hf,hg⟩ := hD
  obtain ⟨x,y,hxy⟩ := exists_pair_ne E
  have hpos : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hback := hg (f x) (f y)
  rw [f.symm_apply_apply,f.symm_apply_apply] at hback
  have hforward := mul_le_mul_of_nonneg_left (hf x y) hb.le
  nlinarith

theorem bddBelow_distortions [Nontrivial E] : BddBelow (distortions E F) :=
  ⟨1, fun D hD => one_le_distortion E F hD⟩

theorem one_le_distance [Nontrivial E] (hne : (distortions E F).Nonempty) :
    1 ≤ finiteDistance E F := le_csInf hne (fun D hD => one_le_distortion E F hD)

theorem distortions_nonempty_of_almostIsometric (X Y : SeparableRealBanach)
    (h : AlmostIsometricAtEveryTolerance X Y) :
    (distortions X.Carrier Y.Carrier).Nonempty := by
  obtain ⟨f, _, hf, hg⟩ := h 1 zero_lt_one
  refine ⟨4, f, 2, 2, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using hf
  · simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using hg

theorem finiteDistance_eq_one (X Y : SeparableRealBanach)
    (h : AlmostIsometricAtEveryTolerance X Y) : finiteDistance X.Carrier Y.Carrier = 1 := by
  have hex : (distortions X.Carrier Y.Carrier).Nonempty := by
    obtain ⟨f,hzero,hf,hg⟩ := h 1 zero_lt_one
    have htwo : (1 : ℝ) + 1 = 2 := by norm_num
    refine ⟨4, f,2,2,by norm_num,by norm_num,by norm_num,?_,?_⟩
    · simpa only [htwo] using hf
    · simpa only [htwo] using hg
  apply le_antisymm
  · by_contra hbad
    have hdist : 1 < finiteDistance X.Carrier Y.Carrier := lt_of_not_ge hbad
    let ε := (finiteDistance X.Carrier Y.Carrier-1)/2
    have hε : 0 < ε := by dsimp [ε]; linarith
    let δ := min (ε/4) 1
    have hδ : 0 < δ := lt_min (by positivity) zero_lt_one
    have hδ1 : δ ≤ 1 := min_le_right _ _
    have hδε : δ ≤ ε/4 := min_le_left _ _
    obtain ⟨f,hzero,hf,hg⟩ := h δ hδ
    have hmem : (1+δ)^2 ∈ distortions X.Carrier Y.Carrier := by
      refine ⟨f,1+δ,1+δ,by linarith,by linarith,by ring,hf,hg⟩
    have hle : finiteDistance X.Carrier Y.Carrier ≤ (1+δ)^2 :=
      csInf_le (bddBelow_distortions X.Carrier Y.Carrier) hmem
    have hsquare : δ^2 ≤ δ := by
      nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ1)]
    dsimp [ε] at hδε
    nlinarith
  · exact le_csInf hex (fun D hD => one_le_distortion X.Carrier Y.Carrier hD)

def normalizeSimilarity (f : E ≃ F) (a : ℝ) (ha : 0 < a)
    (heq : ∀ x y, ‖f x-f y‖ = a*‖x-y‖) : E ≃ᵢ F where
  toEquiv := {
    toFun := fun x => a⁻¹ • f x
    invFun := fun y => f.symm (a • y)
    left_inv := by
      intro x
      change f.symm (a • (a⁻¹ • f x)) = x
      rw [smul_smul,mul_inv_cancel₀ ha.ne',one_smul,f.symm_apply_apply]
    right_inv := by
      intro y
      change a⁻¹ • f (f.symm (a • y)) = y
      rw [f.apply_symm_apply,smul_smul,inv_mul_cancel₀ ha.ne',one_smul] }
  isometry_toFun := isometry_iff_dist_eq.mpr (by
    intro x y
    rw [dist_eq_norm,dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ha),heq,← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul])

theorem not_attained_at_one (hno : IsEmpty (E ≃L[ℝ] F)) : 1 ∉ distortions E F := by
  rintro ⟨f,a,b,ha,hb,hab,hf,hg⟩
  have hab' : a*b = 1 := hab.symm
  have heq (x y : E) : ‖f x-f y‖ = a*‖x-y‖ := by
    apply le_antisymm (hf x y)
    have hback := hg (f x) (f y)
    rw [f.symm_apply_apply,f.symm_apply_apply] at hback
    have hmul := mul_le_mul_of_nonneg_left hback ha.le
    simpa only [← mul_assoc,hab',one_mul] using hmul
  let g := normalizeSimilarity E F f a ha heq
  exact hno.false g.toRealLinearIsometryEquiv.toContinuousLinearEquiv

end LipschitzDistance

namespace AlmostIsometricFamily
theorem finiteDistance_one_nonattained (d : AlmostIsometricFamily) (h2 : d.HasContractivelyComplementedCopy) (h3 : d.HasCoordinateSplitting) (h4 : d.ExcludesFiniteSumCopy) :
    LipschitzDistance.finiteDistance d.FixedX d.FixedY = 1 ∧
      1 ∉ LipschitzDistance.distortions d.FixedX d.FixedY := by
  refine ⟨LipschitzDistance.finiteDistance_eq_one d.fixedXBanach d.fixedYBanach
    d.almostIsometricAtEveryTolerance_fixedXBanach_fixedYBanach, ?_⟩
  exact LipschitzDistance.not_attained_at_one d.FixedX d.FixedY
    (d.nonisomorphic_fixedX_fixedY_of_complemented_splitting_exclusion h2 h3 h4)
end AlmostIsometricFamily
end BanachGeometry
