import MathlibAnnex.Analysis.Normed.Module.EquivalentSeminorm.Transport
import MathlibAnnex.Analysis.Normed.Dual.DeterminantFrame
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Module.Span
import Mathlib.Topology.MetricSpace.Cover

noncomputable section
set_option autoImplicit false
open Set Module
open scoped BigOperators NNReal
namespace MathlibAnnex.Satellite
universe u
private abbrev Coord (n : ℕ) := Fin n → ℝ
private abbrev NormModel (n : ℕ) := EquivalentSeminorm (Coord n)
private abbrev DualFrame (n : ℕ) := DeterminantFrame.Frame n (Coord n)
private abbrev dualFrameMatrix {n : ℕ} := DeterminantFrame.frameMatrix (Pi.basisFun ℝ (Fin n))
private abbrev frameDet {n : ℕ} := DeterminantFrame.frameDeterminant (Pi.basisFun ℝ (Fin n))
private abbrev replacementDet {n : ℕ} := DeterminantFrame.replacementDeterminant (Pi.basisFun ℝ (Fin n))
private abbrev frameCoordinates {n : ℕ} := @DeterminantFrame.frameCoordinates n (Coord n) _ _
private abbrev framePreimage {n : ℕ} (B : DualFrame n) (c : Coord n) := (dualFrameMatrix B)⁻¹.mulVec c
private abbrev IsDualContraction {n : ℕ} (M : NormModel n) (r : Coord n →L[ℝ] ℝ) := ∀ x, |r x| ≤ M.p x
private abbrev dualRowSet {n : ℕ} (M : NormModel n) := {r : Coord n →L[ℝ] ℝ | IsDualContraction M r}
private abbrev dualFrameSet {n : ℕ} (M : NormModel n) := {B : DualFrame n | ∀ i, IsDualContraction M (B i)}

private instance modelFiniteDimensional {n : ℕ} (M : NormModel n) : FiniteDimensional ℝ (EquivalentSeminorm.Space M) :=
  inferInstanceAs (FiniteDimensional ℝ (Coord n))

private def modelBasis {n : ℕ} (M : NormModel n) : Basis (Fin n) ℝ (EquivalentSeminorm.Space M) :=
  Pi.basisFun ℝ (Fin n)

private def toModelRow {n : ℕ} (M : NormModel n) (r : Coord n →L[ℝ] ℝ) :
    EquivalentSeminorm.Space M →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (show EquivalentSeminorm.Space M →ₗ[ℝ] ℝ from r.toLinearMap)

private def fromModelRow {n : ℕ} (M : NormModel n) (r : EquivalentSeminorm.Space M →L[ℝ] ℝ) :
    Coord n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (show Coord n →ₗ[ℝ] ℝ from r.toLinearMap)

private theorem toModelRow_mem_iff {n : ℕ} (M : NormModel n) (r : Coord n →L[ℝ] ℝ) :
    toModelRow M r ∈ DeterminantFrame.unitRowSet (EquivalentSeminorm.Space M) ↔ IsDualContraction M r := by
  rw [DeterminantFrame.mem_unitRowSet]
  constructor
  · intro h x
    have := (toModelRow M r).le_opNorm (show EquivalentSeminorm.Space M from x)
    change |r x| ≤ ‖toModelRow M r‖ * M.p x at this
    exact this.trans (by nlinarith [apply_nonneg M.p x])
  · intro h
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change |r (show Coord n from x)| ≤ 1 * M.p (show Coord n from x)
    simpa only [one_mul] using h (show Coord n from x)

private abbrev detMax {n : ℕ} (M : NormModel n) := DeterminantFrame.determinantMaximum (modelBasis M)
private abbrev NearMaxInverseBound {n : ℕ} (M : NormModel n) := DeterminantFrame.NearMaxInverseBound (modelBasis M)
private abbrev nearMaxFrames {n : ℕ} (M : NormModel n) (η : ℝ) := {B : DualFrame n | B ∈ dualFrameSet M ∧ detMax M - η ≤ |frameDet B|}

private theorem toModelFrame_mem {n : ℕ} (M : NormModel n) {B : DualFrame n} (h : B ∈ dualFrameSet M) :
    (fun i => toModelRow M (B i)) ∈ DeterminantFrame.unitFrameSet n (EquivalentSeminorm.Space M) := by
  intro i
  exact (toModelRow_mem_iff M (B i)).mpr (h i)

private theorem toModelFrame_near {n : ℕ} (M : NormModel n) {η : ℝ} {B : DualFrame n} (h : B ∈ nearMaxFrames M η) :
    (fun i => toModelRow M (B i)) ∈ DeterminantFrame.nearMaxFrames (modelBasis M) η :=
  ⟨toModelFrame_mem M h.1, h.2⟩

private theorem seminorm_framePreimage_le {n : ℕ} (M : NormModel n) {η : ℝ} (H : NearMaxInverseBound M η) {B : DualFrame n}
    (h : B ∈ nearMaxFrames M η) (c : Coord n) : M.p (framePreimage B c) ≤ H.boundConstant * ‖c‖ := by
  exact H.bound (toModelFrame_near M h) c

private theorem detMax_pos {n : ℕ} (M : NormModel n) : 0 < detMax M :=
  DeterminantFrame.determinantMaximum_pos (modelBasis M)

private theorem nearMaxFrame_det_ne_zero {n : ℕ} (M : NormModel n) {η : ℝ}
    (hη : η < detMax M) {B : DualFrame n} (hB : B ∈ nearMaxFrames M η) : frameDet B ≠ 0 :=
  DeterminantFrame.nearMaxFrame_det_ne_zero (modelBasis M) hη (toModelFrame_near M hB)

private theorem inverse_mulVec_frameCoordinates {n : ℕ} (M : NormModel n) {η : ℝ}
    (hη : η < detMax M) {B : DualFrame n} (hB : B ∈ nearMaxFrames M η) (x : Coord n) :
    framePreimage B (frameCoordinates B x) = x := by
  exact DeterminantFrame.inverse_mulVec_frameCoordinates (modelBasis M) hη (toModelFrame_near M hB) (show EquivalentSeminorm.Space M from x)

private theorem abs_replacementDet_le_detMax {n : ℕ} (M : NormModel n) {B : DualFrame n} (hB : B ∈ dualFrameSet M)
    (i : Fin n) {r : Coord n →L[ℝ] ℝ} (hr : IsDualContraction M r) : |replacementDet B i r| ≤ detMax M := by
  have h := DeterminantFrame.abs_replacementDeterminant_le_maximum (modelBasis M) (toModelFrame_mem M hB) i ((toModelRow_mem_iff M r).mpr hr)
  have heq : (fun j => toModelRow M ((DeterminantFrame.replaceRow B i r) j)) =
      DeterminantFrame.replaceRow (fun j => toModelRow M (B j)) i (toModelRow M r) := by
    funext j
    by_cases hj : j = i <;> simp [DeterminantFrame.replaceRow, hj]
  change |DeterminantFrame.frameDeterminant (modelBasis M)
    (fun j => toModelRow M ((DeterminantFrame.replaceRow B i r) j))| ≤ detMax M
  rw [heq]
  exact h

private def maxFrame {n : ℕ} (M : NormModel n) : DualFrame n :=
  fun i => fromModelRow M (DeterminantFrame.maximizingFrame (modelBasis M) i)

private theorem maxFrame_det {n : ℕ} (M : NormModel n) : |frameDet (maxFrame M)| = detMax M := rfl

private theorem maxFrame_mem {n : ℕ} (M : NormModel n) : maxFrame M ∈ dualFrameSet M := by
  intro i
  apply (toModelRow_mem_iff M _).mp
  have h := DeterminantFrame.maximizingFrame_mem (modelBasis M) i
  convert h using 1
  ext x
  rfl


private abbrev replaceFrameRow {n : ℕ} := @DeterminantFrame.replaceRow n (Coord n) _ _
private abbrev functionalRow {n : ℕ} := DeterminantFrame.functionalCoordinates (Pi.basisFun ℝ (Fin n))
private theorem continuous_frameDet {n : ℕ} : Continuous (frameDet : DualFrame n → ℝ) :=
  DeterminantFrame.continuous_frameDeterminant (Pi.basisFun ℝ (Fin n))
private theorem dualFrameMatrix_replaceFrameRow {n : ℕ} (B : DualFrame n) (i : Fin n) (r : Coord n →L[ℝ] ℝ) :
    dualFrameMatrix (replaceFrameRow B i r) = (dualFrameMatrix B).updateRow i (functionalRow r) :=
  DeterminantFrame.frameMatrix_replaceRow (Pi.basisFun ℝ (Fin n)) B i r
private theorem sum_mul_replacementDet {n : ℕ} (B : DualFrame n) (hB : frameDet B ≠ 0) (r : Coord n →L[ℝ] ℝ) (c : Coord n) :
    (∑ i : Fin n, c i * replacementDet B i r) = frameDet B * r (framePreimage B c) :=
  DeterminantFrame.sum_mul_replacementDeterminant (Pi.basisFun ℝ (Fin n)) B hB r c

private theorem isCompact_dualRowSet {n : ℕ} (M : NormModel n) : IsCompact (dualRowSet M) := by
  have hc : IsClosed (dualRowSet M) := by
    have heq : dualRowSet M = (⋂ x : Coord n, {r : Coord n →L[ℝ] ℝ | |r x| ≤ M.p x}) := by ext r; simp [dualRowSet, IsDualContraction]
    rw [heq]
    exact isClosed_iInter fun x => isClosed_le (by fun_prop) continuous_const
  have hb : Bornology.IsBounded (dualRowSet M) := by
    apply (Metric.isBounded_iff_subset_closedBall (0 : Coord n →L[ℝ] ℝ)).2
    refine ⟨M.upper, ?_⟩
    intro r hr
    rw [Metric.mem_closedBall, dist_zero_right]
    apply ContinuousLinearMap.opNorm_le_bound _ M.upper_pos.le
    intro x
    exact (hr x).trans (M.le_upper x)
  exact Metric.isCompact_of_isClosed_isBounded hc hb

private theorem isCompact_dualFrameSet {n : ℕ} (M : NormModel n) : IsCompact (dualFrameSet M) := by
  have heq : dualFrameSet M = Set.univ.pi (fun _ : Fin n => dualRowSet M) := by ext B; simp [dualFrameSet, dualRowSet]
  rw [heq]
  exact isCompact_univ_pi fun _ => isCompact_dualRowSet M

namespace Internal
end Internal

open Internal
private theorem Internal.dualRowSet_eq_modelContractionSet {n : ℕ} (M : NormModel n) :
    dualRowSet M = EquivalentSeminorm.contractionSet M ℝ := by
  ext b
  simp [dualRowSet, IsDualContraction, EquivalentSeminorm.contractionSet, EquivalentSeminorm.IsContraction, Real.norm_eq_abs]


def satellitePolynomial {n : ℕ} {J : Type*} [Fintype J]
    (weight : ℝ) (coeff : J → Coord n)
    (B : DualFrame n) (sat : J → (Coord n →L[ℝ] ℝ)) : ℝ :=
  weight * frameDet B +
    ∑ a : J, ∑ i : Fin n, coeff a i * replacementDet B i (sat a)


private noncomputable def Internal.lineModelFunctional {n : ℕ} (M : NormModel n)
    (x : Coord n) (hx : x ≠ 0) :
    Module.Dual ℝ (ℝ ∙ x) :=
  (((M.p x) • ContinuousLinearEquiv.coord ℝ x hx) :
    (ℝ ∙ x) →L[ℝ] ℝ).toLinearMap


private theorem span_vector_eq_coord_smul {n : ℕ} (x : Coord n) (hx : x ≠ 0)
    (y : ℝ ∙ x) :
    (y : Coord n) = (ContinuousLinearEquiv.coord ℝ x hx y) • x := by
  have h := ContinuousLinearEquiv.toSpanNonzeroSingleton_coord ℝ hx y
  exact (congrArg Subtype.val h).symm


private theorem Internal.lineModelFunctional_le {n : ℕ} (M : NormModel n)
    (x : Coord n) (hx : x ≠ 0) (y : ℝ ∙ x) :
    lineModelFunctional M x hx y ≤ M.p (y : Coord n) := by
  let a : ℝ := ContinuousLinearEquiv.coord ℝ x hx y
  have hy : (y : Coord n) = a • x := by
    simpa [a] using span_vector_eq_coord_smul x hx y
  have hnonneg : 0 ≤ M.p x := apply_nonneg M.p x
  calc
    lineModelFunctional M x hx y = M.p x * a := by
      simp [lineModelFunctional, a]
    _ ≤ M.p x * |a| :=
      mul_le_mul_of_nonneg_left (le_abs_self a) hnonneg
    _ = |a| * M.p x := by ring
    _ = M.p (a • x) := by
      simpa [Real.norm_eq_abs] using (map_smul_eq_mul M.p a x).symm
    _ = M.p (y : Coord n) := by rw [hy]


private theorem exists_modelNormingFunctional {n : ℕ} (M : NormModel n)
    (x : Coord n) :
    ∃ r : Coord n →L[ℝ] ℝ,
      IsDualContraction M r ∧ r x = M.p x := by
  by_cases hx : x = 0
  · subst x
    refine ⟨0, ?_, by simp⟩
    intro y
    simp
  · let S : Subspace ℝ (Coord n) := ℝ ∙ x
    let f : Module.Dual ℝ S := lineModelFunctional M x hx
    obtain ⟨r, hrS, hrdom⟩ :=
      Module.Dual.exists_continuous_extension_of_le_seminorm_real
        S f M.continuous_p (fun y => lineModelFunctional_le M x hx y)
    refine ⟨r, ?_, ?_⟩
    · intro y
      exact hrdom y
    · have hself := hrS
        (⟨x, Submodule.mem_span_singleton_self x⟩ : S)
      simpa [S, f, lineModelFunctional] using hself


private theorem IsDualContraction.neg {n : ℕ} {M : NormModel n}
    {r : Coord n →L[ℝ] ℝ} (hr : IsDualContraction M r) :
    IsDualContraction M (-r) := by
  intro x
  simpa using hr x


private theorem Internal.exists_modelNormingEndpoints {n : ℕ} (M : NormModel n)
    (x : Coord n) :
    ∃ rPlus rMinus : Coord n →L[ℝ] ℝ,
      IsDualContraction M rPlus ∧
      IsDualContraction M rMinus ∧
      rPlus x = M.p x ∧
      rMinus x = -M.p x := by
  rcases exists_modelNormingFunctional M x with ⟨r, hr, hrx⟩
  refine ⟨r, -r, hr, hr.neg, hrx, ?_⟩
  simp [hrx]


def coefficientAnnulus {n : ℕ} (K : ℝ) : Set (Coord n) :=
  {c | K⁻¹ ≤ ‖c‖ ∧ ‖c‖ ≤ 1}


private theorem isClosed_coefficientAnnulus {n : ℕ} (K : ℝ) :
    IsClosed (coefficientAnnulus (n := n) K) := by
  change IsClosed ({c : Coord n | K⁻¹ ≤ ‖c‖} ∩ {c : Coord n | ‖c‖ ≤ 1})
  exact (isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const)


private theorem isBounded_coefficientAnnulus {n : ℕ} (K : ℝ) :
    Bornology.IsBounded (coefficientAnnulus (n := n) K) := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : Coord n)]
  refine ⟨1, ?_⟩
  intro c hc
  simpa [coefficientAnnulus, Metric.mem_closedBall, dist_eq_norm] using hc.2


private theorem isCompact_coefficientAnnulus {n : ℕ} (K : ℝ) :
    IsCompact (coefficientAnnulus (n := n) K) := by
  exact Metric.isCompact_of_isClosed_isBounded
    (isClosed_coefficientAnnulus K)
    (isBounded_coefficientAnnulus K)


structure FiniteCoefficientNet {n : ℕ} (K : ℝ) (ρ : ℝ≥0) where
  centers : Set (Coord n)
  centers_subset : centers ⊆ coefficientAnnulus K
  finite_centers : centers.Finite
  isCover : Metric.IsCover ρ (coefficientAnnulus K) centers


private theorem nonempty_finiteCoefficientNet {n : ℕ} (K : ℝ) {ρ : ℝ≥0}
    (hρ : ρ ≠ 0) : Nonempty (FiniteCoefficientNet (n := n) K ρ) := by
  rcases Metric.exists_finite_isCover_of_isCompact hρ
      (isCompact_coefficientAnnulus (n := n) K) with
    ⟨C, hCsub, hCfinite, hcover⟩
  exact ⟨⟨C, hCsub, hCfinite, hcover⟩⟩


variable {n : ℕ} {K : ℝ} {ρ : ℝ≥0}

private theorem FiniteCoefficientNet.exists_center (C : FiniteCoefficientNet (n := n) K ρ)
    {z : Coord n} (hz : z ∈ coefficientAnnulus K) :
    ∃ c ∈ C.centers, edist z c ≤ ρ :=
  C.isCover hz


variable {n : ℕ} {K : ℝ} {ρ : ℝ≥0}

private theorem FiniteCoefficientNet.center_mem_annulus (C : FiniteCoefficientNet (n := n) K ρ)
    {c : Coord n} (hc : c ∈ C.centers) : c ∈ coefficientAnnulus boundConstant :=
  C.centers_subset hc


variable {n : ℕ} {K : ℝ} {ρ : ℝ≥0}

private noncomputable instance Internal.centerFintype (C : FiniteCoefficientNet (n := n) K ρ) :
    Fintype C.centers :=
  C.centers_finite.fintype


variable {n : ℕ} {K : ℝ} {ρ : ℝ≥0}

private def Internal.centerValue (C : FiniteCoefficientNet (n := n) K ρ) (c : C.centers) :
    Coord n := c.1


private def Internal.satelliteRadius (ε K : ℝ) : ℝ := min ε 1 / (8 * K)


private theorem Internal.satelliteRadius_pos {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K) :
    0 < satelliteRadius ε boundConstant := by
  exact div_pos (lt_min hε zero_lt_one) (mul_pos (by norm_num) hK)


private theorem Internal.two_mul_bound_mul_satelliteRadius_lt_half {ε K : ℝ}
    (hε : 0 < ε) (hK : 0 < K) :
    2 * K * satelliteRadius ε K < ε / 2 := by
  have hden : 0 < 8 * boundConstant := mul_pos (by norm_num) hK
  have hmin : min ε 1 ≤ ε := min_le_left _ _
  unfold satelliteRadius
  calc
    2 * K * (min ε 1 / (8 * K)) = min ε 1 / 4 := by field_simp; ring
    _ ≤ ε / 4 := by linarith
    _ < ε / 2 := by linarith


private theorem Internal.satelliteRadius_lt_half_inv {ε K : ℝ}
    (_hε : 0 < ε) (hK : 0 < K) :
    satelliteRadius ε K < 1 / (2 * K) := by
  have hmin : min ε 1 ≤ 1 := min_le_right _ _
  unfold satelliteRadius
  have hK2 : 0 < 2 * boundConstant := mul_pos (by norm_num) hK
  have hK8 : 0 < 8 * boundConstant := mul_pos (by norm_num) hK
  calc
    min ε 1 / (8 * K) ≤ 1 / (8 * K) :=
      div_le_div_of_nonneg_right hmin hK8.le
    _ < 1 / (2 * K) := by
      apply one_div_lt_one_div_of_lt hK2
      nlinarith


private noncomputable def Internal.satelliteRadiusNNReal (ε K : ℝ) (hε : 0 < ε) (hK : 0 < K) :
    ℝ≥0 :=
  ⟨satelliteRadius ε K, (satelliteRadius_pos hε hK).le⟩


@[simp] private theorem Internal.coe_satelliteRadiusNNReal (ε K : ℝ) (hε : 0 < ε) (hK : 0 < K) :
    (satelliteRadiusNNReal ε K hε hK : ℝ) = satelliteRadius ε boundConstant := rfl


private theorem Internal.satelliteRadiusNNReal_ne_zero {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K) :
    satelliteRadiusNNReal ε K hε hK ≠ 0 := by
  exact ne_of_gt (by
    change 0 < satelliteRadius ε K
    exact satelliteRadius_pos hε hK)


theorem frameCoordinates_norm_le_model {n : ℕ} (M : NormModel n)
    {B : DualFrame n} (hB : B ∈ dualFrameSet M) (x : Coord n) :
    ‖frameCoordinates B x‖ ≤ M.p x := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ M.p x)).2
  intro i
  simpa [frameCoordinates, DeterminantFrame.frameCoordinates, Real.norm_eq_abs] using hB i x


theorem frameCoordinates_mem_coefficientAnnulus {n : ℕ}
    (M : NormModel n) {η : ℝ} (hη : η < detMax M)
    (H : NearMaxInverseBound M η) {B : DualFrame n}
    (hB : B ∈ nearMaxFrames M η) {x : Coord n}
    (hx : M.p x = 1) :
    frameCoordinates B x ∈ coefficientAnnulus H.boundConstant := by
  have hupper : ‖frameCoordinates B x‖ ≤ 1 := by
    simpa [hx] using frameCoordinates_norm_le_model M hB.1 x
  have hrec := inverse_mulVec_frameCoordinates M hη hB x
  have hinv : M.p x =
      M.p ((dualFrameMatrix B)⁻¹.mulVec (frameCoordinates B x)) := by
    exact congrArg M.p hrec.symm
  have hprod : 1 ≤ H.boundConstant * ‖frameCoordinates B x‖ := by
    calc
      1 = M.p x := hx.symm
      _ = M.p ((dualFrameMatrix B)⁻¹.mulVec (frameCoordinates B x)) := hinv
      _ ≤ H.boundConstant * ‖frameCoordinates B x‖ := seminorm_framePreimage_le M H hB _
  have hlower : H.boundConstant⁻¹ ≤ ‖frameCoordinates B x‖ := by
    have hdiv : 1 / H.boundConstant ≤ ‖frameCoordinates B x‖ :=
      (div_le_iff₀ H.boundConstant_pos).2 (by simpa [mul_comm] using hprod)
    simpa [one_div] using hdiv
  exact ⟨hlower, hupper⟩


theorem modelDist_framePreimage_le {n : ℕ} (M : NormModel n)
    {η : ℝ} (hη : η < detMax M) (H : NearMaxInverseBound M η) {B : DualFrame n}
    (hB : B ∈ nearMaxFrames M η) (x c : Coord n) :
    M.p (x - framePreimage B c) ≤
      H.boundConstant * ‖frameCoordinates B x - c‖ := by
  calc
    M.p (x - framePreimage B c) =
        M.p (framePreimage B (frameCoordinates B x) - framePreimage B c) := by
      rw [inverse_mulVec_frameCoordinates M hη hB x]
    _ = M.p (framePreimage B (frameCoordinates B x - c)) := by
      apply congrArg (fun y : Coord n => M.p y)
      simp [framePreimage, Matrix.mulVec_sub]
    _ ≤ H.boundConstant * ‖frameCoordinates B x - c‖ := by
      simpa [framePreimage] using seminorm_framePreimage_le M H hB (frameCoordinates B x - c)


private theorem Internal.FiniteCoefficientNet.exists_center_dist {n : ℕ} {K : ℝ} {ρ : ℝ≥0}
    (C : FiniteCoefficientNet (n := n) K ρ)
    {z : Coord n} (hz : z ∈ coefficientAnnulus K) :
    ∃ c ∈ C.centers, dist z c ≤ (ρ : ℝ) := by
  rcases C.isCover hz with ⟨c, hc, hdist⟩
  refine ⟨c, hc, ?_⟩
  exact_mod_cast hdist


theorem exists_net_preimage_close {n : ℕ} (M : NormModel n)
    {η : ℝ} (hη : η < detMax M) (H : NearMaxInverseBound M η)
    {ρ : ℝ≥0} (C : FiniteCoefficientNet (n := n) H.boundConstant ρ)
    {B : DualFrame n} (hB : B ∈ nearMaxFrames M η)
    {x : Coord n} (hx : M.p x = 1) :
    ∃ c ∈ C.centers,
      M.p (x - framePreimage B c) ≤ H.boundConstant * (ρ : ℝ) := by
  have hz : frameCoordinates B x ∈ coefficientAnnulus H.boundConstant :=
    frameCoordinates_mem_coefficientAnnulus M hη H hB hx
  rcases Internal.FiniteCoefficientNet.exists_center_dist C hz with ⟨c, hc, hdist⟩
  refine ⟨c, hc, ?_⟩
  calc
    M.p (x - framePreimage B c)
        ≤ H.boundConstant * ‖frameCoordinates B x - c‖ :=
      modelDist_framePreimage_le M hη H hB x c
    _ = H.boundConstant * dist (frameCoordinates B x) c := by
      rw [dist_eq_norm]
    _ ≤ H.boundConstant * (ρ : ℝ) :=
      mul_le_mul_of_nonneg_left hdist H.boundConstant_nonneg


def satelliteBudget {n : ℕ} {J : Type u} [Fintype J]
    (M : NormModel n) (coeff : J → Coord n) : ℝ :=
  detMax M * ∑ a : J, ∑ i : Fin n, |coeff a i|


private theorem Internal.satelliteBudget_nonneg {n : ℕ} {J : Type u} [Fintype J]
    (M : NormModel n) (coeff : J → Coord n) :
    0 ≤ satelliteBudget M coeff := by
  unfold satelliteBudget
  exact mul_nonneg (detMax_pos M).le
    (Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun i _ => abs_nonneg (coeff a i))


theorem abs_satelliteTerms_le_budget {n : ℕ} {J : Type u} [Fintype J]
    (M : NormModel n) (coeff : J → Coord n) {B : DualFrame n}
    (hB : B ∈ dualFrameSet M)
    (sat : J → (Coord n →L[ℝ] ℝ))
    (hsat : ∀ a, IsDualContraction M (sat a)) :
    |∑ a : J, ∑ i : Fin n,
        coeff a i * replacementDet B i (sat a)| ≤
      satelliteBudget M coeff := by
  calc
    |∑ a : J, ∑ i : Fin n,
        coeff a i * replacementDet B i (sat a)|
        ≤ ∑ a : J, |∑ i : Fin n,
            coeff a i * replacementDet B i (sat a)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : J, ∑ i : Fin n,
          |coeff a i * replacementDet B i (sat a)| := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : J, ∑ i : Fin n,
          |coeff a i| * detMax M := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_replacementDet_le_detMax M hB i (hsat a)) (abs_nonneg _)
    _ = satelliteBudget M coeff := by
      unfold satelliteBudget
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring


theorem abs_satellitePolynomial_le {n : ℕ} {J : Type u} [Fintype J]
    (M : NormModel n) {weight : ℝ} (hweight : 0 ≤ weight)
    (coeff : J → Coord n) {B : DualFrame n}
    (hB : B ∈ dualFrameSet M)
    (sat : J → (Coord n →L[ℝ] ℝ))
    (hsat : ∀ a, IsDualContraction M (sat a)) :
    |satellitePolynomial weight coeff B sat| ≤
      weight * |frameDet B| + satelliteBudget M coeff := by
  unfold satellitePolynomial
  calc
    |weight * frameDet B +
        ∑ a : J, ∑ i : Fin n,
          coeff a i * replacementDet B i (sat a)|
        ≤ |weight * frameDet B| +
          |∑ a : J, ∑ i : Fin n,
            coeff a i * replacementDet B i (sat a)| := abs_add_le _ _
    _ ≤ weight * |frameDet B| + satelliteBudget M coeff := by
      rw [abs_mul, abs_of_nonneg hweight]
      exact add_le_add le_rfl
        (abs_satelliteTerms_le_budget M coeff hB sat hsat)


theorem base_mem_nearMax_of_benchmark_le {n : ℕ} {J : Type u} [Fintype J]
    (M : NormModel n) {η weight : ℝ} (_hη0 : 0 ≤ η) (hweight : 0 < weight)
    (coeff : J → Coord n) {B : DualFrame n}
    (hB : B ∈ dualFrameSet M)
    (sat : J → (Coord n →L[ℝ] ℝ))
    (hsat : ∀ a, IsDualContraction M (sat a))
    (hgap : satelliteBudget M coeff < weight * η)
    (hbenchmark : weight * detMax M ≤
      |satellitePolynomial weight coeff B sat|) :
    B ∈ nearMaxFrames M η := by
  refine ⟨hB, ?_⟩
  by_contra hnear
  have hdet : |frameDet B| < detMax M - η := lt_of_not_ge hnear
  have hupper := abs_satellitePolynomial_le M hweight.le coeff hB sat hsat
  have hstrict :
      weight * |frameDet B| + satelliteBudget M coeff <
        weight * detMax M := by
    have hbase : weight * |frameDet B| < weight * (detMax M - η) :=
      mul_lt_mul_of_pos_left hdet hweight
    nlinarith
  exact (not_lt_of_ge hbenchmark) (hupper.trans_lt hstrict)


theorem exists_weight_dominating_budget {n : ℕ} {J : Type u} [Fintype J]
    (M : NormModel n) (coeff : J → Coord n) {η : ℝ} (hη : 0 < η) :
    ∃ weight : ℝ, 0 < weight ∧ satelliteBudget M coeff < weight * η := by
  refine ⟨satelliteBudget M coeff / η + 1, ?_, ?_⟩
  · have hbudget := satelliteBudget_nonneg M coeff
    have hdiv : 0 ≤ satelliteBudget M coeff / η := div_nonneg hbudget hη.le
    linarith
  · field_simp [hη.ne']
    nlinarith [satelliteBudget_nonneg M coeff]


abbrev SatelliteRows (n : ℕ) (J : Type u) := J → (Coord n →L[ℝ] ℝ)


abbrev SatelliteConfiguration (n : ℕ) (J : Type u) :=
  DualFrame n × SatelliteRows n J


def satelliteRowsSet {n : ℕ} (M : NormModel n) (J : Type u) :
    Set (SatelliteRows n J) :=
  {sat | ∀ a, IsDualContraction M (sat a)}


def satelliteConfigurationSet {n : ℕ} (M : NormModel n) (J : Type u) :
    Set (SatelliteConfiguration n J) :=
  dualFrameSet M ×ˢ satelliteRowsSet M J


@[simp] private theorem Internal.mem_satelliteRowsSet {n : ℕ} (M : NormModel n)
    (J : Type u) {sat : SatelliteRows n J} :
    sat ∈ satelliteRowsSet M J ↔ ∀ a, IsDualContraction M (sat a) := Iff.rfl


@[simp] private theorem Internal.mem_satelliteConfigurationSet {n : ℕ} (M : NormModel n)
    (J : Type u) {C : SatelliteConfiguration n J} :
    C ∈ satelliteConfigurationSet M J ↔
      C.1 ∈ dualFrameSet M ∧ ∀ a, IsDualContraction M (C.2 a) := Iff.rfl


private theorem isCompact_satelliteRowsSet {n : ℕ} (M : NormModel n)
    (J : Type u) [Fintype J] :
    IsCompact (satelliteRowsSet M J) := by
  have heq : satelliteRowsSet M J =
      Set.univ.pi (fun _ : J => dualRowSet M) := by
    ext sat
    simp [satelliteRowsSet, dualRowSet]
  rw [heq]
  exact isCompact_univ_pi fun _ => isCompact_dualRowSet M


private theorem isCompact_satelliteConfigurationSet {n : ℕ} (M : NormModel n)
    (J : Type u) [Fintype J] :
    IsCompact (satelliteConfigurationSet M J) := by
  exact (isCompact_dualFrameSet M).prod (isCompact_satelliteRowsSet M J)


private theorem satelliteConfigurationSet_nonempty {n : ℕ} (M : NormModel n)
    (J : Type u) :
    (satelliteConfigurationSet M J).Nonempty := by
  refine ⟨((fun _ => 0), fun _ => 0), ?_⟩
  constructor
  · intro i x
    simpa only [zero_apply, abs_zero] using (apply_nonneg M.p x)
  · intro a x
    simpa only [zero_apply, abs_zero] using (apply_nonneg M.p x)


def configurationPolynomial {n : ℕ} {J : Type u} [Fintype J]
    (weight : ℝ) (coeff : J → Coord n) :
    SatelliteConfiguration n J → ℝ :=
  fun C => satellitePolynomial weight coeff C.1 C.2


private theorem continuous_configurationPolynomial {n : ℕ} {J : Type u} [Fintype J]
    (weight : ℝ) (coeff : J → Coord n) :
    Continuous (configurationPolynomial weight coeff) := by
  change Continuous fun C : SatelliteConfiguration n J =>
    weight * frameDet C.1 +
      ∑ a : J, ∑ i : Fin n,
        coeff a i * replacementDet C.1 i (C.2 a)
  have hreplacement : ∀ (a : J) (i : Fin n),
      Continuous fun C : SatelliteConfiguration n J =>
        replacementDet C.1 i (C.2 a) := by
    intro a i
    unfold replacementDet DeterminantFrame.replacementDeterminant DeterminantFrame.frameDeterminant
    apply Continuous.matrix_det
    apply continuous_matrix
    intro k j
    simp only [DeterminantFrame.frameMatrix, Pi.basisFun_apply]
    change Continuous fun C : SatelliteConfiguration n J =>
      (replaceFrameRow C.1 i (C.2 a)) k (Pi.single j 1)
    by_cases hki : k = i
    · subst k
      simpa [replaceFrameRow, DeterminantFrame.replaceRow] using
        (show Continuous fun C : SatelliteConfiguration n J =>
          C.2 a (Pi.single j 1) by fun_prop)
    · simpa [replaceFrameRow, DeterminantFrame.replaceRow, hki] using
        (show Continuous fun C : SatelliteConfiguration n J =>
          C.1 k (Pi.single j 1) by fun_prop)
  apply Continuous.add
  · exact continuous_const.mul (frameDet_continuous.comp continuous_fst)
  · exact continuous_finsetSum Finset.univ fun a _ =>
      continuous_finsetSum Finset.univ fun i _ =>
        continuous_const.mul (hreplacement a i)


private theorem exists_maxSatelliteConfiguration {n : ℕ} (M : NormModel n)
    (J : Type u) [Fintype J] (weight : ℝ) (coeff : J → Coord n) :
    ∃ C ∈ satelliteConfigurationSet M J,
      ∀ D ∈ satelliteConfigurationSet M J,
        |configurationPolynomial weight coeff D| ≤
          |configurationPolynomial weight coeff C| := by
  rcases (isCompact_satelliteConfigurationSet M J).exists_isMaxOn
      (satelliteConfigurationSet_nonempty M J)
      (continuous_configurationPolynomial weight coeff).abs.continuousOn with
    ⟨C, hC, hmax⟩
  exact ⟨C, hC, hmax⟩


noncomputable def maxSatelliteConfiguration {n : ℕ} (M : NormModel n)
    (J : Type u) [Fintype J] (weight : ℝ) (coeff : J → Coord n) :
    SatelliteConfiguration n J :=
  Classical.choose (exists_maxSatelliteConfiguration M J weight coeff)


private theorem Internal.maxSatelliteConfiguration_mem {n : ℕ} (M : NormModel n)
    (J : Type u) [Fintype J] (weight : ℝ) (coeff : J → Coord n) :
    maxSatelliteConfiguration M J weight coeff ∈
      satelliteConfigurationSet M J :=
  (Classical.choose_spec
    (exists_maxSatelliteConfiguration M J weight coeff)).1


private theorem Internal.abs_configurationPolynomial_le_max {n : ℕ} (M : NormModel n)
    (J : Type u) [Fintype J] (weight : ℝ) (coeff : J → Coord n)
    {C : SatelliteConfiguration n J}
    (hC : C ∈ satelliteConfigurationSet M J) :
    |configurationPolynomial weight coeff C| ≤
      |configurationPolynomial weight coeff
        (maxSatelliteConfiguration M J weight coeff)| :=
  (Classical.choose_spec
    (exists_maxSatelliteConfiguration M J weight coeff)).2 C hC


@[simp] private theorem replacementDet_zero {n : ℕ} (B : DualFrame n) (i : Fin n) :
    replacementDet B i (0 : Coord n →L[ℝ] ℝ) = 0 := by
  change Matrix.det (dualFrameMatrix (replaceFrameRow B i 0)) = 0
  rw [dualFrameMatrix_replaceFrameRow]
  apply Matrix.det_eq_zero_of_row_eq_zero i
  intro j
  simp [functionalRow, DeterminantFrame.functionalCoordinates]


private noncomputable def Internal.benchmarkConfiguration {n : ℕ} (M : NormModel n)
    (J : Type u) : SatelliteConfiguration n J :=
  (maxFrame M, fun _ => 0)


private theorem Internal.benchmarkConfiguration_mem {n : ℕ} (M : NormModel n)
    (J : Type u) :
    benchmarkConfiguration M J ∈ satelliteConfigurationSet M J := by
  constructor
  · exact maxFrame_mem M
  · intro a x
    simpa only [benchmarkConfiguration, zero_apply, abs_zero] using
      (apply_nonneg M.p x)


private theorem Internal.abs_configurationPolynomial_benchmark {n : ℕ} (M : NormModel n)
    (J : Type u) [Fintype J] {weight : ℝ} (hweight : 0 ≤ weight)
    (coeff : J → Coord n) :
    |configurationPolynomial weight coeff (benchmarkConfiguration M J)| =
      weight * detMax M := by
  simp [configurationPolynomial, benchmarkConfiguration, satellitePolynomial,
    abs_mul, abs_of_nonneg hweight, maxFrame_det]


private theorem Internal.benchmark_le_maxSatelliteConfiguration {n : ℕ} (M : NormModel n)
    (J : Type u) [Fintype J] {weight : ℝ} (hweight : 0 ≤ weight)
    (coeff : J → Coord n) :
    weight * detMax M ≤
      |configurationPolynomial weight coeff
        (maxSatelliteConfiguration M J weight coeff)| := by
  rw [← abs_configurationPolynomial_benchmark M J hweight coeff]
  exact abs_configurationPolynomial_le_max M J weight coeff
    (benchmarkConfiguration_mem M J)


theorem absoluteMaximizer_base_nearMax {n : ℕ} {J : Type u}
    [Fintype J] (M : NormModel n) {η weight : ℝ}
    (hη0 : 0 ≤ η) (hweight : 0 < weight)
    (coeff : J → Coord n)
    (hgap : satelliteBudget M coeff < weight * η)
    {C : SatelliteConfiguration n J}
    (hC : C ∈ satelliteConfigurationSet M J)
    (hmax : ∀ D ∈ satelliteConfigurationSet M J,
      |configurationPolynomial weight coeff D| ≤
        |configurationPolynomial weight coeff C|) :
    C.1 ∈ nearMaxFrames M η := by
  apply base_mem_nearMax_of_benchmark_le M hη0 hweight coeff hC.1 C.2 hC.2 hgap
  calc
    weight * detMax M =
        |configurationPolynomial weight coeff (benchmarkConfiguration M J)| := by
      symm
      exact abs_configurationPolynomial_benchmark M J hweight.le coeff
    _ ≤ |configurationPolynomial weight coeff C| :=
      hmax (benchmarkConfiguration M J) (benchmarkConfiguration_mem M J)
    _ = |satellitePolynomial weight coeff C.1 C.2| := rfl


private theorem maxSatelliteConfiguration_base_nearMax {n : ℕ} {J : Type u}
    [Fintype J] (M : NormModel n) {η weight : ℝ}
    (hη0 : 0 ≤ η) (hweight : 0 < weight)
    (coeff : J → Coord n)
    (hgap : satelliteBudget M coeff < weight * η) :
    (maxSatelliteConfiguration M J weight coeff).1 ∈
      nearMaxFrames M η := by
  let C := maxSatelliteConfiguration M J weight coeff
  have hC : C ∈ satelliteConfigurationSet M J := by
    exact maxSatelliteConfiguration_mem M J weight coeff
  apply base_mem_nearMax_of_benchmark_le M hη0 hweight coeff hC.1 C.2 hC.2 hgap
  simpa [configurationPolynomial, C] using
    benchmark_le_maxSatelliteConfiguration M J hweight.le coeff


private theorem Internal.abs_add_eq_add_abs_of_mul_nonneg {a b : ℝ} (h : 0 ≤ a * b) :
    |a + b| = |a| + |b| := by
  rcases mul_nonneg_iff.mp h with hab | hab
  · rw [abs_of_nonneg hab.1, abs_of_nonneg hab.2,
      abs_of_nonneg (add_nonneg hab.1 hab.2)]
  · rw [abs_of_nonpos hab.1, abs_of_nonpos hab.2,
      abs_of_nonpos (add_nonpos hab.1 hab.2)]
    ring


private theorem Internal.abs_add_or_abs_sub_eq_add_abs (a b : ℝ) :
    |a + b| = |a| + |b| ∨ |a - b| = |a| + |b| := by
  by_cases h : 0 ≤ a * b
  · exact Or.inl (abs_add_eq_add_abs_of_mul_nonneg h)
  · right
    have hneg : 0 ≤ a * (-b) := by nlinarith
    simpa [sub_eq_add_neg, abs_neg] using
      (abs_add_eq_add_abs_of_mul_nonneg hneg)


theorem abs_affine_endpoint_rigidity
    {R d u p : ℝ} (hp : 0 ≤ p) (hu : |u| ≤ p) (hd : d ≠ 0)
    (hplus : |R + d * p| ≤ |R + d * u|)
    (hminus : |R - d * p| ≤ |R + d * u|) :
    |u| = p := by
  have hend : |R| + |d| * p ≤ |R + d * u| := by
    rcases abs_add_or_abs_sub_eq_add_abs R (d * p) with h | h
    · calc
        |R| + |d| * p = |R| + |d * p| := by
          rw [abs_mul, abs_of_nonneg hp]
        _ = |R + d * p| := h.symm
        _ ≤ |R + d * u| := hplus
    · calc
        |R| + |d| * p = |R| + |d * p| := by
          rw [abs_mul, abs_of_nonneg hp]
        _ = |R - d * p| := h.symm
        _ ≤ |R + d * u| := hminus
  have htri : |R + d * u| ≤ |R| + |d| * |u| := by
    calc
      |R + d * u| ≤ |R| + |d * u| := abs_add_le _ _
      _ = |R| + |d| * |u| := by rw [abs_mul]
  have hmul : |d| * p ≤ |d| * |u| := by
    linarith
  have hp_le : p ≤ |u| := by
    nlinarith [abs_pos.mpr hd]
  exact le_antisymm hu hp_le


private def Internal.satelliteRowContribution {n : ℕ} {J : Type u} [Fintype J]
    (coeff : J → Coord n) (B : DualFrame n)
    (sat : J → (Coord n →L[ℝ] ℝ)) (a : J) : ℝ :=
  ∑ i : Fin n, coeff a i * replacementDet B i (sat a)


private def Internal.satelliteRemainder {n : ℕ} {J : Type u} [Fintype J] [DecidableEq J]
    (weight : ℝ) (coeff : J → Coord n)
    (C : SatelliteConfiguration n J) (a : J) : ℝ :=
  weight * frameDet C.1 +
    Finset.sum (Finset.univ.erase a) (fun b =>
      satelliteRowContribution coeff C.1 C.2 b)


private theorem Internal.configurationPolynomial_eq_remainder_add {n : ℕ}
    {J : Type u} [Fintype J] [DecidableEq J]
    (weight : ℝ) (coeff : J → Coord n)
    (C : SatelliteConfiguration n J) (a : J) :
    configurationPolynomial weight coeff C =
      satelliteRemainder weight coeff C a +
        satelliteRowContribution coeff C.1 C.2 a := by
  have hsum := Finset.add_sum_erase (Finset.univ : Finset J)
    (fun b : J => satelliteRowContribution coeff C.1 C.2 b)
    (Finset.mem_univ a)
  change weight * frameDet C.1 +
      ∑ b : J, satelliteRowContribution coeff C.1 C.2 b =
    (weight * frameDet C.1 +
      Finset.sum (Finset.univ.erase a) (fun b =>
        satelliteRowContribution coeff C.1 C.2 b)) +
      satelliteRowContribution coeff C.1 C.2 a
  rw [← hsum]
  ring


private theorem satelliteRowContribution_eq_det_mul_eval {n : ℕ}
    {J : Type u} [Fintype J] (coeff : J → Coord n)
    {B : DualFrame n} (hB : frameDet B ≠ 0)
    (sat : J → (Coord n →L[ℝ] ℝ)) (a : J) :
    satelliteRowContribution coeff B sat a =
      frameDet B * sat a (framePreimage B (coeff a)) := by
  exact sum_mul_replacementDet B hB (sat a) (coeff a)


private def Internal.updateSatelliteConfiguration {n : ℕ} {J : Type u}
    [DecidableEq J] (C : SatelliteConfiguration n J) (a : J)
    (r : Coord n →L[ℝ] ℝ) : SatelliteConfiguration n J :=
  (C.1, Function.update C.2 a r)


private theorem Internal.updateSatelliteConfiguration_mem {n : ℕ} {J : Type u}
    [DecidableEq J] (M : NormModel n)
    {C : SatelliteConfiguration n J}
    (hC : C ∈ satelliteConfigurationSet M J) (a : J)
    {r : Coord n →L[ℝ] ℝ} (hr : IsDualContraction M r) :
    updateSatelliteConfiguration C a r ∈ satelliteConfigurationSet M J := by
  constructor
  · exact hC.1
  · intro b
    by_cases hba : b = a
    · subst b
      simpa [updateSatelliteConfiguration] using hr
    · simpa [updateSatelliteConfiguration, hba] using hC.2 b


private theorem Internal.satelliteRemainder_update {n : ℕ} {J : Type u}
    [Fintype J] [DecidableEq J]
    (weight : ℝ) (coeff : J → Coord n)
    (C : SatelliteConfiguration n J) (a : J)
    (r : Coord n →L[ℝ] ℝ) :
    satelliteRemainder weight coeff
      (updateSatelliteConfiguration C a r) a =
      satelliteRemainder weight coeff C a := by
  unfold satelliteRemainder updateSatelliteConfiguration
  apply congrArg (fun t : ℝ => weight * frameDet C.1 + t)
  apply Finset.sum_congr rfl
  intro b hb
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  simp [satelliteRowContribution, hba]


private theorem Internal.configurationPolynomial_update_eq {n : ℕ} {J : Type u}
    [Fintype J] [DecidableEq J]
    (weight : ℝ) (coeff : J → Coord n)
    (C : SatelliteConfiguration n J) (a : J)
    (r : Coord n →L[ℝ] ℝ) (hdet : frameDet C.1 ≠ 0) :
    configurationPolynomial weight coeff
      (updateSatelliteConfiguration C a r) =
      satelliteRemainder weight coeff C a +
        frameDet C.1 * r (framePreimage C.1 (coeff a)) := by
  rw [configurationPolynomial_eq_remainder_add,
    satelliteRemainder_update]
  change satelliteRemainder weight coeff C a +
      satelliteRowContribution coeff C.1 (Function.update C.2 a r) a =
    satelliteRemainder weight coeff C a +
      frameDet C.1 * r (framePreimage C.1 (coeff a))
  rw [satelliteRowContribution_eq_det_mul_eval coeff hdet]
  simp


theorem absoluteMaximizer_satellite_norms_preimage {n : ℕ}
    (M : NormModel n) {J : Type u} [Fintype J] [DecidableEq J]
    {η weight : ℝ} (hηD : η < detMax M)
    (coeff : J → Coord n)
    {C : SatelliteConfiguration n J}
    (hC : C ∈ satelliteConfigurationSet M J)
    (hnear : C.1 ∈ nearMaxFrames M η)
    (hmax : ∀ D ∈ satelliteConfigurationSet M J,
      |configurationPolynomial weight coeff D| ≤
        |configurationPolynomial weight coeff C|)
    (a : J) :
    |C.2 a (framePreimage C.1 (coeff a))| =
      M.p (framePreimage C.1 (coeff a)) := by
  let z : Coord n := framePreimage C.1 (coeff a)
  let R : ℝ := satelliteRemainder weight coeff C a
  let d : ℝ := frameDet C.1
  let u : ℝ := C.2 a z
  let p : ℝ := M.p z
  have hd : d ≠ 0 := by
    simpa [d] using nearMaxFrame_det_ne_zero M hηD hnear
  have hu : |u| ≤ p := by
    simpa [u, p] using hC.2 a z
  have hp : 0 ≤ p := by
    exact apply_nonneg M.p z
  rcases exists_modelNormingEndpoints M z with
    ⟨rPlus, rMinus, hrPlus, hrMinus, hrPlusZ, hrMinusZ⟩
  have hself : updateSatelliteConfiguration C a (C.2 a) = C := by
    have hsat : Function.update C.2 a (C.2 a) = C.2 := by
      funext b
      by_cases hba : b = a
      · subst b
        simp
      · simp [hba]
    exact Prod.ext rfl hsat
  have hcurrent :
      configurationPolynomial weight coeff C = R + d * u := by
    have hformula :=
      configurationPolynomial_update_eq weight coeff C a (C.2 a) hd
    rw [hself] at hformula
    simpa [R, d, u, z] using hformula
  have hplus : |R + d * p| ≤ |R + d * u| := by
    have hm := hmax (updateSatelliteConfiguration C a rPlus)
      (updateSatelliteConfiguration_mem M hC a hrPlus)
    rw [configurationPolynomial_update_eq weight coeff C a rPlus hd,
      hcurrent] at hm
    simpa [R, d, p, z, hrPlusZ] using hm
  have hminus : |R - d * p| ≤ |R + d * u| := by
    have hm := hmax (updateSatelliteConfiguration C a rMinus)
      (updateSatelliteConfiguration_mem M hC a hrMinus)
    rw [configurationPolynomial_update_eq weight coeff C a rMinus hd,
      hcurrent] at hm
    simpa [R, d, p, z, hrMinusZ, sub_eq_add_neg] using hm
  simpa [u, p, z] using
    abs_affine_endpoint_rigidity hp hu hd hplus hminus


def CoefficientDetectsUnit {n : ℕ} (M : NormModel n) {J : Type u}
    (η : ℝ) (H : NearMaxInverseBound M η) (ρ : ℝ)
    (coeff : J → Coord n) : Prop :=
  ∀ ⦃B : DualFrame n⦄, B ∈ nearMaxFrames M η →
    ∀ ⦃x : Coord n⦄, M.p x = 1 →
      ∃ a : J, M.p (x - framePreimage B (coeff a)) ≤ H.boundConstant * ρ


private theorem Internal.model_sub_error_le_model {n : ℕ} (M : NormModel n)
    (x z : Coord n) :
    M.p x - M.p (x - z) ≤ M.p z := by
  have h := map_add_le_add M.p (x - z) z
  have hx : (x - z) + z = x := sub_add_cancel x z
  rw [hx] at h
  linarith


theorem abs_eval_lower_of_norms_nearby {n : ℕ} (M : NormModel n)
    {r : Coord n →L[ℝ] ℝ} (hr : IsDualContraction M r)
    {x z : Coord n} (hx : M.p x = 1)
    {δ : ℝ} (hδ : M.p (x - z) ≤ δ)
    (hnorm : |r z| = M.p z) :
    1 - 2 * δ ≤ |r x| := by
  have hpz : 1 - δ ≤ M.p z := by
    have := model_sub_error_le_model M x z
    rw [hx] at this
    linarith
  have hdiff : |r (x - z)| ≤ δ := (hr (x - z)).trans hδ
  have hlin : r z = r x - r (x - z) := by
    have hmap := r.map_sub x z
    linarith
  have hz_le : |r z| ≤ |r x| + δ := by
    calc
      |r z| = |r x - r (x - z)| := by rw [hlin]
      _ ≤ |r x| + |r (x - z)| := abs_sub _ _
      _ ≤ |r x| + δ := add_le_add le_rfl hdiff
  rw [hnorm] at hz_le
  linarith


theorem absoluteMaximizer_satellites_almost_norm {n : ℕ}
    (M : NormModel n) {J : Type u} [Fintype J] [DecidableEq J]
    {η weight ρ : ℝ} (hηD : η < detMax M)
    (H : NearMaxInverseBound M η) (coeff : J → Coord n)
    (hdetect : CoefficientDetectsUnit M η H ρ coeff)
    {C : SatelliteConfiguration n J}
    (hC : C ∈ satelliteConfigurationSet M J)
    (hnear : C.1 ∈ nearMaxFrames M η)
    (hmax : ∀ D ∈ satelliteConfigurationSet M J,
      |configurationPolynomial weight coeff D| ≤
        |configurationPolynomial weight coeff C|)
    {x : Coord n} (hx : M.p x = 1) :
    ∃ a : J, 1 - 2 * (H.boundConstant * ρ) ≤ |C.2 a x| := by
  rcases hdetect hnear hx with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  let z : Coord n := framePreimage C.1 (coeff a)
  have hnorm : |C.2 a z| = M.p z := by
    simpa [z] using absoluteMaximizer_satellite_norms_preimage
      M hηD coeff hC hnear hmax a
  exact abs_eval_lower_of_norms_nearby M (hC.2 a) hx ha hnorm


theorem absoluteMaximizer_satellites_one_sub_epsilon {n : ℕ}
    (M : NormModel n) {J : Type u} [Fintype J] [DecidableEq J]
    {η weight ε : ℝ} (hηD : η < detMax M) (hε : 0 < ε)
    (H : NearMaxInverseBound M η) (coeff : J → Coord n)
    (hdetect : CoefficientDetectsUnit M η H (satelliteRadius ε H.boundConstant) coeff)
    {C : SatelliteConfiguration n J}
    (hC : C ∈ satelliteConfigurationSet M J)
    (hnear : C.1 ∈ nearMaxFrames M η)
    (hmax : ∀ D ∈ satelliteConfigurationSet M J,
      |configurationPolynomial weight coeff D| ≤
        |configurationPolynomial weight coeff C|)
    {x : Coord n} (hx : M.p x = 1) :
    ∃ a : J, 1 - ε < |C.2 a x| := by
  rcases absoluteMaximizer_satellites_almost_norm M hηD H coeff hdetect
      hC hnear hmax hx with ⟨a, ha⟩
  refine ⟨a, lt_of_lt_of_le ?_ ha⟩
  have hr := two_mul_bound_mul_satelliteRadius_lt_half hε H.boundConstant_pos
  nlinarith


theorem finiteCoefficientNet_detectsUnit {n : ℕ} (M : NormModel n)
    {η : ℝ} (hηD : η < detMax M) (H : NearMaxInverseBound M η)
    {ρ : ℝ≥0} (C : FiniteCoefficientNet (n := n) H.boundConstant ρ) :
    CoefficientDetectsUnit M η H (ρ : ℝ) (Internal.centerValue C) := by
  intro B hB x hx
  rcases exists_net_preimage_close M hηD H C hB hx with
    ⟨c, hc, hclose⟩
  exact ⟨⟨c, hc⟩, by simpa [Internal.centerValue] using hclose⟩


theorem finiteNet_absoluteMaximizer_satellites_one_sub_epsilon
    {n : ℕ} (M : NormModel n) {η ε weight : ℝ}
    (hη0 : 0 ≤ η) (hηD : η < detMax M) (hε : 0 < ε)
    (H : NearMaxInverseBound M η)
    (Cnet : FiniteCoefficientNet (n := n) H.boundConstant
      (satelliteRadiusNNReal ε H.boundConstant hε H.boundConstant_pos))
    (hweight : 0 < weight)
    (hgap : satelliteBudget M (Internal.centerValue Cnet) < weight * η)
    {Q : SatelliteConfiguration n Cnet.centers}
    (hQ : Q ∈ satelliteConfigurationSet M Cnet.centers)
    (hmax : ∀ D ∈ satelliteConfigurationSet M Cnet.centers,
      |configurationPolynomial weight (Internal.centerValue Cnet) D| ≤
        |configurationPolynomial weight (Internal.centerValue Cnet) Q|)
    {x : Coord n} (hx : M.p x = 1) :
    ∃ a : Cnet.centers, 1 - ε < |Q.2 a x| := by
  have hnear : Q.1 ∈ nearMaxFrames M η :=
    absoluteMaximizer_base_nearMax M hη0 hweight (Internal.centerValue Cnet) hgap hQ hmax
  have hdetect : CoefficientDetectsUnit M η H
      (satelliteRadius ε H.boundConstant) (Internal.centerValue Cnet) := by
    simpa using finiteCoefficientNet_detectsUnit M hηD H Cnet
  exact absoluteMaximizer_satellites_one_sub_epsilon
    M hηD hε H (Internal.centerValue Cnet) hdetect hQ hnear hmax hx


private theorem maxNetSatelliteConfiguration_satellites_one_sub_epsilon
    {n : ℕ} (M : NormModel n) {η ε weight : ℝ}
    (hη0 : 0 ≤ η) (hηD : η < detMax M) (hε : 0 < ε)
    (H : NearMaxInverseBound M η)
    (C : FiniteCoefficientNet (n := n) H.boundConstant
      (satelliteRadiusNNReal ε H.boundConstant hε H.boundConstant_pos))
    (hweight : 0 < weight)
    (hgap : satelliteBudget M (Internal.centerValue C) < weight * η)
    {x : Coord n} (hx : M.p x = 1) :
    ∃ a : C.centers,
      1 - ε <
        |(maxSatelliteConfiguration M C.centers weight (Internal.centerValue C)).2 a x| := by
  let Q := maxSatelliteConfiguration M C.centers weight (Internal.centerValue C)
  have hQ : Q ∈ satelliteConfigurationSet M C.centers := by
    exact maxSatelliteConfiguration_mem M C.centers weight (Internal.centerValue C)
  have hmax : ∀ D ∈ satelliteConfigurationSet M C.centers,
      |configurationPolynomial weight (Internal.centerValue C) D| ≤
        |configurationPolynomial weight (Internal.centerValue C) Q| := by
    intro D hD
    simpa [Q] using abs_configurationPolynomial_le_max
      M C.centers weight (Internal.centerValue C) hD
  simpa [Q] using finiteNet_absoluteMaximizer_satellites_one_sub_epsilon
    M hη0 hηD hε H C hweight hgap hQ hmax hx


theorem exists_goodNetSatelliteMaximizer
    {n : ℕ} (M : NormModel n) {η ε : ℝ}
    (hη : 0 < η) (hηD : η < detMax M) (hε : 0 < ε)
    (H : NearMaxInverseBound M η)
    (C : FiniteCoefficientNet (n := n) H.boundConstant
      (satelliteRadiusNNReal ε H.boundConstant hε H.boundConstant_pos)) :
    ∃ weight : ℝ,
      0 < weight ∧
      satelliteBudget M (Internal.centerValue C) < weight * η ∧
      ∀ x : Coord n, M.p x = 1 →
        ∃ a : C.centers,
          1 - ε <
            |(maxSatelliteConfiguration M C.centers weight (Internal.centerValue C)).2 a x| := by
  rcases exists_weight_dominating_budget M (Internal.centerValue C) hη with
    ⟨weight, hweight, hgap⟩
  refine ⟨weight, hweight, hgap, ?_⟩
  intro x hx
  exact maxNetSatelliteConfiguration_satellites_one_sub_epsilon
    M hη.le hηD hε H C hweight hgap hx


theorem exists_goodSatellitePackage
    {n : ℕ} (M : NormModel n) {η ε : ℝ}
    (hη : 0 < η) (hηD : η < detMax M) (hε : 0 < ε) :
    ∃ H : NearMaxInverseBound M η,
      ∃ C : FiniteCoefficientNet (n := n) H.boundConstant
        (satelliteRadiusNNReal ε H.boundConstant hε H.boundConstant_pos),
        ∃ weight : ℝ,
          0 < weight ∧
          satelliteBudget M (Internal.centerValue C) < weight * η ∧
          ∀ x : Coord n, M.p x = 1 →
            ∃ a : C.centers,
              1 - ε <
                |(maxSatelliteConfiguration M C.centers
                    weight (Internal.centerValue C)).2 a x| := by
  rcases DeterminantFrame.nonempty_nearMaxInverseBound (modelBasis M) hη.le hηD with ⟨H⟩
  rcases nonempty_finiteCoefficientNet H.boundConstant
      (satelliteRadiusNNReal_ne_zero hε H.boundConstant_pos) with ⟨C⟩
  rcases exists_goodNetSatelliteMaximizer M hη hηD hε H C with
    ⟨weight, hweight, hgap, hgood⟩
  exact ⟨H, C, weight, hweight, hgap, hgood⟩

end MathlibAnnex.Satellite
