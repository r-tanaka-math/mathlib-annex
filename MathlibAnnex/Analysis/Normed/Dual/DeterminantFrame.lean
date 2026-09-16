import MathlibAnnex.LinearAlgebra.Matrix.MaximalMinor
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-!
# Determinant-maximizing dual frames

This module is the R07 generalization candidate.  It is deliberately stated for
an arbitrary finite-dimensional real normed space together with an explicit
basis indexed by `Fin n`.  The numerical determinant maximum therefore retains
its dependence on the chosen basis.

The proof has three parts.

* The product of the dual unit ball is compact, so the absolute determinant has
  an attained maximum.  A uniformly scaled coordinate frame belongs to that
  product and has positive determinant, including when `n = 0`.
* Replacing one row gives the row form of Cramer's identity, using Mathlib's
  `Matrix.det_smul_inv_vecMul_eq_cramer_transpose`.
* A frame whose determinant is within `η` of the maximum has an explicit common
  inverse bound.  The estimate is coordinatewise and is then transported back
  through the inverse coordinate equivalence.

The R03 read-only dependency is used only through
`MathlibAnnex.Matrix.mulVec_injective_of_maximalMinor_ne_zero`; this module does
not re-declare maximal minors or determinant perturbation bounds.

This source preserves the dispatch statement design, with explicit basis
coordinates and the zero-dimensional boundary. Local qualification and repair
evidence are recorded separately; formal admission is outside this module.
-/

noncomputable section

set_option autoImplicit false

open Set Module
open scoped BigOperators

namespace MathlibAnnex
namespace DeterminantFrame

universe u

variable {n : ℕ}
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An ordered family of continuous linear functionals. -/
abbrev Frame (n : ℕ) (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  Fin n → (E →L[ℝ] ℝ)

/-- The continuous coordinate equivalence attached to the displayed basis. -/
noncomputable def coordinateEquiv (b : Basis (Fin n) ℝ E) : E ≃L[ℝ] (Fin n → ℝ) :=
  b.equivFun.toContinuousLinearEquiv

/-- The inverse coordinate map, named so its operator norm can appear explicitly. -/
noncomputable def inverseCoordinateMap (b : Basis (Fin n) ℝ E) :
    (Fin n → ℝ) →L[ℝ] E :=
  (coordinateEquiv b).symm.toContinuousLinearMap

/-- Matrix of a dual frame in the displayed basis. -/
def frameMatrix (b : Basis (Fin n) ℝ E) (B : Frame n E) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => B i (b j)

/-- Determinant of a dual frame in the displayed basis. -/
def frameDeterminant (b : Basis (Fin n) ℝ E) (B : Frame n E) : ℝ :=
  Matrix.det (frameMatrix b B)

/-- Evaluation map associated to a frame. -/
def frameMap (B : Frame n E) : E →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => B i

/-- Coordinate vector produced by a frame. -/
def frameCoordinates (B : Frame n E) (x : E) : Fin n → ℝ :=
  fun i => B i x

/-- A dual row belongs to the closed operator-norm unit ball. -/
def unitRowSet (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Set (E →L[ℝ] ℝ) :=
  Metric.closedBall 0 1

/-- Product of the dual operator-norm unit balls. -/
def unitFrameSet (n : ℕ) (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Set (Frame n E) :=
  {B | ∀ i, B i ∈ unitRowSet E}

@[simp] theorem mem_unitRowSet {r : E →L[ℝ] ℝ} :
    r ∈ unitRowSet E ↔ ‖r‖ ≤ 1 := by
  simp [unitRowSet, Metric.mem_closedBall, dist_eq_norm]

@[simp] theorem mem_unitFrameSet {B : Frame n E} :
    B ∈ unitFrameSet n E ↔ ∀ i, ‖B i‖ ≤ 1 := by
  simp [unitFrameSet]

/-- Frame coordinates equal matrix multiplication on basis coordinates. -/
theorem frameCoordinates_eq_mulVec (b : Basis (Fin n) ℝ E)
    (B : Frame n E) (x : E) :
    frameCoordinates B x = (frameMatrix b B).mulVec (coordinateEquiv b x) := by
  funext i
  change B i x = ∑ j : Fin n, B i (b j) * coordinateEquiv b x j
  calc
    B i x = B i (∑ j : Fin n, (coordinateEquiv b x j) • b j) := by
      change B i x = B i (∑ j : Fin n, b.equivFun x j • b j)
      rw [b.sum_equivFun]
    _ = ∑ j : Fin n, B i ((coordinateEquiv b x j) • b j) := by
      rw [map_sum]
    _ = ∑ j : Fin n, B i (b j) * coordinateEquiv b x j := by
      apply Finset.sum_congr rfl
      intro j _
      simp [mul_comm]

/-- Continuity of the frame determinant. -/
theorem frameDeterminant_continuous (b : Basis (Fin n) ℝ E) :
    Continuous (frameDeterminant b : Frame n E → ℝ) := by
  apply Continuous.matrix_det
  apply continuous_matrix
  intro i j
  change Continuous fun B : Frame n E => B i (b j)
  fun_prop

/-- The dual unit ball is compact in finite dimension. -/
theorem unitRowSet_isCompact : IsCompact (unitRowSet E) := by
  letI : ProperSpace (E →L[ℝ] ℝ) := FiniteDimensional.proper ℝ (E →L[ℝ] ℝ)
  exact isCompact_closedBall 0 1

/-- The frame set is a compact finite product. -/
theorem unitFrameSet_isCompact : IsCompact (unitFrameSet n E) := by
  have heq : unitFrameSet n E = Set.univ.pi (fun _ : Fin n => unitRowSet E) := by
    ext B
    simp [unitFrameSet]
  rw [heq]
  exact isCompact_univ_pi fun _ => unitRowSet_isCompact

/-- The zero frame witnesses nonemptiness. -/
theorem unitFrameSet_nonempty : (unitFrameSet n E).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  simp

/-- Existence of an attained absolute determinant maximum. -/
theorem exists_maximizingFrame (b : Basis (Fin n) ℝ E) :
    ∃ B ∈ unitFrameSet n E,
      ∀ C ∈ unitFrameSet n E,
        |frameDeterminant b C| ≤ |frameDeterminant b B| := by
  rcases unitFrameSet_isCompact.exists_isMaxOn unitFrameSet_nonempty
      (frameDeterminant_continuous b).abs.continuousOn with ⟨B, hB, hmax⟩
  exact ⟨B, hB, hmax⟩

/-- A selected maximizing frame. -/
noncomputable def maximizingFrame (b : Basis (Fin n) ℝ E) : Frame n E :=
  Classical.choose (exists_maximizingFrame b)

/-- The selected frame lies in the product of dual unit balls. -/
theorem maximizingFrame_mem (b : Basis (Fin n) ℝ E) :
    maximizingFrame b ∈ unitFrameSet n E :=
  (Classical.choose_spec (exists_maximizingFrame b)).1

/-- Every admissible determinant is bounded by the selected maximum. -/
theorem abs_frameDeterminant_le_maximizingFrame (b : Basis (Fin n) ℝ E)
    {B : Frame n E} (hB : B ∈ unitFrameSet n E) :
    |frameDeterminant b B| ≤ |frameDeterminant b (maximizingFrame b)| :=
  (Classical.choose_spec (exists_maximizingFrame b)).2 B hB

/-- The attained absolute determinant maximum for the displayed basis. -/
noncomputable def determinantMaximum (b : Basis (Fin n) ℝ E) : ℝ :=
  |frameDeterminant b (maximizingFrame b)|

/-- Raw coordinate rows, before the common contraction factor is applied. -/
noncomputable def rawCoordinateRow (b : Basis (Fin n) ℝ E) (i : Fin n) :
    E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (coordinateEquiv b).toContinuousLinearMap

/-- Sum of the operator norms of the coordinate rows. -/
noncomputable def coordinateRowSize (b : Basis (Fin n) ℝ E) : ℝ :=
  ∑ i : Fin n, ‖rawCoordinateRow b i‖

/-- A positive common scaling factor placing every coordinate row in the dual unit ball. -/
noncomputable def coordinateScale (b : Basis (Fin n) ℝ E) : ℝ :=
  (1 + coordinateRowSize b)⁻¹

/-- The coordinate-row size is nonnegative. -/
theorem coordinateRowSize_nonneg (b : Basis (Fin n) ℝ E) :
    0 ≤ coordinateRowSize b := by
  exact Finset.sum_nonneg fun i _ => norm_nonneg (rawCoordinateRow b i)

/-- The common coordinate scaling factor is strictly positive, also for `n = 0`. -/
theorem coordinateScale_pos (b : Basis (Fin n) ℝ E) :
    0 < coordinateScale b := by
  apply inv_pos.mpr
  linarith [coordinateRowSize_nonneg b]

/-- Each raw coordinate row is bounded by the aggregate size. -/
theorem norm_rawCoordinateRow_le_size (b : Basis (Fin n) ℝ E) (i : Fin n) :
    ‖rawCoordinateRow b i‖ ≤ coordinateRowSize b := by
  unfold coordinateRowSize
  exact Finset.single_le_sum (fun j _ => norm_nonneg (rawCoordinateRow b j))
    (Finset.mem_univ i)

/-- Scaled coordinate row. -/
noncomputable def coordinateRow (b : Basis (Fin n) ℝ E) (i : Fin n) :
    E →L[ℝ] ℝ :=
  coordinateScale b • rawCoordinateRow b i

/-- Explicit scaled coordinate frame. -/
noncomputable def coordinateFrame (b : Basis (Fin n) ℝ E) : Frame n E :=
  fun i => coordinateRow b i

/-- Evaluation of a scaled coordinate row. -/
@[simp] theorem coordinateRow_apply (b : Basis (Fin n) ℝ E)
    (i : Fin n) (x : E) :
    coordinateRow b i x = coordinateScale b * coordinateEquiv b x i := by
  simp [coordinateRow, rawCoordinateRow]

/-- Every scaled coordinate row has operator norm at most one. -/
theorem coordinateFrame_mem (b : Basis (Fin n) ℝ E) :
    coordinateFrame b ∈ unitFrameSet n E := by
  rw [mem_unitFrameSet]
  intro i
  rw [show coordinateFrame b i = coordinateScale b • rawCoordinateRow b i from rfl,
    norm_smul, Real.norm_eq_abs, abs_of_pos (coordinateScale_pos b)]
  have hden : 0 < 1 + coordinateRowSize b := by
    linarith [coordinateRowSize_nonneg b]
  have hrow := norm_rawCoordinateRow_le_size b i
  rw [coordinateScale]
  apply (inv_mul_le_one₀ hden).2
  linarith

/-- Matrix of the explicit coordinate frame. -/
theorem frameMatrix_coordinateFrame (b : Basis (Fin n) ℝ E) :
    frameMatrix b (coordinateFrame b) =
      coordinateScale b • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [frameMatrix, coordinateFrame, coordinateRow_apply, coordinateEquiv]
  · simp [frameMatrix, coordinateFrame, coordinateRow_apply, coordinateEquiv, hij, Ne.symm hij]

/-- Determinant of the explicit coordinate frame. -/
theorem frameDeterminant_coordinateFrame (b : Basis (Fin n) ℝ E) :
    frameDeterminant b (coordinateFrame b) = coordinateScale b ^ n := by
  rw [frameDeterminant, frameMatrix_coordinateFrame]
  simp

/-- The basis-dependent determinant maximum is positive.  In dimension zero,
`coordinateRowSize = 0`, the empty determinant is `1`, and the same proof applies. -/
theorem determinantMaximum_pos (b : Basis (Fin n) ℝ E) :
    0 < determinantMaximum b := by
  unfold determinantMaximum
  have hle := abs_frameDeterminant_le_maximizingFrame b (coordinateFrame_mem b)
  have hpos : 0 < |frameDeterminant b (coordinateFrame b)| := by
    rw [frameDeterminant_coordinateFrame,
      abs_of_pos (pow_pos (coordinateScale_pos b) n)]
    exact pow_pos (coordinateScale_pos b) n
  exact hpos.trans_le hle

/-- Replace one row of a frame. -/
def replaceRow (B : Frame n E) (i : Fin n) (r : E →L[ℝ] ℝ) : Frame n E :=
  Function.update B i r

/-- Determinant after replacing one row. -/
def replacementDeterminant (b : Basis (Fin n) ℝ E)
    (B : Frame n E) (i : Fin n) (r : E →L[ℝ] ℝ) : ℝ :=
  frameDeterminant b (replaceRow B i r)

/-- Coordinates of one functional in the displayed basis. -/
def functionalCoordinates (b : Basis (Fin n) ℝ E) (r : E →L[ℝ] ℝ) :
    Fin n → ℝ :=
  fun j => r (b j)

/-- Replacing a frame row is matrix row replacement. -/
@[simp] theorem frameMatrix_replaceRow (b : Basis (Fin n) ℝ E)
    (B : Frame n E) (i : Fin n) (r : E →L[ℝ] ℝ) :
    frameMatrix b (replaceRow B i r) =
      (frameMatrix b B).updateRow i (functionalCoordinates b r) := by
  ext k j
  by_cases hki : k = i
  · subst k
    simp [frameMatrix, replaceRow, functionalCoordinates]
  · simp [frameMatrix, replaceRow, hki]

/-- A continuous linear functional is the dot product with its basis-coordinate row. -/
theorem functional_apply_eq_sum (b : Basis (Fin n) ℝ E)
    (r : E →L[ℝ] ℝ) (x : E) :
    r x = ∑ j : Fin n, functionalCoordinates b r j * coordinateEquiv b x j := by
  calc
    r x = r (∑ j : Fin n, (coordinateEquiv b x j) • b j) := by
      change r x = r (∑ j : Fin n, b.equivFun x j • b j)
      rw [b.sum_equivFun]
    _ = ∑ j : Fin n, r ((coordinateEquiv b x j) • b j) := by
      rw [map_sum]
    _ = ∑ j : Fin n, functionalCoordinates b r j * coordinateEquiv b x j := by
      apply Finset.sum_congr rfl
      intro j _
      simp [functionalCoordinates, mul_comm]

/-- One row-replacement determinant is the matching row-Cramer coordinate. -/
theorem replacementDeterminant_eq_cramerTranspose
    (b : Basis (Fin n) ℝ E) (B : Frame n E)
    (i : Fin n) (r : E →L[ℝ] ℝ) :
    replacementDeterminant b B i r =
      Matrix.cramer (Matrix.transpose (frameMatrix b B))
        (functionalCoordinates b r) i := by
  rw [Matrix.cramer_transpose_apply]
  simp [replacementDeterminant, frameDeterminant]

/-- Reassociation used after row Cramer.  Kept private because it is a technical
matrix/coordinate bridge rather than a separate mathematical API. -/
private theorem sum_mul_vecMul_eq_functional_inv_mulVec
    (b : Basis (Fin n) ℝ E) (A : Matrix (Fin n) (Fin n) ℝ)
    (r : E →L[ℝ] ℝ) (c : Fin n → ℝ) :
    (∑ i : Fin n, c i * Matrix.vecMul (functionalCoordinates b r) A i) =
      r ((coordinateEquiv b).symm (Matrix.mulVec A c)) := by
  calc
    (∑ i : Fin n, c i * Matrix.vecMul (functionalCoordinates b r) A i) =
        dotProduct c (Matrix.vecMul (functionalCoordinates b r) A) := rfl
    _ = dotProduct (Matrix.vecMul (functionalCoordinates b r) A) c :=
      dotProduct_comm _ _
    _ = dotProduct (functionalCoordinates b r) (Matrix.mulVec A c) :=
      (Matrix.dotProduct_mulVec (functionalCoordinates b r) A c).symm
    _ = r ((coordinateEquiv b).symm (Matrix.mulVec A c)) := by
      simpa only [dotProduct, (coordinateEquiv b).apply_symm_apply] using
        (functional_apply_eq_sum b r
          ((coordinateEquiv b).symm (Matrix.mulVec A c))).symm

/-- Exact row-replacement Cramer identity in an arbitrary displayed basis. -/
theorem cramerReplacement (b : Basis (Fin n) ℝ E) (B : Frame n E)
    (hB : frameDeterminant b B ≠ 0) (r : E →L[ℝ] ℝ) (c : Fin n → ℝ) :
    (∑ i : Fin n, c i * replacementDeterminant b B i r) =
      frameDeterminant b B *
        r ((coordinateEquiv b).symm ((frameMatrix b B)⁻¹.mulVec c)) := by
  let A : Matrix (Fin n) (Fin n) ℝ := frameMatrix b B
  have hdet : A.det ≠ 0 := by simpa [A, frameDeterminant] using hB
  have hunit : IsUnit A.det := (isUnit_iff_ne_zero).2 hdet
  have hcramer :
      A.det • Matrix.vecMul (functionalCoordinates b r) (A⁻¹) =
        Matrix.cramer (Matrix.transpose A) (functionalCoordinates b r) := by
    exact Matrix.det_smul_inv_vecMul_eq_cramer_transpose
      A (functionalCoordinates b r) hunit
  calc
    (∑ i : Fin n, c i * replacementDeterminant b B i r) =
        ∑ i : Fin n,
          c i * Matrix.cramer (Matrix.transpose A) (functionalCoordinates b r) i := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z : ℝ => c i * z) (by
        simpa [A] using replacementDeterminant_eq_cramerTranspose b B i r)
    _ = ∑ i : Fin n,
        c i * (A.det • Matrix.vecMul (functionalCoordinates b r) (A⁻¹)) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hcramer]
    _ = A.det * ∑ i : Fin n,
        c i * Matrix.vecMul (functionalCoordinates b r) (A⁻¹) i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change c i * (A.det * Matrix.vecMul (functionalCoordinates b r) (A⁻¹) i) =
        A.det * (c i * Matrix.vecMul (functionalCoordinates b r) (A⁻¹) i)
      ring
    _ = A.det * r ((coordinateEquiv b).symm (Matrix.mulVec (A⁻¹) c)) := by
      rw [sum_mul_vecMul_eq_functional_inv_mulVec]
    _ = frameDeterminant b B *
        r ((coordinateEquiv b).symm ((frameMatrix b B)⁻¹.mulVec c)) := by
      rfl

/-- R03 bridge: nonzero determinant gives injective coordinate matrix action.
The full square matrix is viewed as its canonical maximal minor. -/
private theorem frameMatrix_mulVec_injective_of_det_ne_zero
    (b : Basis (Fin n) ℝ E) (B : Frame n E)
    (hB : frameDeterminant b B ≠ 0) :
    Function.Injective (frameMatrix b B).mulVec := by
  let s : MathlibAnnex.Matrix.MaximalMinorIndex n (Fin n) :=
    MathlibAnnex.Matrix.MaximalMinorIndex.ofOrderEmbedding (OrderEmbedding.id (Fin n))
  apply MathlibAnnex.Matrix.mulVec_injective_of_maximalMinor_ne_zero
    (frameMatrix b B) s
  simpa [s, frameDeterminant] using hB

/-- A nonzero frame determinant makes the frame evaluation map injective. -/
theorem frameMap_injective_of_det_ne_zero (b : Basis (Fin n) ℝ E)
    (B : Frame n E) (hB : frameDeterminant b B ≠ 0) :
    Function.Injective (frameMap B) := by
  intro x y hxy
  apply (coordinateEquiv b).injective
  apply frameMatrix_mulVec_injective_of_det_ne_zero b B hB
  change frameCoordinates B x = frameCoordinates B y at hxy
  rwa [frameCoordinates_eq_mulVec b B x, frameCoordinates_eq_mulVec b B y] at hxy

/-- Frames whose determinant is within `η` of the attained maximum. -/
def nearMaxFrames (b : Basis (Fin n) ℝ E) (η : ℝ) : Set (Frame n E) :=
  {B | B ∈ unitFrameSet n E ∧
    determinantMaximum b - η ≤ |frameDeterminant b B|}

/-- Near-maximal frames form a compact subset of the compact frame set. -/
theorem nearMaxFrames_isCompact (b : Basis (Fin n) ℝ E) (η : ℝ) :
    IsCompact (nearMaxFrames b η) := by
  have hclosed : IsClosed
      {B : Frame n E | determinantMaximum b - η ≤ |frameDeterminant b B|} :=
    isClosed_le continuous_const (frameDeterminant_continuous b).abs
  exact unitFrameSet_isCompact.inter_right hclosed

/-- The selected maximizing frame belongs to every near-maximal set with
nonnegative slack. -/
theorem nearMaxFrames_nonempty (b : Basis (Fin n) ℝ E) {η : ℝ}
    (hη : 0 ≤ η) : (nearMaxFrames b η).Nonempty := by
  refine ⟨maximizingFrame b, maximizingFrame_mem b, ?_⟩
  simp only [determinantMaximum]
  linarith

/-- Determinant lower bound carried by near-maximal membership. -/
theorem nearMaxFrame_abs_det_lower (b : Basis (Fin n) ℝ E) {η : ℝ}
    {B : Frame n E} (hB : B ∈ nearMaxFrames b η) :
    determinantMaximum b - η ≤ |frameDeterminant b B| :=
  hB.2

/-- Positive determinant gap implies a nonzero determinant. -/
theorem nearMaxFrame_det_ne_zero (b : Basis (Fin n) ℝ E) {η : ℝ}
    (hη : η < determinantMaximum b) {B : Frame n E}
    (hB : B ∈ nearMaxFrames b η) : frameDeterminant b B ≠ 0 := by
  have hgap : 0 < determinantMaximum b - η := sub_pos.mpr hη
  have habs : 0 < |frameDeterminant b B| :=
    hgap.trans_le (nearMaxFrame_abs_det_lower b hB)
  exact abs_pos.mp habs

/-- The determinant of a near-maximal coordinate matrix is a unit. -/
theorem nearMaxFrame_det_isUnit (b : Basis (Fin n) ℝ E) {η : ℝ}
    (hη : η < determinantMaximum b) {B : Frame n E}
    (hB : B ∈ nearMaxFrames b η) : IsUnit (frameMatrix b B).det := by
  exact isUnit_iff_ne_zero.mpr (by
    simpa [frameDeterminant] using nearMaxFrame_det_ne_zero b hη hB)

/-- The inverse matrix and inverse coordinate equivalence reconstruct a vector. -/
theorem inverse_mulVec_frameCoordinates (b : Basis (Fin n) ℝ E) {η : ℝ}
    (hη : η < determinantMaximum b) {B : Frame n E}
    (hB : B ∈ nearMaxFrames b η) (x : E) :
    (coordinateEquiv b).symm
        ((frameMatrix b B)⁻¹.mulVec (frameCoordinates B x)) = x := by
  rw [frameCoordinates_eq_mulVec, Matrix.mulVec_mulVec]
  rw [Matrix.nonsing_inv_mul _ (nearMaxFrame_det_isUnit b hη hB)]
  rw [Matrix.one_mulVec]
  exact (coordinateEquiv b).symm_apply_apply x

/-- Replacing one row of an admissible frame by another unit-dual row preserves
admissibility. -/
theorem replaceRow_mem_unitFrameSet {B : Frame n E}
    (hB : B ∈ unitFrameSet n E) (i : Fin n) {r : E →L[ℝ] ℝ}
    (hr : r ∈ unitRowSet E) : replaceRow B i r ∈ unitFrameSet n E := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [replaceRow] using hr
  · simpa [replaceRow, hji] using hB j

/-- Every admissible row replacement determinant is bounded by the global maximum. -/
theorem abs_replacementDeterminant_le_maximum
    (b : Basis (Fin n) ℝ E) {B : Frame n E}
    (hB : B ∈ unitFrameSet n E) (i : Fin n) {r : E →L[ℝ] ℝ}
    (hr : r ∈ unitRowSet E) :
    |replacementDeterminant b B i r| ≤ determinantMaximum b := by
  simpa [determinantMaximum, replacementDeterminant] using
    abs_frameDeterminant_le_maximizingFrame b
      (replaceRow_mem_unitFrameSet hB i hr)

/-- The Cramer numerator is controlled by row count, coefficient sup norm, and
maximum determinant. -/
theorem abs_cramerNumerator_le (b : Basis (Fin n) ℝ E)
    {B : Frame n E} (hB : B ∈ unitFrameSet n E)
    (c : Fin n → ℝ) {r : E →L[ℝ] ℝ} (hr : r ∈ unitRowSet E) :
    |∑ i : Fin n, c i * replacementDeterminant b B i r| ≤
      (n : ℝ) * ‖c‖ * determinantMaximum b := by
  calc
    |∑ i : Fin n, c i * replacementDeterminant b B i r| ≤
        ∑ i : Fin n, |c i * replacementDeterminant b B i r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖c‖ * determinantMaximum b := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm c i)
        (abs_replacementDeterminant_le_maximum b hB i hr)
        (abs_nonneg _) (norm_nonneg c)
    _ = (n : ℝ) * ‖c‖ * determinantMaximum b := by
      simp [mul_assoc]

/-- Coordinatewise inverse estimate. -/
theorem abs_inverse_mulVec_apply_le (b : Basis (Fin n) ℝ E)
    {η : ℝ} (hηD : η < determinantMaximum b) {B : Frame n E}
    (hB : B ∈ nearMaxFrames b η) (c : Fin n → ℝ) (j : Fin n) :
    |((frameMatrix b B)⁻¹.mulVec c) j| ≤
      ((n : ℝ) * determinantMaximum b /
        (coordinateScale b * (determinantMaximum b - η))) * ‖c‖ := by
  let x : Fin n → ℝ := (frameMatrix b B)⁻¹.mulVec c
  let r : E →L[ℝ] ℝ := coordinateRow b j
  have hgap : 0 < determinantMaximum b - η := sub_pos.mpr hηD
  have hden : 0 < coordinateScale b * (determinantMaximum b - η) :=
    mul_pos (coordinateScale_pos b) hgap
  have hr : r ∈ unitRowSet E := by
    simpa [r, coordinateFrame] using coordinateFrame_mem b j
  have hcramer := cramerReplacement b B
    (nearMaxFrame_det_ne_zero b hηD hB) r c
  have hnum := abs_cramerNumerator_le b hB.1 c hr
  have heq :
      |frameDeterminant b B| * (coordinateScale b * |x j|) =
        |∑ i : Fin n, c i * replacementDeterminant b B i r| := by
    rw [hcramer]
    simp [x, r, abs_mul, coordinateRow_apply,
      abs_of_pos (coordinateScale_pos b)]
  have hlower :
      (determinantMaximum b - η) * (coordinateScale b * |x j|) ≤
        |frameDeterminant b B| * (coordinateScale b * |x j|) := by
    exact mul_le_mul_of_nonneg_right (nearMaxFrame_abs_det_lower b hB)
      (mul_nonneg (coordinateScale_pos b).le (abs_nonneg _))
  have hmain :
      coordinateScale b * (determinantMaximum b - η) * |x j| ≤
        (n : ℝ) * determinantMaximum b * ‖c‖ := by
    calc
      coordinateScale b * (determinantMaximum b - η) * |x j| =
          (determinantMaximum b - η) * (coordinateScale b * |x j|) := by ring
      _ ≤ |frameDeterminant b B| * (coordinateScale b * |x j|) := hlower
      _ = |∑ i : Fin n, c i * replacementDeterminant b B i r| := heq
      _ ≤ (n : ℝ) * ‖c‖ * determinantMaximum b := hnum
      _ = (n : ℝ) * determinantMaximum b * ‖c‖ := by ring
  change |x j| ≤ _
  calc
    |x j| ≤ ((n : ℝ) * determinantMaximum b * ‖c‖) /
        (coordinateScale b * (determinantMaximum b - η)) := by
      apply (le_div_iff₀ hden).2
      calc
        |x j| * (coordinateScale b * (determinantMaximum b - η)) =
            coordinateScale b * (determinantMaximum b - η) * |x j| := by ring
        _ ≤ (n : ℝ) * determinantMaximum b * ‖c‖ := hmain
    _ = ((n : ℝ) * determinantMaximum b /
        (coordinateScale b * (determinantMaximum b - η))) * ‖c‖ := by
      ring

/-- Coordinate-space factor in the common inverse estimate. -/
noncomputable def coordinateInverseFactor (b : Basis (Fin n) ℝ E) (η : ℝ) : ℝ :=
  (n : ℝ) * determinantMaximum b /
    (coordinateScale b * (determinantMaximum b - η))

/-- Explicit common inverse constant.  The leading one preserves strict
positivity in dimension zero. -/
noncomputable def inverseBoundConstant (b : Basis (Fin n) ℝ E) (η : ℝ) : ℝ :=
  1 + ‖inverseCoordinateMap b‖ * coordinateInverseFactor b η

/-- The explicit inverse constant is positive whenever the determinant gap is positive. -/
theorem inverseBoundConstant_pos (b : Basis (Fin n) ℝ E)
    {η : ℝ} (hηD : η < determinantMaximum b) :
    0 < inverseBoundConstant b η := by
  have hgap : 0 < determinantMaximum b - η := sub_pos.mpr hηD
  have hdet : 0 ≤ determinantMaximum b := (determinantMaximum_pos b).le
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hfactor : 0 ≤ coordinateInverseFactor b η := by
    unfold coordinateInverseFactor
    exact div_nonneg (mul_nonneg hn hdet)
      (mul_nonneg (coordinateScale_pos b).le hgap.le)
  unfold inverseBoundConstant
  nlinarith [norm_nonneg (inverseCoordinateMap b)]

/-- The explicit Cramer estimate transported back through the inverse coordinate map. -/
theorem inverseBoundConstant_bound (b : Basis (Fin n) ℝ E)
    {η : ℝ} (hηD : η < determinantMaximum b) {B : Frame n E}
    (hB : B ∈ nearMaxFrames b η) (c : Fin n → ℝ) :
    ‖(coordinateEquiv b).symm ((frameMatrix b B)⁻¹.mulVec c)‖ ≤
      inverseBoundConstant b η * ‖c‖ := by
  let C : ℝ := coordinateInverseFactor b η
  have hC : 0 ≤ C := by
    dsimp [C, coordinateInverseFactor]
    have hgap : 0 < determinantMaximum b - η := sub_pos.mpr hηD
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (determinantMaximum_pos b).le)
      (mul_nonneg (coordinateScale_pos b).le hgap.le)
  have hcoord : ‖(frameMatrix b B)⁻¹.mulVec c‖ ≤ C * ‖c‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg c))).2
    intro j
    simpa [C, coordinateInverseFactor] using
      abs_inverse_mulVec_apply_le b hηD hB c j
  have hop :
      ‖(coordinateEquiv b).symm ((frameMatrix b B)⁻¹.mulVec c)‖ ≤
        ‖inverseCoordinateMap b‖ * ‖(frameMatrix b B)⁻¹.mulVec c‖ := by
    exact (inverseCoordinateMap b).le_opNorm _
  calc
    ‖(coordinateEquiv b).symm ((frameMatrix b B)⁻¹.mulVec c)‖ ≤
        ‖inverseCoordinateMap b‖ * ‖(frameMatrix b B)⁻¹.mulVec c‖ := hop
    _ ≤ ‖inverseCoordinateMap b‖ * (C * ‖c‖) :=
      mul_le_mul_of_nonneg_left hcoord (norm_nonneg _)
    _ ≤ (1 + ‖inverseCoordinateMap b‖ * C) * ‖c‖ := by
      nlinarith [norm_nonneg c]
    _ = inverseBoundConstant b η * ‖c‖ := by
      simp [inverseBoundConstant, C]

/-- Packaged common inverse estimate on the near-maximal frame set. -/
structure NearMaxInverseBound (b : Basis (Fin n) ℝ E) (η : ℝ) where
  /-- Common bound for every near-maximal inverse frame. -/
  K : ℝ
  /-- Strict positivity, including dimension zero. -/
  K_pos : 0 < K
  /-- Uniform estimate from the coordinate sup norm to the ambient norm. -/
  bound : ∀ {B : Frame n E}, B ∈ nearMaxFrames b η → ∀ c : Fin n → ℝ,
    ‖(coordinateEquiv b).symm ((frameMatrix b B)⁻¹.mulVec c)‖ ≤ K * ‖c‖

namespace NearMaxInverseBound

variable {b : Basis (Fin n) ℝ E} {η : ℝ}

/-- The stored common bound is nonnegative. -/
theorem K_nonneg (H : NearMaxInverseBound b η) : 0 ≤ H.K := H.K_pos.le

/-- Apply the stored estimate to a coefficient difference. -/
theorem bound_sub (H : NearMaxInverseBound b η) {B : Frame n E}
    (hB : B ∈ nearMaxFrames b η) (c d : Fin n → ℝ) :
    ‖(coordinateEquiv b).symm ((frameMatrix b B)⁻¹.mulVec (c - d))‖ ≤
      H.K * ‖c - d‖ :=
  H.bound hB (c - d)

end NearMaxInverseBound

/-- A common inverse bound exists for every nonnegative slack strictly below the
basis-dependent determinant maximum. -/
theorem exists_nearMaxInverseBound (b : Basis (Fin n) ℝ E) {η : ℝ}
    (_hη0 : 0 ≤ η) (hηD : η < determinantMaximum b) :
    Nonempty (NearMaxInverseBound b η) := by
  refine ⟨⟨inverseBoundConstant b η, inverseBoundConstant_pos b hηD, ?_⟩⟩
  intro B hB c
  exact inverseBoundConstant_bound b hηD hB c

end DeterminantFrame
end MathlibAnnex
