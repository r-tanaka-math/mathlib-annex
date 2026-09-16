import MathlibAnnex.Analysis.Normed.Operator.FiniteSup
import MathlibAnnex.LinearAlgebra.Matrix.VolumeScaledMaximalMinor
import MathlibAnnex.LinearAlgebra.Matrix.MaximalMinor
import MathlibAnnex.LinearAlgebra.Matrix.MaximalMinorFactorization

noncomputable section
set_option autoImplicit false
open Set Module
open scoped BigOperators NNReal
namespace MathlibAnnex.PluckerSupport
universe u
open Satellite
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

private theorem inverseBound {n : ℕ} (M : NormModel n) {η : ℝ} (H : NearMaxInverseBound M η) {B : DualFrame n}
    (h : B ∈ nearMaxFrames M η) (c : Coord n) : M.p (framePreimage B c) ≤ H.K * ‖c‖ := by
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
private theorem frameDet_continuous {n : ℕ} : Continuous (frameDet : DualFrame n → ℝ) :=
  DeterminantFrame.frameDeterminant_continuous (Pi.basisFun ℝ (Fin n))
private theorem dualFrameMatrix_replaceFrameRow {n : ℕ} (B : DualFrame n) (i : Fin n) (r : Coord n →L[ℝ] ℝ) :
    dualFrameMatrix (replaceFrameRow B i r) = (dualFrameMatrix B).updateRow i (functionalRow r) :=
  DeterminantFrame.frameMatrix_replaceRow (Pi.basisFun ℝ (Fin n)) B i r
private theorem cramerReplacement {n : ℕ} (B : DualFrame n) (hB : frameDet B ≠ 0) (r : Coord n →L[ℝ] ℝ) (c : Coord n) :
    (∑ i : Fin n, c i * replacementDet B i r) = frameDet B * r (framePreimage B c) :=
  DeterminantFrame.cramerReplacement (Pi.basisFun ℝ (Fin n)) B hB r c

private theorem dualRowSet_isCompact {n : ℕ} (M : NormModel n) : IsCompact (dualRowSet M) := by
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

private theorem dualFrameSet_isCompact {n : ℕ} (M : NormModel n) : IsCompact (dualFrameSet M) := by
  have heq : dualFrameSet M = Set.univ.pi (fun _ : Fin n => dualRowSet M) := by ext B; simp [dualFrameSet, dualRowSet]
  rw [heq]
  exact isCompact_univ_pi fun _ => dualRowSet_isCompact M


private abbrev SupCoord (n : ℕ) := Fin n → ℝ

open FiniteSup FiniteSup.Bridge
namespace Internal
end Internal
open Internal

private abbrev MinorIndex (n N : ℕ) := MathlibAnnex.Matrix.MaximalMinorIndex n (Fin N)
private abbrev PluckerCoord (n N : ℕ) := MinorIndex n N → ℝ
private abbrev clmMatrix {n N : ℕ} (A : Coord n →L[ℝ] SupCoord N) := LinearMap.toMatrix' A.toLinearMap
private abbrev maximalMinor := @MathlibAnnex.Matrix.maximalMinor
private abbrev maximalMinors := @MathlibAnnex.Matrix.maximalMinors
private abbrev selectedSubmatrix := @MathlibAnnex.Matrix.maximalSubmatrix
private abbrev minorIndexOfOrderEmbedding := @MathlibAnnex.Matrix.MaximalMinorIndex.ofOrderEmbedding
private abbrev selectedSubmatrix_minorIndexOfOrderEmbedding := @MathlibAnnex.Matrix.maximalSubmatrix_ofOrderEmbedding
private abbrev maximalMinor_minorIndexOfOrderEmbedding := @MathlibAnnex.Matrix.maximalMinor_ofOrderEmbedding
private abbrev normalizedPlucker := @MathlibAnnex.Matrix.ballVolumeScaledMaximalMinors
private def pluckerFunctional {n N : ℕ} (w : PluckerCoord n N) : PluckerCoord n N →L[ℝ] ℝ :=
  ∑ i, w i • ContinuousLinearMap.proj i
private theorem pluckerFunctional_apply {n N : ℕ} (w z : PluckerCoord n N) : pluckerFunctional w z = dotProduct w z := by
  simp [pluckerFunctional, dotProduct]
variable {m : ℕ} {J : Type u} [Fintype J]

private abbrev positiveSatelliteAmbientDim (m : ℕ) (J : Type u) [Fintype J] : ℕ :=
  (m + 1) + Fintype.card J

private def baseRowIndex (J : Type u) [Fintype J] (i : Fin (m + 1)) :
    Fin (positiveSatelliteAmbientDim m J) :=
  Fin.castAdd (Fintype.card J) i

private noncomputable def satelliteRowIndex (m : ℕ) (J : Type u) [Fintype J] (a : J) :
    Fin (positiveSatelliteAmbientDim m J) :=
  Fin.natAdd (m + 1) (Fintype.equivFin J a)

private noncomputable def baseRowOrderEmb (m : ℕ) (J : Type u) [Fintype J] :
    Fin (m + 1) ↪o Fin (positiveSatelliteAmbientDim m J) :=
  Fin.castAddOrderEmb (Fintype.card J)

@[simp] private theorem baseRowOrderEmb_apply (i : Fin (m + 1)) :
    baseRowOrderEmb m J i = baseRowIndex J i := by
  rfl

private def replacementSortedRow (i : Fin (m + 1)) (a : J) :
    Fin (m + 1) → Fin (positiveSatelliteAmbientDim m J) :=
  Fin.snoc
    (fun k : Fin m => baseRowIndex J (i.succAbove k))
    (satelliteRowIndex m J a)

private theorem replacementSortedRow_strictMono (i : Fin (m + 1)) (a : J) :
    StrictMono (replacementSortedRow i a) := by
  intro x y hxy
  cases y using Fin.lastCases with
  | last =>
      cases x using Fin.lastCases with
      | last => exact (lt_irrefl _ hxy).elim
      | cast x =>
          simp [replacementSortedRow, baseRowIndex, satelliteRowIndex,
            Fin.lt_def]
          omega
  | cast y =>
      have hxlast : x ≠ Fin.last m := ne_of_lt (hxy.trans_le (Fin.le_last _))
      obtain ⟨x', hx⟩ := Fin.eq_castSucc_of_ne_last hxlast
      subst x
      have hbase :
          (baseRowOrderEmb m J) (i.succAbove x') <
            (baseRowOrderEmb m J) (i.succAbove y) :=
        (baseRowOrderEmb m J).lt_iff_lt.mpr
          ((i.succAboveOrderEmb).lt_iff_lt.mpr
            (Fin.castSucc_lt_castSucc_iff.mp hxy))
      simpa only [replacementSortedRow, Fin.snoc_castSucc,
        baseRowOrderEmb_apply] using hbase

private noncomputable def replacementSortedOrderEmb (i : Fin (m + 1)) (a : J) :
    Fin (m + 1) ↪o Fin (positiveSatelliteAmbientDim m J) :=
  OrderEmbedding.ofStrictMono (replacementSortedRow i a)
    (replacementSortedRow_strictMono i a)

private noncomputable def baseMinorIndex :
    MinorIndex (m + 1) (positiveSatelliteAmbientDim m J) :=
  minorIndexOfOrderEmbedding (baseRowOrderEmb m J)

private noncomputable def replacementMinorIndex (i : Fin (m + 1)) (a : J) :
    MinorIndex (m + 1) (positiveSatelliteAmbientDim m J) :=
  minorIndexOfOrderEmbedding (replacementSortedOrderEmb i a)

private noncomputable def replacementMovePerm (i : Fin (m + 1)) :
    Equiv.Perm (Fin (m + 1)) :=
  (Fin.cycleIcc i (Fin.last m)).symm

private noncomputable def replacementParity (i : Fin (m + 1)) : ℝ :=
  (((Equiv.Perm.sign (replacementMovePerm i) : Units ℤ) : ℤ) : ℝ)

@[simp] private theorem replacementParity_abs (i : Fin (m + 1)) :
    |replacementParity i| = 1 := by
  unfold replacementParity
  have hsign :
      |(((Equiv.Perm.sign (replacementMovePerm i) : Units ℤ) : ℤ))| = 1 :=
    Equiv.Perm.sign_abs (replacementMovePerm i)
  exact_mod_cast hsign

private theorem maximalMinor_configurationFinMap_base
    (C : SatelliteConfiguration (m + 1) J) :
    maximalMinor (clmMatrix (configurationFinMap C))
      (baseMinorIndex (m := m) (J := J)) = frameDet C.1 := by
  unfold baseMinorIndex
  unfold maximalMinor minorIndexOfOrderEmbedding
  rw [MathlibAnnex.Matrix.maximalMinor_ofOrderEmbedding]
  congr 1
  ext i j
  simp [baseRowOrderEmb, clmMatrix, dualFrameMatrix, DeterminantFrame.frameMatrix, Pi.basisFun_apply, frameDet, DeterminantFrame.frameDeterminant]

@[simp] private theorem replacementMovePerm_apply_self (i : Fin (m + 1)) :
    replacementMovePerm i i = Fin.last m := by
  unfold replacementMovePerm
  apply (Fin.cycleIcc i (Fin.last m)).injective
  simp only [Equiv.apply_symm_apply]
  exact (Fin.cycleIcc_of_last (Fin.le_last i)).symm

@[simp] private theorem replacementMovePerm_apply_succAbove
    (i : Fin (m + 1)) (k : Fin m) :
    replacementMovePerm i (i.succAbove k) = Fin.castSucc k := by
  unfold replacementMovePerm
  apply (Fin.cycleIcc i (Fin.last m)).injective
  simp only [Equiv.apply_symm_apply]
  have hcycle := congrFun
    (Fin.cycleIcc_comp_succAbove i (Fin.last m) (Fin.le_last i)) k
  simpa [Function.comp_apply] using hcycle.symm

private theorem replaceFrame_matrix_eq_permuted_selected
    (C : SatelliteConfiguration (m + 1) J)
    (i : Fin (m + 1)) (a : J) :
    dualFrameMatrix (replaceFrameRow C.1 i (C.2 a)) =
      (selectedSubmatrix (clmMatrix (configurationFinMap C))
        (replacementMinorIndex i a)).submatrix
          (replacementMovePerm i) id := by
  unfold replacementMinorIndex
  unfold selectedSubmatrix minorIndexOfOrderEmbedding
  rw [MathlibAnnex.Matrix.maximalSubmatrix_ofOrderEmbedding]
  ext k j
  simp only [replacementSortedOrderEmb, OrderEmbedding.coe_ofStrictMono,
    Matrix.submatrix_apply, id_eq]
  simp only [dualFrameMatrix, DeterminantFrame.frameMatrix, Pi.basisFun_apply]
  change
    (replaceFrameRow C.1 i (C.2 a) k) (Pi.single j 1) =
      configurationFinMap C (Pi.single j 1)
        (replacementSortedRow i a (replacementMovePerm i k))
  by_cases hki : k = i
  · subst k
    simp [replaceFrameRow, DeterminantFrame.replaceRow, replacementSortedRow, satelliteRowIndex]
  · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hki
    simp [replaceFrameRow, DeterminantFrame.replaceRow, replacementSortedRow, baseRowIndex]

private theorem replacementParity_mul_maximalMinor
    (C : SatelliteConfiguration (m + 1) J)
    (i : Fin (m + 1)) (a : J) :
    replacementParity i *
      maximalMinor (clmMatrix (configurationFinMap C))
        (replacementMinorIndex i a) =
      replacementDet C.1 i (C.2 a) := by
  have hperm := Matrix.det_permute (replacementMovePerm i)
    (selectedSubmatrix (clmMatrix (configurationFinMap C))
      (replacementMinorIndex i a))
  rw [← replaceFrame_matrix_eq_permuted_selected C i a] at hperm
  simpa [replacementParity, replacementDet, frameDet, maximalMinor, MathlibAnnex.Matrix.maximalMinor, selectedSubmatrix, DeterminantFrame.replacementDeterminant, DeterminantFrame.frameDeterminant] using hperm.symm

noncomputable def satellitePluckerCoefficients
    (weight : ℝ) (coeff : J → Coord (m + 1)) :
    PluckerCoord (m + 1) (positiveSatelliteAmbientDim m J) :=
  weight • Pi.single (baseMinorIndex (m := m) (J := J)) 1 +
    ∑ a : J, ∑ i : Fin (m + 1),
      (coeff a i * replacementParity i) •
        Pi.single (replacementMinorIndex i a) 1

theorem pluckerPairing_satelliteCoefficients_maximalMinors
    (weight : ℝ) (coeff : J → Coord (m + 1))
    (C : SatelliteConfiguration (m + 1) J) :
    dotProduct (satellitePluckerCoefficients weight coeff)
      (maximalMinors (clmMatrix (configurationFinMap C))) =
      configurationPolynomial weight coeff C := by
  classical
  simp only [satellitePluckerCoefficients, add_dotProduct,
    smul_dotProduct, single_dotProduct, one_mul]
  change weight * maximalMinor (clmMatrix (configurationFinMap C))
      (baseMinorIndex (m := m) (J := J)) +
      dotProduct
        (∑ a : J, ∑ i : Fin (m + 1),
          (coeff a i * replacementParity i) •
            Pi.single (replacementMinorIndex i a) 1)
        (maximalMinors (clmMatrix (configurationFinMap C))) =
      configurationPolynomial weight coeff C
  rw [maximalMinor_configurationFinMap_base C]
  simp only [configurationPolynomial, satellitePolynomial]
  congr 1
  have pair_sum_left_J
      (ω : J → PluckerCoord (m + 1) (positiveSatelliteAmbientDim m J))
      (z : PluckerCoord (m + 1) (positiveSatelliteAmbientDim m J)) :
      dotProduct (∑ a : J, ω a) z =
        ∑ a : J, dotProduct (ω a) z := by
    unfold dotProduct
    simp only [Finset.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have pair_sum_left_Fin
      (ω : Fin (m + 1) →
        PluckerCoord (m + 1) (positiveSatelliteAmbientDim m J))
      (z : PluckerCoord (m + 1) (positiveSatelliteAmbientDim m J)) :
      dotProduct (∑ i : Fin (m + 1), ω i) z =
        ∑ i : Fin (m + 1), dotProduct (ω i) z := by
    unfold dotProduct
    simp only [Finset.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  calc
    dotProduct
        (∑ a : J, ∑ i : Fin (m + 1),
          (coeff a i * replacementParity i) •
            Pi.single (replacementMinorIndex i a) 1)
        (maximalMinors (clmMatrix (configurationFinMap C))) =
      ∑ a : J, dotProduct
        (∑ i : Fin (m + 1),
          (coeff a i * replacementParity i) •
            Pi.single (replacementMinorIndex i a) 1)
        (maximalMinors (clmMatrix (configurationFinMap C))) := by
          exact pair_sum_left_J
            (fun a : J => ∑ i : Fin (m + 1),
              (coeff a i * replacementParity i) •
                Pi.single (replacementMinorIndex i a) 1)
            (maximalMinors (clmMatrix (configurationFinMap C)))
    _ = ∑ a : J, ∑ i : Fin (m + 1), dotProduct
        ((coeff a i * replacementParity i) •
          Pi.single (replacementMinorIndex i a) 1)
        (maximalMinors (clmMatrix (configurationFinMap C))) := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact pair_sum_left_Fin
            (fun i : Fin (m + 1) =>
              (coeff a i * replacementParity i) •
                Pi.single (replacementMinorIndex i a) 1)
            (maximalMinors (clmMatrix (configurationFinMap C)))
    _ = ∑ a : J, ∑ i : Fin (m + 1),
        coeff a i * replacementDet C.1 i (C.2 a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          apply Finset.sum_congr rfl
          intro i _hi
          rw [smul_dotProduct, single_dotProduct, one_mul]
          change coeff a i * replacementParity i *
              maximalMinor (clmMatrix (configurationFinMap C))
                (replacementMinorIndex i a) =
            coeff a i * replacementDet C.1 i (C.2 a)
          rw [mul_assoc, replacementParity_mul_maximalMinor C i a]

theorem pluckerFunctional_normalized_configurationFinMap
    (M : NormModel (m + 1)) (weight : ℝ)
    (coeff : J → Coord (m + 1))
    (C : SatelliteConfiguration (m + 1) J) :
    pluckerFunctional (satellitePluckerCoefficients weight coeff)
        (normalizedPlucker M (configurationFinMap C)) =
      M.closedUnitBallVolume * configurationPolynomial weight coeff C := by
  rw [pluckerFunctional_apply, MathlibAnnex.Matrix.pairing_ballVolumeScaledMaximalMinors,
    pluckerPairing_satelliteCoefficients_maximalMinors]

private def Internal.supportOrientation (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

@[simp] private theorem Internal.supportOrientation_mem (t : ℝ) :
    supportOrientation t = 1 ∨ supportOrientation t = -1 := by
  by_cases ht : 0 ≤ t
  · exact Or.inl (by simp [supportOrientation, ht])
  · exact Or.inr (by simp [supportOrientation, ht])

private theorem Internal.supportOrientation_mul (t : ℝ) :
    supportOrientation t * t = |t| := by
  by_cases ht : 0 ≤ t
  · simp [supportOrientation, ht, abs_of_nonneg ht]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    simp [supportOrientation, ht, abs_of_nonpos ht']

noncomputable def orientedSatelliteSupport
    (weight : ℝ) (coeff : J → Coord (m + 1))
    (Cstar : SatelliteConfiguration (m + 1) J) :
    PluckerCoord (m + 1) (positiveSatelliteAmbientDim m J) →L[ℝ] ℝ :=
  supportOrientation (configurationPolynomial weight coeff Cstar) •
    pluckerFunctional (satellitePluckerCoefficients weight coeff)

theorem orientedSatelliteSupport_configuration
    (M : NormModel (m + 1)) (weight : ℝ)
    (coeff : J → Coord (m + 1))
    (Cstar C : SatelliteConfiguration (m + 1) J) :
    orientedSatelliteSupport weight coeff Cstar
        (normalizedPlucker M (configurationFinMap C)) =
      M.closedUnitBallVolume *
        (supportOrientation (configurationPolynomial weight coeff Cstar) *
          configurationPolynomial weight coeff C) := by
  change supportOrientation (configurationPolynomial weight coeff Cstar) *
      pluckerFunctional (satellitePluckerCoefficients weight coeff)
        (normalizedPlucker M (configurationFinMap C)) =
    M.closedUnitBallVolume *
      (supportOrientation (configurationPolynomial weight coeff Cstar) *
        configurationPolynomial weight coeff C)
  rw [pluckerFunctional_normalized_configurationFinMap]
  ring

theorem orientedSatelliteSupport_self
    (M : NormModel (m + 1)) (weight : ℝ)
    (coeff : J → Coord (m + 1))
    (Cstar : SatelliteConfiguration (m + 1) J) :
    orientedSatelliteSupport weight coeff Cstar
        (normalizedPlucker M (configurationFinMap Cstar)) =
      M.closedUnitBallVolume * |configurationPolynomial weight coeff Cstar| := by
  rw [orientedSatelliteSupport_configuration, supportOrientation_mul]

end MathlibAnnex.PluckerSupport
