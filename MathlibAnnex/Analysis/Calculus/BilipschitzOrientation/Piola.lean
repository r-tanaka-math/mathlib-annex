import MathlibAnnex.Analysis.Calculus.BilipschitzOrientation.Basic
import MathlibAnnex.MeasureTheory.Integral.MaximalMinor
import MathlibAnnex.Analysis.Distribution.WeakGradient.Basic
import Mathlib.Tactic

/-!
# Degree-free orientation for global bi-Lipschitz data: weak Piola layer

The public output of this file is the weak Piola identity and the resulting
`WeakDivergenceZero` statement for the target Jacobian sign.  Coordinate
rank-one perturbations are implementation details and stay private.  The
whole-space determinant-difference identity is supplied by the exact R04
maximal-minor null-Lagrangian theorem; compact C¹ test fields and divergence
come from the exact repaired R05 API.

This browser-produced source is `HANDWRITTEN_UNBUILT` until local elaboration.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace MathlibAnnex
namespace BilipschitzOrientation

private def basisVector {n : ℕ} (i : Fin n) : Fin n → ℝ := Pi.single i 1

private noncomputable def coordinateProjector {n : ℕ} (i : Fin n) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (ContinuousLinearMap.proj i).smulRight (basisVector i)

@[simp] private theorem coordinateProjector_apply {n : ℕ} (i : Fin n)
    (x : Fin n → ℝ) :
    coordinateProjector i x = x i • basisVector i := by
  rfl

private def clmMatrix {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A (Pi.single j 1) i

private theorem clmMatrix_eq_toMatrix' {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    clmMatrix A = LinearMap.toMatrix' A.toLinearMap := by
  ext i j
  rfl

private noncomputable def coordDet {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : ℝ :=
  Matrix.det (clmMatrix A)

@[simp] private theorem coordDet_eq_det {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    coordDet A = A.det := by
  rw [coordDet, clmMatrix_eq_toMatrix']
  exact LinearMap.det_toMatrix' A.toLinearMap

private theorem coordDet_comp {n : ℕ}
    (A B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    coordDet (A.comp B) = coordDet A * coordDet B := by
  simp only [coordDet_eq_det]
  change LinearMap.det (A.toLinearMap.comp B.toLinearMap) =
    LinearMap.det A.toLinearMap * LinearMap.det B.toLinearMap
  exact LinearMap.det_comp A.toLinearMap B.toLinearMap

private def coordinatePerturbation {n : ℕ} (D : BiLipschitzOpenData n)
    (W : CompactC1VectorField (Fin n → ℝ)) (i : Fin n)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  coordinateProjector i (W (D.f x))

private def coordinatePiolaTerm {n : ℕ} (D : BiLipschitzOpenData n)
    (W : CompactC1VectorField (Fin n → ℝ)) (i : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  (fderiv ℝ W (D.f x) (basisVector i)) i * coordDet (fderiv ℝ D.f x)

private theorem divergence_mul_coordDet {n : ℕ}
    (D : BiLipschitzOpenData n)
    (W : CompactC1VectorField (Fin n → ℝ)) (x : Fin n → ℝ) :
    divergence W (D.f x) * coordDet (fderiv ℝ D.f x) =
      ∑ i : Fin n, coordinatePiolaTerm D W i x := by
  rw [divergence_pi]
  simp [coordinatePiolaTerm, basisVector, Finset.sum_mul]

private def oneRowPerturbationMatrix {n : ℕ} (i : Fin n)
    (B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i
    ((1 : Matrix (Fin n) (Fin n) ℝ) i + B i)

private theorem row_eq_sum_stdBasis {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    B i = ∑ j : Fin n, B i j • (1 : Matrix (Fin n) (Fin n) ℝ) j := by
  funext j
  simp [Matrix.one_apply]

private theorem det_oneRowPerturbationMatrix {n : ℕ} (i : Fin n)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.det (oneRowPerturbationMatrix i B) = 1 + B i i := by
  rw [oneRowPerturbationMatrix, Matrix.det_updateRow_add]
  rw [Matrix.updateRow_eq_self, Matrix.det_one]
  rw [row_eq_sum_stdBasis B i, Matrix.det_updateRow_sum]
  simp [Matrix.det_one, Matrix.one_apply]

private theorem clmMatrix_one_add_coordinateProjector_comp {n : ℕ}
    (i : Fin n) (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    clmMatrix ((ContinuousLinearMap.id ℝ (Fin n → ℝ)) +
      (coordinateProjector i).comp B) =
      oneRowPerturbationMatrix i (clmMatrix B) := by
  classical
  ext r c
  by_cases hri : r = i
  · subst r
    simp [oneRowPerturbationMatrix, coordinateProjector, basisVector,
      clmMatrix, Matrix.updateRow, Matrix.one_apply, Pi.single_apply]
  · simp [oneRowPerturbationMatrix, coordinateProjector, basisVector,
      clmMatrix, Matrix.updateRow, Matrix.one_apply, Pi.single_apply, hri]

private theorem coordDet_one_add_coordinateProjector_comp {n : ℕ}
    (i : Fin n) (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    coordDet ((ContinuousLinearMap.id ℝ (Fin n → ℝ)) +
      (coordinateProjector i).comp B) =
      1 + (B (basisVector i)) i := by
  rw [coordDet, clmMatrix_one_add_coordinateProjector_comp,
    det_oneRowPerturbationMatrix]
  simp [clmMatrix, basisVector]

private theorem compactField_exists_fderiv_bound {n : ℕ}
    (W : CompactC1VectorField (Fin n → ℝ)) :
    ∃ C : ℝ≥0, ∀ y, ‖fderiv ℝ W y‖₊ ≤ C := by
  have hcont : Continuous (fun y => ‖fderiv ℝ W y‖₊) :=
    (W.contDiff.continuous_fderiv (by norm_num)).nnnorm
  obtain ⟨C, hC⟩ := W.isCompact_carrier.bddAbove_image hcont.continuousOn
  refine ⟨C, fun y => ?_⟩
  by_cases hy : y ∈ W.carrier
  · exact hC ⟨y, hy, rfl⟩
  · rw [W.fderiv_eq_zero_of_not_mem_carrier hy]
    simp

private theorem exists_lipschitzWith_compactField {n : ℕ}
    (W : CompactC1VectorField (Fin n → ℝ)) : ∃ K : ℝ≥0, LipschitzWith K W := by
  obtain ⟨C, hC⟩ := compactField_exists_fderiv_bound W
  exact ⟨C, lipschitzWith_of_nnnorm_fderiv_le
    (W.contDiff.differentiable (by norm_num)) hC⟩

private theorem preimage_eq_g_image {n : ℕ} (D : BiLipschitzOpenData n)
    {K : Set (Fin n → ℝ)} (hK : K ⊆ D.target) :
    D.f ⁻¹' K = D.g '' K := by
  ext x
  constructor
  · intro hx
    let y := D.f x
    have hyT : y ∈ D.target := hK hx
    have hright : D.f (D.g y) = y := D.right_inv hyT
    have hxg : x = D.g y := D.f_injective (by simpa [y] using hright.symm)
    exact ⟨y, hx, hxg.symm⟩
  · rintro ⟨y, hyK, rfl⟩
    simpa [D.right_inv (hK hyK)] using hyK

private theorem isCompact_preimage_carrier {n : ℕ}
    (D : BiLipschitzOpenData n)
    (W : CompactC1VectorField (Fin n → ℝ))
    (hW : W.carrier ⊆ D.target) :
    IsCompact (D.f ⁻¹' W.carrier) := by
  rw [preimage_eq_g_image D hW]
  exact W.isCompact_carrier.image D.lipschitzWith_g.continuous

private theorem exists_lipschitzWith_coordinatePerturbation {n : ℕ}
    (D : BiLipschitzOpenData n)
    (W : CompactC1VectorField (Fin n → ℝ)) (i : Fin n) :
    ∃ K : ℝ≥0, LipschitzWith K (coordinatePerturbation D W i) := by
  obtain ⟨KW, hKW⟩ := exists_lipschitzWith_compactField W
  exact ⟨‖coordinateProjector i‖₊ * (KW * D.fConstant), by
    change LipschitzWith (‖coordinateProjector i‖₊ * (KW * D.fConstant))
      (fun x => coordinateProjector i (W (D.f x)))
    exact (coordinateProjector i).lipschitz.comp
      (hKW.comp D.lipschitzWith_f)⟩

private theorem coordinatePerturbation_support_subset_preimage {n : ℕ}
    (D : BiLipschitzOpenData n)
    (W : CompactC1VectorField (Fin n → ℝ)) (i : Fin n) :
    Function.support (coordinatePerturbation D W i) ⊆ D.f ⁻¹' W.carrier := by
  intro x hx
  by_contra hnot
  have hzero : W (D.f x) = 0 := by
    by_contra hnz
    exact hnot (W.support_subset hnz)
  exact hx (by simp [coordinatePerturbation, hzero])

private theorem hasCompactSupport_coordinatePerturbation {n : ℕ}
    (D : BiLipschitzOpenData n)
    (W : CompactC1VectorField (Fin n → ℝ))
    (hW : W.carrier ⊆ D.target) (i : Fin n) :
    HasCompactSupport (coordinatePerturbation D W i) := by
  exact (isCompact_preimage_carrier D W hW).of_isClosed_subset
    (isClosed_tsupport _)
    (closure_minimal (coordinatePerturbation_support_subset_preimage D W i)
      (isCompact_preimage_carrier D W hW).isClosed)

private theorem coordinatePiolaTerm_eq_zero_of_image_not_mem_carrier {n : ℕ}
    (D : BiLipschitzOpenData n)
    (W : CompactC1VectorField (Fin n → ℝ)) (i : Fin n)
    {x : Fin n → ℝ} (hx : D.f x ∉ W.carrier) :
    coordinatePiolaTerm D W i x = 0 := by
  rw [coordinatePiolaTerm, W.fderiv_eq_zero_of_not_mem_carrier hx]
  simp

private theorem coordinatePiolaTerm_eq_zero_of_not_mem_source {n : ℕ}
    (D : BiLipschitzOpenData n)
    (W : CompactC1VectorField (Fin n → ℝ))
    (hW : W.carrier ⊆ D.target) (i : Fin n)
    {x : Fin n → ℝ} (hx : x ∉ D.source) :
    coordinatePiolaTerm D W i x = 0 := by
  apply coordinatePiolaTerm_eq_zero_of_image_not_mem_carrier D W i
  intro hfx
  have hpre : x ∈ D.f ⁻¹' W.carrier := hfx
  rw [preimage_eq_g_image D hW] at hpre
  rcases hpre with ⟨y, hy, rfl⟩
  exact hx (D.mapsTo_g (hW hy))

private theorem fderiv_coordinatePerturbation {n : ℕ}
    (D : BiLipschitzOpenData n)
    (W : CompactC1VectorField (Fin n → ℝ)) (i : Fin n)
    {x : Fin n → ℝ} (hdf : DifferentiableAt ℝ D.f x) :
    fderiv ℝ (coordinatePerturbation D W i) x =
      ((coordinateProjector i).comp (fderiv ℝ W (D.f x))).comp
        (fderiv ℝ D.f x) := by
  have hWdiff : DifferentiableAt ℝ W (D.f x) :=
    (W.contDiff.differentiable (by norm_num)) (D.f x)
  have hcomp :=
    ((coordinateProjector i).hasFDerivAt.comp x
      (hWdiff.hasFDerivAt.comp x hdf.hasFDerivAt)).fderiv
  change fderiv ℝ (⇑(coordinateProjector i) ∘ W ∘ D.f) x = _
  rw [hcomp]
  ext v
  rfl

private theorem fderiv_add_coordinatePerturbation {n : ℕ}
    (D : BiLipschitzOpenData n)
    (W : CompactC1VectorField (Fin n → ℝ)) (i : Fin n)
    {x : Fin n → ℝ} (hdf : DifferentiableAt ℝ D.f x) :
    fderiv ℝ (fun y => D.f y + coordinatePerturbation D W i y) x =
      ((ContinuousLinearMap.id ℝ (Fin n → ℝ)) +
        (coordinateProjector i).comp (fderiv ℝ W (D.f x))).comp
          (fderiv ℝ D.f x) := by
  have hWdiff : DifferentiableAt ℝ W (D.f x) :=
    (W.contDiff.differentiable (by norm_num)) (D.f x)
  have hudiff : DifferentiableAt ℝ (coordinatePerturbation D W i) x :=
    (coordinateProjector i).differentiableAt.comp x (hWdiff.comp x hdf)
  calc
    fderiv ℝ (fun y => D.f y + coordinatePerturbation D W i y) x =
        fderiv ℝ D.f x + fderiv ℝ (coordinatePerturbation D W i) x := by
      change fderiv ℝ (D.f + coordinatePerturbation D W i) x = _
      exact (hdf.hasFDerivAt.add hudiff.hasFDerivAt).fderiv
    _ = ((ContinuousLinearMap.id ℝ (Fin n → ℝ)) +
          (coordinateProjector i).comp (fderiv ℝ W (D.f x))).comp
            (fderiv ℝ D.f x) := by
      rw [fderiv_coordinatePerturbation D W i hdf]
      ext v
      simp

private theorem coordDet_difference_eq_coordinatePiolaTerm {n : ℕ}
    (D : BiLipschitzOpenData n)
    (W : CompactC1VectorField (Fin n → ℝ)) (i : Fin n)
    {x : Fin n → ℝ} (hdf : DifferentiableAt ℝ D.f x) :
    coordDet (fderiv ℝ (fun y => D.f y + coordinatePerturbation D W i y) x) -
      coordDet (fderiv ℝ D.f x) = coordinatePiolaTerm D W i x := by
  rw [fderiv_add_coordinatePerturbation D W i hdf]
  rw [coordDet_comp, coordDet_one_add_coordinateProjector_comp]
  simp [coordinatePiolaTerm, basisVector]
  ring

private theorem coordDet_difference_eq_coordinatePiolaTerm_ae {n : ℕ}
    (D : BiLipschitzOpenData n)
    (W : CompactC1VectorField (Fin n → ℝ)) (i : Fin n) :
    ∀ᵐ x ∂volume,
      coordDet (fderiv ℝ (fun y => D.f y + coordinatePerturbation D W i y) x) -
        coordDet (fderiv ℝ D.f x) = coordinatePiolaTerm D W i x := by
  filter_upwards [D.lipschitzWith_f.ae_differentiableAt] with x hx
  exact coordDet_difference_eq_coordinatePiolaTerm D W i hx

private noncomputable def identityMinorIndex (n : ℕ) :
    Matrix.MaximalMinorIndex n (Fin n) :=
  Matrix.MaximalMinorIndex.ofOrderEmbedding (OrderIso.refl (Fin n)).toOrderEmbedding

private theorem selectedSquare_identity {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    ContinuousLinearMap.selectedSquare (identityMinorIndex n) A = A := by
  ext x i
  simp [ContinuousLinearMap.selectedSquare, identityMinorIndex]

@[simp] private theorem maximalMinorIntegrand_identity {n : ℕ}
    (f : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) :
    NullLagrangian.maximalMinorIntegrand (identityMinorIndex n) f x =
      coordDet (fderiv ℝ f x) := by
  unfold NullLagrangian.maximalMinorIntegrand
  rw [selectedSquare_identity]
  exact (coordDet_eq_det (fderiv ℝ f x)).symm

private theorem integral_coordDet_add_sub_eq_zero_of_lipschitzWith
    {m : ℕ} {g u : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)}
    {Cg Cu : ℝ≥0} (hg : LipschitzWith Cg g) (hu : LipschitzWith Cu u)
    (huc : HasCompactSupport u) :
    ∫ x, (coordDet (fderiv ℝ (fun y => g y + u y) x) -
      coordDet (fderiv ℝ g x)) = 0 := by
  simpa only [maximalMinorIntegrand_identity] using
    (NullLagrangian.integral_maximalMinor_fderiv_add_sub_eq_zero_of_lipschitzWith
      (identityMinorIndex (m + 1)) hg hu huc)

private theorem integrable_coordDet_difference_of_lipschitzWith
    {m : ℕ} {g u : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)}
    {Cg Cu : ℝ≥0} (hg : LipschitzWith Cg g) (hu : LipschitzWith Cu u)
    (huc : HasCompactSupport u) :
    Integrable (fun x =>
      coordDet (fderiv ℝ (fun y => g y + u y) x) -
        coordDet (fderiv ℝ g x)) := by
  let s := identityMinorIndex (m + 1)
  let K : Set (Fin (m + 1) → ℝ) := tsupport u
  let q := fun x =>
    NullLagrangian.maximalMinorIntegrand s (fun y => g y + u y) x -
      NullLagrangian.maximalMinorIntegrand s g x
  have hK : IsCompact K := huc
  have hplus : LipschitzWith (Cg + Cu) (fun x => g x + u x) := hg.add hu
  have hplusInt :=
    NullLagrangian.integrableOn_maximalMinor_fderiv_of_lipschitzWith s hplus hK
  have hgInt :=
    NullLagrangian.integrableOn_maximalMinor_fderiv_of_lipschitzWith s hg hK
  have hqOn : IntegrableOn q K := hplusInt.sub hgInt
  have hind : Integrable (K.indicator q) :=
    hqOn.integrable_indicator hK.measurableSet
  have heq : K.indicator q = q := by
    funext x
    by_cases hx : x ∈ K
    · simp [hx]
    · have hz :=
        NullLagrangian.topMinor_difference_eq_zero_of_not_mem_tsupport s (g := g) hx
      simp [hx, q, hz]
  rw [heq] at hind
  simpa only [q, s, maximalMinorIntegrand_identity] using hind

private theorem integrable_coordinatePiolaTerm {m : ℕ}
    (D : BiLipschitzOpenData (m + 1))
    (W : CompactC1VectorField (Fin (m + 1) → ℝ))
    (hW : W.carrier ⊆ D.target) (i : Fin (m + 1)) :
    Integrable (coordinatePiolaTerm D W i) := by
  let u := coordinatePerturbation D W i
  obtain ⟨Cu, hu⟩ := exists_lipschitzWith_coordinatePerturbation D W i
  have huc : HasCompactSupport u := hasCompactSupport_coordinatePerturbation D W hW i
  have hdiff := integrable_coordDet_difference_of_lipschitzWith
    D.lipschitzWith_f hu huc
  exact hdiff.congr (coordDet_difference_eq_coordinatePiolaTerm_ae D W i)

private theorem coordinate_weak_piola {m : ℕ}
    (D : BiLipschitzOpenData (m + 1))
    (W : CompactC1VectorField (Fin (m + 1) → ℝ))
    (hW : W.carrier ⊆ D.target) (i : Fin (m + 1)) :
    ∫ x in D.source, coordinatePiolaTerm D W i x ∂volume = 0 := by
  let u := coordinatePerturbation D W i
  obtain ⟨Cu, hu⟩ := exists_lipschitzWith_coordinatePerturbation D W i
  have huc : HasCompactSupport u := hasCompactSupport_coordinatePerturbation D W hW i
  have hNL := integral_coordDet_add_sub_eq_zero_of_lipschitzWith
    D.lipschitzWith_f hu huc
  have hglobal : ∫ x, coordinatePiolaTerm D W i x = 0 := by
    rw [← integral_congr_ae
      (coordDet_difference_eq_coordinatePiolaTerm_ae D W i)]
    exact hNL
  have houtside : ∀ᵐ x ∂volume.restrict D.sourceᶜ,
      coordinatePiolaTerm D W i x = 0 := by
    filter_upwards [ae_restrict_mem D.isOpen_source.measurableSet.compl] with x hx
    exact coordinatePiolaTerm_eq_zero_of_not_mem_source D W hW i hx
  have hint := integrable_coordinatePiolaTerm D W hW i
  have hsplit := integral_add_compl D.isOpen_source.measurableSet hint
  have hcompl : ∫ x in D.sourceᶜ, coordinatePiolaTerm D W i x = 0 :=
    MeasureTheory.integral_eq_zero_of_ae houtside
  linarith [hglobal, hsplit, hcompl]

/-- Weak Piola identity for the forward map.  Dimension zero is the empty-sum
case; positive dimension uses R04's exact maximal-minor null-Lagrangian API. -/
theorem weak_piola {n : ℕ} (D : BiLipschitzOpenData n)
    (W : CompactC1VectorField (Fin n → ℝ)) (hW : W.carrier ⊆ D.target) :
    ∫ x in D.source,
      divergence W (D.f x) * (fderiv ℝ D.f x).det ∂volume = 0 := by
  cases n with
  | zero =>
      simp [divergence_pi]
  | succ m =>
      have hint : ∀ i : Fin (m + 1),
          IntegrableOn (coordinatePiolaTerm D W i) D.source := by
        intro i
        exact (integrable_coordinatePiolaTerm D W hW i).integrableOn
      rw [show (fun x => divergence W (D.f x) * (fderiv ℝ D.f x).det) =
        (fun x => ∑ i : Fin (m + 1), coordinatePiolaTerm D W i x) by
          funext x
          rw [← coordDet_eq_det]
          exact divergence_mul_coordDet D W x]
      rw [MeasureTheory.integral_finsetSum _ (fun i _ => hint i)]
      exact Finset.sum_eq_zero fun i _ => coordinate_weak_piola D W hW i

private theorem integrable_divergence {n : ℕ}
    (W : CompactC1VectorField (Fin n → ℝ)) : Integrable (divergence W) := by
  have hdiv_cont : Continuous (divergence W) := by
    have hfd_cont : Continuous (fun y => fderiv ℝ W y) :=
      W.contDiff.continuous_fderiv (by norm_num)
    have hrepr : (fun y => divergence W y) =
        (fun y => ∑ i : Fin n, (fderiv ℝ W y (Pi.single i 1)) i) := by
      funext y
      exact divergence_pi W y
    change Continuous (fun y => divergence W y)
    rw [hrepr]
    apply continuous_finsetSum
    intro i hi
    have heval : Continuous (fun A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) =>
        (A (Pi.single i 1)) i) := by fun_prop
    exact heval.comp hfd_cont
  have hcarrier : IntegrableOn (divergence W) W.carrier :=
    ContinuousOn.integrableOn_compact W.isCompact_carrier hdiv_cont.continuousOn
  have hind : Integrable (W.carrier.indicator (divergence W)) :=
    hcarrier.integrable_indicator W.isCompact_carrier.measurableSet
  have heq : W.carrier.indicator (divergence W) = divergence W := by
    funext y
    by_cases hy : y ∈ W.carrier
    · simp [hy]
    · have hfd := W.fderiv_eq_zero_of_not_mem_carrier hy
      have hdivzero : divergence W y = 0 := by
        rw [divergence_pi, hfd]
        simp
      simp [hy, hdivzero]
  rw [heq] at hind
  exact hind

/-- Weak Piola plus signed transfer gives zero weak divergence for the target
Jacobian sign. -/
theorem weakDivergenceZero_targetJacobianSign {n : ℕ}
    (D : BiLipschitzOpenData n) :
    WeakDivergenceZero volume D.target (targetJacobianSign D) := by
  intro W hW
  have hp := weak_piola D W hW
  have ht := signed_area_transfer D
    (φ := divergence W) (integrable_divergence W).integrableOn
  calc
    (∫ y in D.target, targetJacobianSign D y * divergence W y ∂volume) =
        ∫ y in D.target, divergence W y * targetJacobianSign D y ∂volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        simpa only using (mul_comm (targetJacobianSign D y) (divergence W y))
    _ = ∫ x in D.source,
          divergence W (D.f x) * (fderiv ℝ D.f x).det ∂volume := ht.symm
    _ = 0 := hp

end BilipschitzOrientation
end MathlibAnnex
