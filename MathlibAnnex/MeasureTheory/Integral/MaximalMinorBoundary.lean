import MathlibAnnex.MeasureTheory.Integral.MaximalMinor
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Measure

/-!
# Pointwise boundary agreement and maximal-minor integrals

The public theorem applies to any continuous seminorm whose closed unit ball
is compact. Boundary equality is pointwise on the seminorm unit sphere.
-/
noncomputable section
open Set Function MeasureTheory Filter
open scoped BigOperators Topology NNReal
namespace MathlibAnnex
namespace NullLagrangian

private structure SeminormBall (n : ℕ) where
  p : Seminorm ℝ (Fin n → ℝ)
  continuous_p : Continuous p
  isCompact_closedBall : IsCompact (p.closedBall 0 1)

namespace SeminormBall
private def unitBall {n : ℕ} (M : SeminormBall n) : Set (Fin n → ℝ) := M.p.closedBall 0 1
@[simp] private theorem mem_unitBall {n : ℕ} (M : SeminormBall n) {x : Fin n → ℝ} :
    x ∈ M.unitBall ↔ M.p x ≤ 1 := by simp [unitBall]
private theorem isCompact_unitBall {n : ℕ} (M : SeminormBall n) : IsCompact M.unitBall := M.isCompact_closedBall
private theorem isClosed_unitBall {n : ℕ} (M : SeminormBall n) : IsClosed M.unitBall := M.unitBall_isCompact.isClosed
private theorem measurableSet_unitBall {n : ℕ} (M : SeminormBall n) : MeasurableSet M.unitBall := M.unitBall_isClosed.measurableSet
end SeminormBall
private abbrev Lipschitz {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) :=
  ∃ C : ℝ≥0, LipschitzWith C f
private abbrev ModelUnitSphere {n : ℕ} (M : SeminormBall n) := {x : (Fin n → ℝ) // M.p x = 1}

private def modelOpenBall {n : ℕ} (M : SeminormBall n) : Set ((Fin n → ℝ)) :=
  {x | M.p x < 1}

private def modelSphereSet {n : ℕ} (M : SeminormBall n) : Set ((Fin n → ℝ)) :=
  {x | M.p x = 1}

private def segmentPoint {n : ℕ} (x y : (Fin n → ℝ)) (t : ℝ) : (Fin n → ℝ) :=
  (1 - t) • x + t • y

private theorem exists_segmentPoint_mem_modelSphere {n : ℕ} (M : SeminormBall n)
    {x y : (Fin n → ℝ)} (hx : M.p x < 1) (hy : 1 < M.p y) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, M.p (segmentPoint x y t) = 1 := by

  let φ : ℝ → ℝ := fun t => M.p (segmentPoint x y t)
  have hsegment : Continuous (segmentPoint x y) := by
    unfold segmentPoint
    fun_prop
  have hφ : Continuous φ := M.continuous_p.comp hsegment
  have h0 : φ 0 < 1 := by simpa [φ, segmentPoint] using hx
  have h1 : 1 < φ 1 := by simpa [φ, segmentPoint] using hy
  have hone : (1 : ℝ) ∈ Set.Icc (φ 0) (φ 1) := ⟨h0.le, h1.le⟩
  have himage : (1 : ℝ) ∈ φ '' Set.Icc (0 : ℝ) 1 :=
    (intermediate_value_Icc (a := (0 : ℝ)) (b := 1) (f := φ)
      (by norm_num) hφ.continuousOn) hone
  rcases himage with ⟨t, ht, hteq⟩
  exact ⟨t, ht, hteq⟩

private theorem exists_boundary_point_between {n : ℕ} (M : SeminormBall n)
    {x y : (Fin n → ℝ)} (hx : x ∈ M.unitBall) (hy : y ∉ M.unitBall) :
    ∃ z, M.p z = 1 ∧ ‖x - z‖ ≤ ‖x - y‖ := by

  by_cases hxs : M.p x = 1
  · exact ⟨x, hxs, by simp⟩
  have hxi : M.p x < 1 := lt_of_le_of_ne (M.mem_unitBall.mp hx) hxs
  have hye : 1 < M.p y := lt_of_not_ge (by simpa [SeminormBall.mem_unitBall] using hy)
  rcases exists_segmentPoint_mem_modelSphere M hxi hye with ⟨t, ht, hz⟩
  refine ⟨segmentPoint x y t, hz, ?_⟩
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  rw [segmentPoint]
  have : x - ((1 - t) • x + t • y) = t • (x - y) := by module
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  exact mul_le_of_le_one_left (norm_nonneg _) ht1

private def zeroExtension {n N : ℕ} (M : SeminormBall n)
    (u : (Fin n → ℝ) → (Fin N → ℝ)) (x : (Fin n → ℝ)) : (Fin N → ℝ) := by
  classical
  exact if x ∈ M.unitBall then u x else 0

@[simp] private theorem zeroExtension_of_mem {n N : ℕ} (M : SeminormBall n)
    (u : (Fin n → ℝ) → (Fin N → ℝ)) {x : (Fin n → ℝ)} (hx : x ∈ M.unitBall) :
    zeroExtension M u x = u x := by
  classical
  simp [zeroExtension, hx]

@[simp] private theorem zeroExtension_of_not_mem {n N : ℕ} (M : SeminormBall n)
    (u : (Fin n → ℝ) → (Fin N → ℝ)) {x : (Fin n → ℝ)} (hx : x ∉ M.unitBall) :
    zeroExtension M u x = 0 := by
  classical
  simp [zeroExtension, hx]

private theorem lipschitz_zeroExtension {n N : ℕ} (M : SeminormBall n)
    {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : Lipschitz u)
    (hbdry : ∀ x, M.p x = 1 → u x = 0) :
    Lipschitz (zeroExtension M u) := by

  rcases hu with ⟨K, hK⟩
  refine ⟨K, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  by_cases hx : x ∈ M.unitBall <;> by_cases hy : y ∈ M.unitBall
  · simpa only [zeroExtension_of_mem M u hx, zeroExtension_of_mem M u hy] using
      hK.dist_le_mul x y
  · rcases exists_boundary_point_between M hx hy with ⟨z, hz, hxz⟩
    have huz : u z = 0 := hbdry z hz
    calc
      dist (zeroExtension M u x) (zeroExtension M u y) = dist (u x) (u z) := by
        rw [zeroExtension_of_mem M u hx, zeroExtension_of_not_mem M u hy, huz]
      _ ≤ (K : ℝ) * dist x z := hK.dist_le_mul x z
      _ ≤ (K : ℝ) * dist x y := by
        apply mul_le_mul_of_nonneg_left ?_ K.2
        simpa only [dist_eq_norm] using hxz
  · rcases exists_boundary_point_between M hy hx with ⟨z, hz, hyz⟩
    have huz : u z = 0 := hbdry z hz
    have hzy : dist z y ≤ dist x y := by
      simpa only [dist_eq_norm, norm_sub_rev] using hyz
    calc
      dist (zeroExtension M u x) (zeroExtension M u y) = dist (u z) (u y) := by
        rw [zeroExtension_of_not_mem M u hx, zeroExtension_of_mem M u hy, huz]
      _ ≤ (K : ℝ) * dist z y := hK.dist_le_mul z y
      _ ≤ (K : ℝ) * dist x y := mul_le_mul_of_nonneg_left hzy K.2
  · rw [zeroExtension_of_not_mem M u hx, zeroExtension_of_not_mem M u hy, dist_self]
    exact mul_nonneg K.2 dist_nonneg

private theorem support_zeroExtension_subset {n N : ℕ} (M : SeminormBall n)
    (u : (Fin n → ℝ) → (Fin N → ℝ)) :
    Function.support (zeroExtension M u) ⊆ M.unitBall := by
  intro x hx
  by_contra hnot
  exact hx (zeroExtension_of_not_mem M u hnot)

private theorem hasCompactSupport_zeroExtension {n N : ℕ} (M : SeminormBall n)
    (u : (Fin n → ℝ) → (Fin N → ℝ)) :
    HasCompactSupport (zeroExtension M u) := by

  exact HasCompactSupport.intro M.isCompact_unitBall fun x hx =>
    zeroExtension_of_not_mem M u hx

private def boundaryDifference {n N : ℕ}
    (F G : (Fin n → ℝ) → (Fin N → ℝ)) : (Fin n → ℝ) → (Fin N → ℝ) := fun x => F x - G x

private theorem boundaryDifference_eq_zero {n N : ℕ} (M : SeminormBall n)
    {F G : (Fin n → ℝ) → (Fin N → ℝ)}
    (htrace : ∀ u : ModelUnitSphere M, F u = G u)
    {x : (Fin n → ℝ)} (hx : M.p x = 1) : boundaryDifference F G x = 0 := by
  have h := htrace ⟨x, hx⟩
  simpa [boundaryDifference] using sub_eq_zero.mpr h

private def patchedMap {n N : ℕ} (M : SeminormBall n)
    (F G : (Fin n → ℝ) → (Fin N → ℝ)) : (Fin n → ℝ) → (Fin N → ℝ) :=
  fun x => G x + zeroExtension M (boundaryDifference F G) x

@[simp] private theorem patchedMap_eq_of_mem {n N : ℕ} (M : SeminormBall n)
    (F G : (Fin n → ℝ) → (Fin N → ℝ)) {x : (Fin n → ℝ)} (hx : x ∈ M.unitBall) :
    patchedMap M F G x = F x := by
  simp [patchedMap, zeroExtension_of_mem M _ hx, boundaryDifference]

@[simp] private theorem patchedMap_eq_of_not_mem {n N : ℕ} (M : SeminormBall n)
    (F G : (Fin n → ℝ) → (Fin N → ℝ)) {x : (Fin n → ℝ)} (hx : x ∉ M.unitBall) :
    patchedMap M F G x = G x := by
  simp [patchedMap, zeroExtension_of_not_mem M _ hx]

private theorem modelSphereSet_null {m : ℕ} (M : SeminormBall (m + 1)) :
    volume (modelSphereSet M) = 0 := by

  have hsphere :
      modelSphereSet M = frontier (M.p.ball (0 : (Fin (m + 1) → ℝ)) 1) := by
    ext x
    change M.p x = 1 ↔ x ∈ frontier (M.p.ball (0 : (Fin (m + 1) → ℝ)) 1)
    rw [← congrFun M.p.gauge_ball x]
    exact gauge_eq_one_iff_mem_frontier
      (M.p.convex_ball (0 : (Fin (m + 1) → ℝ)) (1 : ℝ))
      (M.p.ball_mem_nhds M.continuous_p zero_lt_one)
  rw [hsphere]
  exact (M.p.convex_ball (0 : (Fin (m + 1) → ℝ)) (1 : ℝ)).addHaar_frontier volume
private theorem integrable_lipschitz_compactPerturb_topMinor_difference_early
    {m N : ℕ} (s : Matrix.MaximalMinorIndex (m + 1) (Fin N))
    {g u : (Fin (m + 1) → ℝ) → (Fin N → ℝ)}
    (hg : Lipschitz g) (hu : Lipschitz u) (huc : HasCompactSupport u) :
    Integrable (fun x =>
      maximalMinorIntegrand s (fun y => g y + u y) x -
        maximalMinorIntegrand s g x) := by
  obtain ⟨Cg, hgW⟩ := hg
  obtain ⟨Cu, huW⟩ := hu
  have hgL : Lipschitz g := ⟨Cg, hgW⟩
  have hplus : Lipschitz (fun x => g x + u x) :=
    ⟨Cg + Cu, hgW.add huW⟩
  let d : (Fin (m + 1) → ℝ) → ℝ := fun x =>
    maximalMinorIntegrand s (fun y => g y + u y) x - maximalMinorIntegrand s g x
  have hdK : IntegrableOn d (tsupport u) := by
    exact (integrableOn_maximalMinor_fderiv_of_lipschitzWith s (hgW.add huW) huc).sub
      (integrableOn_maximalMinor_fderiv_of_lipschitzWith s hgW huc)
  have hdind : Integrable ((tsupport u).indicator d) :=
    hdK.integrable_indicator huc.measurableSet
  have hind : (tsupport u).indicator d = d := by
    funext x
    by_cases hx : x ∈ tsupport u
    · simp [hx]
    · have hz := topMinor_difference_eq_zero_of_not_mem_tsupport
        s (g := g) (u := u) hx
      simpa [hx, d] using hz.symm
  rw [hind] at hdind
  exact hdind

private theorem topMinor_boundary_trace {m N : ℕ} (M : SeminormBall (m + 1))
    (s : Matrix.MaximalMinorIndex (m + 1) (Fin N)) {F G : (Fin (m + 1) → ℝ) → (Fin N → ℝ)}
    (hF : Lipschitz F) (hG : Lipschitz G)
    (htrace : ∀ u : ModelUnitSphere M, F u = G u) :
    ∫ x in M.unitBall, maximalMinorIntegrand s F x =
      ∫ x in M.unitBall, maximalMinorIntegrand s G x := by

  let u := boundaryDifference F G
  let u0 := zeroExtension M u
  let H := patchedMap M F G
  let dHG : (Fin (m + 1) → ℝ) → ℝ := fun x =>
    maximalMinorIntegrand s H x - maximalMinorIntegrand s G x
  let dFG : (Fin (m + 1) → ℝ) → ℝ := fun x =>
    maximalMinorIntegrand s F x - maximalMinorIntegrand s G x
  obtain ⟨CF, hFW⟩ := hF
  obtain ⟨CG, hGW⟩ := hG
  have hFL : Lipschitz F := ⟨CF, hFW⟩
  have hGL : Lipschitz G := ⟨CG, hGW⟩
  have hu : Lipschitz u := by
    exact ⟨CF + CG, by
      change LipschitzWith (CF + CG) (fun x => F x - G x)
      exact hFW.sub hGW⟩
  have hub : ∀ x, M.p x = 1 → u x = 0 := by
    intro x hx
    simpa only [u] using boundaryDifference_eq_zero M htrace hx
  have hu0 : Lipschitz u0 := lipschitz_zeroExtension M hu hub
  have huc : HasCompactSupport u0 := hasCompactSupport_zeroExtension M u
  have hglobal : ∫ x, dHG x = 0 := by
    change (∫ x, maximalMinorIntegrand s (fun y => G y + u0 y) x -
      maximalMinorIntegrand s G x) = 0
    rcases hu0 with ⟨C0, h0⟩
    exact integral_maximalMinor_fderiv_add_sub_eq_zero_of_lipschitzWith s hGW h0 huc

  have houtside : dHG =ᵐ[volume.restrict (M.unitBall)ᶜ] 0 := by
    filter_upwards [ae_restrict_mem (M.unitBall_measurable.compl)] with x hx
    have hlocal : H =ᶠ[𝓝 x] G := by
      have hopen : IsOpen (M.unitBall)ᶜ := M.unitBall_isClosed.isOpen_compl
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact patchedMap_eq_of_not_mem M F G hy
    have hderiv : fderiv ℝ H x = fderiv ℝ G x := hlocal.fderiv_eq
    simp [dHG, maximalMinorIntegrand, hderiv]

  have hsphere_ae : ∀ᵐ x ∂volume.restrict M.unitBall,
      x ∉ modelSphereSet M := by
    apply ae_restrict_of_ae
    apply ae_iff.mpr
    rw [show {x | ¬ x ∉ modelSphereSet M} = modelSphereSet M by ext z; simp]
    exact modelSphereSet_null M

  have hinside : dHG =ᵐ[volume.restrict M.unitBall] dFG := by
    filter_upwards [ae_restrict_mem M.measurableSet_unitBall, hsphere_ae]
      with x hx hxsphere
    have hxle : M.p x ≤ 1 := M.mem_unitBall.mp hx
    have hxne : M.p x ≠ 1 := by
      simpa [modelSphereSet] using hxsphere
    have hxi : M.p x < 1 := lt_of_le_of_ne hxle hxne
    have hlocal : H =ᶠ[𝓝 x] F := by
      have hopen : IsOpen (modelOpenBall M) :=
        M.continuous_p.isOpen_preimage _ isOpen_Iio
      have hxopen : x ∈ modelOpenBall M := hxi
      filter_upwards [hopen.mem_nhds hxopen] with y hy
      exact patchedMap_eq_of_mem M F G (M.mem_unitBall.mpr hy.le)
    have hderiv : fderiv ℝ H x = fderiv ℝ F x := hlocal.fderiv_eq
    simp [dHG, dFG, maximalMinorIntegrand, hderiv]

  have hdiff_integrable : Integrable dHG := by
    change Integrable (fun x =>
      maximalMinorIntegrand s (fun y => G y + u0 y) x -
        maximalMinorIntegrand s G x)
    exact integrable_lipschitz_compactPerturb_topMinor_difference_early s hGL hu0 huc
  have houtside_integral : ∫ x in (M.unitBall)ᶜ, dHG x = 0 := by
    exact MeasureTheory.integral_eq_zero_of_ae houtside
  have hball_integral : ∫ x in M.unitBall, dHG x = 0 := by
    have hsplit :
        (∫ x, dHG x) =
          (∫ x in M.unitBall, dHG x) +
            ∫ x in (M.unitBall)ᶜ, dHG x := by
      exact (integral_add_compl M.measurableSet_unitBall hdiff_integrable).symm
    linarith [hglobal, hsplit, houtside_integral]
  have hFGzero : ∫ x in M.unitBall, dFG x = 0 := by
    rw [← integral_congr_ae hinside]
    exact hball_integral
  have hFi := integrableOn_maximalMinor_fderiv_of_lipschitzWith s hFW M.isCompact_unitBall
  have hGi := integrableOn_maximalMinor_fderiv_of_lipschitzWith s hGW M.isCompact_unitBall
  have hsub :
      (∫ x in M.unitBall, maximalMinorIntegrand s F x) -
        ∫ x in M.unitBall, maximalMinorIntegrand s G x = 0 := by
    simpa [dFG, integral_sub hFi hGi] using hFGzero
  exact sub_eq_zero.mp hsub

/-- Pointwise equality on a compact seminorm-ball boundary gives equality of maximal-minor integrals. -/
theorem integral_maximalMinor_eq_of_pointwise_boundary_eq
    {m N : ℕ} (p : Seminorm ℝ (Fin (m + 1) → ℝ)) (hp : Continuous p)
    (hK : IsCompact (p.closedBall 0 1))
    (s : Matrix.MaximalMinorIndex (m + 1) (Fin N))
    {F G : (Fin (m + 1) → ℝ) → (Fin N → ℝ)} {CF CG : ℝ≥0}
    (hF : LipschitzWith CF F) (hG : LipschitzWith CG G)
    (htrace : ∀ x, p x = 1 → F x = G x) :
    ∫ x in p.closedBall 0 1, maximalMinorIntegrand s F x =
      ∫ x in p.closedBall 0 1, maximalMinorIntegrand s G x := by
  let M : SeminormBall (m + 1) := ⟨p, hp, hK⟩
  exact topMinor_boundary_trace M s ⟨CF, hF⟩ ⟨CG, hG⟩
    (fun x => htrace x x.property)

end NullLagrangian
end MathlibAnnex
