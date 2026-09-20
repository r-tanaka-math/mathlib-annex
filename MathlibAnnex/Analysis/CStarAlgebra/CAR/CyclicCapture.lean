import MathlibAnnex.Analysis.CStarAlgebra.CAR.CaptureSurviving
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CyclicRestriction

/-!
# Cyclic pieces carried by the target defect vectors

Each vector supplied by the completed-CAR compression theorem generates a
closed reducing copy of the corresponding selected pure GNS representation.
Distinct selected classes give orthogonal cyclic pieces.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

universe v

/-- A unit vector with one of the selected vector states generates an
irreducible cyclic restriction, unitarily equivalent to that selected GNS
fiber. -/
theorem exists_selectedCyclicUnitary
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (sigma : Representation Limit K)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (eta : K) (heta : ‖eta‖ = 1)
    (hstate : Representation.vectorFunctional sigma eta =
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1) :
    let M := Representation.cyclicSubspace sigma eta
    letI : CompleteSpace M :=
      (Representation.isClosed_cyclicSubspace sigma eta).completeSpace_coe
    let tau := Representation.restrictToReducing sigma M
      (Representation.reduces_cyclicSubspace sigma eta)
    ∃ U : MathlibAnnex.CStarAlgebra.PureState.SelectedGNS completedRootPureState i ≃ₗᵢ[ℂ] M,
      tau.IsIrreducible ∧
      U (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i) =
        (⟨eta, Representation.self_mem_cyclicSubspace sigma eta⟩ : M) ∧
      ∀ a, (U : MathlibAnnex.CStarAlgebra.PureState.SelectedGNS completedRootPureState i →L[ℂ] M).comp
          (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i a) =
        (tau a).comp
          (U : MathlibAnnex.CStarAlgebra.PureState.SelectedGNS completedRootPureState i →L[ℂ] M) := by
  dsimp only
  letI : CompleteSpace (Representation.cyclicSubspace sigma eta) :=
    (Representation.isClosed_cyclicSubspace sigma eta).completeSpace_coe
  let z : Representation.cyclicSubspace sigma eta :=
    ⟨eta, Representation.self_mem_cyclicSubspace sigma eta⟩
  let tau := Representation.restrictToReducing sigma
    (Representation.cyclicSubspace sigma eta)
    (Representation.reduces_cyclicSubspace sigma eta)
  have hz : ‖z‖ = 1 := by simpa [z] using heta
  have hzstate : Representation.vectorFunctional tau z =
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1 := by
    rw [Representation.vectorFunctional_restrictToReducing]
    exact hstate
  have hcyclic : DenseRange (StarAlgHom.orbitMap tau z) := by
    exact Representation.denseRange_orbitMap_restrictCyclic sigma eta
  have hpure : IsPureState Limit (Representation.vectorFunctional tau z) := by
    rw [hzstate]
    exact (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).2
  have hstar : StarAlgHom.IsIrreducible tau :=
    MathlibAnnex.CStarAlgebra.isIrreducible_starAlgHom_of_isPureState tau z hz hcyclic hpure
  have hz_ne : z ≠ 0 := by
    intro hzero
    simpa [hzero] using hz
  letI : Nontrivial (Representation.cyclicSubspace sigma eta) :=
    nontrivial_of_ne z 0 hz_ne
  have hirr : tau.IsIrreducible :=
    (Representation.isIrreducible_iff_starAlgHom tau).2 hstar
  have hsourceCyclic : DenseRange (StarAlgHom.orbitMap
      (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i)
      (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)) :=
    MathlibAnnex.CStarAlgebra.PureState.denseRange_representative_gns_orbit completedRootPureState i
  have hcoeff (a : Limit) :
      inner ℂ (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)
          (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i a
            (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)) =
        inner ℂ z (tau a z) := by
    calc
      inner ℂ (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)
          (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i a
            (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)) =
          (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1 a := by
            have h := congrArg (fun f : Limit →L[ℂ] ℂ ↦ f a)
              (MathlibAnnex.CStarAlgebra.PureState.selected_vectorFunctional completedRootPureState i)
            exact h
      _ = Representation.vectorFunctional tau z a := by rw [hzstate]
      _ = inner ℂ z (tau a z) := rfl
  obtain ⟨U, hU, -⟩ := StarAlgHom.existsUnique_pointedCyclicTransport
    (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i) tau
    (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i) z
    hsourceCyclic hcyclic hcoeff
  refine ⟨U, ?_⟩
  simpa [tau, z] using (show tau.IsIrreducible ∧
      U (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i) = z ∧
      ∀ a, (U : MathlibAnnex.CStarAlgebra.PureState.SelectedGNS completedRootPureState i →L[ℂ]
          Representation.cyclicSubspace sigma eta).comp
            (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i a) =
        (tau a).comp
          (U : MathlibAnnex.CStarAlgebra.PureState.SelectedGNS completedRootPureState i →L[ℂ]
            Representation.cyclicSubspace sigma eta) from
    ⟨hirr, hU.2.1, hU.2.2⟩)

/-- Cyclic subspaces carrying two distinct selected pure-state classes are
orthogonal.  The projection from one cyclic piece to the other is an
intertwiner; Schur and the chosen-representative separation force it to
vanish. -/
theorem isOrtho_cyclicSubspace_of_selectedStates
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (sigma : Representation Limit K)
    {i j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit} (hij : i ≠ j)
    (eta_i eta_j : K) (heta_i : ‖eta_i‖ = 1) (heta_j : ‖eta_j‖ = 1)
    (hstate_i : Representation.vectorFunctional sigma eta_i =
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1)
    (hstate_j : Representation.vectorFunctional sigma eta_j =
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState j).1) :
    Representation.cyclicSubspace sigma eta_i ⟂
      Representation.cyclicSubspace sigma eta_j := by
  let Mi := Representation.cyclicSubspace sigma eta_i
  let Mj := Representation.cyclicSubspace sigma eta_j
  have hMiClosed : IsClosed (Mi : Set K) :=
    Representation.isClosed_cyclicSubspace sigma eta_i
  have hMjClosed : IsClosed (Mj : Set K) :=
    Representation.isClosed_cyclicSubspace sigma eta_j
  letI : CompleteSpace Mi := hMiClosed.completeSpace_coe
  letI : CompleteSpace Mj := hMjClosed.completeSpace_coe
  letI : Mi.HasOrthogonalProjection := by
    letI : IsClosed (Mi : Set K) := hMiClosed
    infer_instance
  let tau_i := Representation.restrictToReducing sigma Mi
    (Representation.reduces_cyclicSubspace sigma eta_i)
  let tau_j := Representation.restrictToReducing sigma Mj
    (Representation.reduces_cyclicSubspace sigma eta_j)
  obtain ⟨Ui, hirri, -, hUi⟩ :=
    exists_selectedCyclicUnitary sigma i eta_i heta_i hstate_i
  obtain ⟨Uj, hirrj, -, hUj⟩ :=
    exists_selectedCyclicUnitary sigma j eta_j heta_j hstate_j
  let zi : Mi := ⟨eta_i, Representation.self_mem_cyclicSubspace sigma eta_i⟩
  let zj : Mj := ⟨eta_j, Representation.self_mem_cyclicSubspace sigma eta_j⟩
  have hzi_ne : zi ≠ 0 := by
    intro hzero
    have h := congrArg norm hzero
    simpa [zi, heta_i] using h
  have hzj_ne : zj ≠ 0 := by
    intro hzero
    have h := congrArg norm hzero
    simpa [zj, heta_j] using h
  letI : Nontrivial Mi := nontrivial_of_ne zi 0 hzi_ne
  letI : Nontrivial Mj := nontrivial_of_ne zj 0 hzj_ne
  let V : Mj →L[ℂ] Mi := Mi.orthogonalProjectionOnto.comp Mj.subtypeL
  have hV : StarAlgHom.Intertwines tau_j tau_i V := by
    intro a
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    have hcomm := Representation.starProjection_commutes_of_reduces sigma Mi
      (Representation.reduces_cyclicSubspace sigma eta_i) a
    have hx := congrArg (fun T : K →L[ℂ] K ↦ T (x : K)) hcomm
    change Mi.starProjection (sigma a (x : K)) =
      sigma a (Mi.starProjection (x : K))
    exact hx
  have hno (E : Mj ≃ₗᵢ[ℂ] Mi) :
      ¬ StarAlgHom.Intertwines tau_j tau_i (E : Mj →L[ℂ] Mi) := by
    intro hE
    have hUjEq : Representation.UnitaryEquivalent
        (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState j) tau_j := by
      refine ⟨Uj, fun a x ↦ ?_⟩
      have h := congrArg
        (fun T : MathlibAnnex.CStarAlgebra.PureState.SelectedGNS completedRootPureState j →L[ℂ] Mj ↦ T x)
        (hUj a)
      simpa [ContinuousLinearMap.comp_apply] using h
    have hEEq : Representation.UnitaryEquivalent tau_j tau_i := by
      refine ⟨E, fun a x ↦ ?_⟩
      have h := congrArg (fun T : Mj →L[ℂ] Mi ↦ T x) (hE a)
      simpa [ContinuousLinearMap.comp_apply] using h
    have hUiEq : Representation.UnitaryEquivalent
        (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i) tau_i := by
      refine ⟨Ui, fun a x ↦ ?_⟩
      have h := congrArg
        (fun T : MathlibAnnex.CStarAlgebra.PureState.SelectedGNS completedRootPureState i →L[ℂ] Mi ↦ T x)
        (hUi a)
      simpa [ContinuousLinearMap.comp_apply] using h
    have hselected : Representation.UnitaryEquivalent
        (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState j)
        (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i) :=
      Representation.unitaryEquivalent_trans hUjEq
        (Representation.unitaryEquivalent_trans hEEq
          (Representation.unitaryEquivalent_symm hUiEq))
    obtain ⟨W, hW⟩ := hselected
    apply MathlibAnnex.CStarAlgebra.PureState.no_unitaryIntertwiner_selectedRepresentation
      completedRootPureState hij.symm W
    intro a
    apply ContinuousLinearMap.ext
    intro x
    simpa [ContinuousLinearMap.comp_apply] using hW a x
  have hVzero : V = 0 :=
    StarAlgHom.Intertwines.eq_zero_of_no_unitary
      (Representation.isIrreducible_starAlgHom tau_j hirrj)
      (Representation.isIrreducible_starAlgHom tau_i hirri)
      hno hV
  apply Submodule.orthogonalProjectionOnto_comp_subtypeL_eq_zero_iff.mp
  simpa [V] using hVzero

/-- On its own cyclic pure-state piece, the ambient common fixed projection
has image in the distinguished one-dimensional line.  This is an ambient-to-
cyclic restriction statement, not an ambient multiplicity claim. -/
theorem initialFixedProjection_maps_ownCyclic
    (family : RepresentativeShellFamily)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (sigma : Representation Limit K)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (eta : K)
    (hfixed : ∀ n, sigma (transportedFlag family i n) eta = eta)
    {x : K} (hx : x ∈ Representation.cyclicSubspace sigma eta) :
    commonFixedProjection (fun n ↦ sigma (transportedFlag family i n)) x ∈
      ℂ ∙ eta := by
  let q := transportedFlag family i
  let phi : Limit →L[ℂ] ℂ :=
    (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1
  let P : K →L[ℂ] K := commonFixedProjection (fun n ↦ sigma (q n))
  have hPeta : P eta = eta := by
    exact (commonFixedProjection_eq_self_iff (fun n ↦ sigma (q n)) eta).2
      ((mem_commonFixedSubspace_iff (fun n ↦ sigma (q n)) eta).2 hfixed)
  have hoperator (b : Limit) : P * sigma b * P = (phi b) • P := by
    exact commonFixedProjection_comp_map_comp_eq sigma
      (Representation.continuousLinearMap sigma).continuous q phi b
      (fun n ↦ (isStarProjection_transportedFlag family i n).isSelfAdjoint.star_eq)
      (tendsto_representative_transported_compression family i b)
  have horbit (b : Limit) : P (sigma b eta) = phi b • eta := by
    have h := congrArg (fun T : K →L[ℂ] K ↦ T eta) (hoperator b)
    simpa [hPeta] using h
  let M := Representation.cyclicSubspace sigma eta
  letI : CompleteSpace M :=
    (Representation.isClosed_cyclicSubspace sigma eta).completeSpace_coe
  let tau := Representation.restrictToReducing sigma M
    (Representation.reduces_cyclicSubspace sigma eta)
  let z : M := ⟨eta, Representation.self_mem_cyclicSubspace sigma eta⟩
  have hdense : DenseRange (StarAlgHom.orbitMap tau z) :=
    Representation.denseRange_orbitMap_restrictCyclic sigma eta
  have hspanClosed : IsClosed ((ℂ ∙ eta : Submodule ℂ K) : Set K) :=
    Submodule.closed_of_finiteDimensional _
  have hclosed : IsClosed {y : M | P (y : K) ∈ (ℂ ∙ eta : Submodule ℂ K)} :=
    hspanClosed.preimage (P.comp M.subtypeL).continuous
  have hall : ∀ y : M, P (y : K) ∈ (ℂ ∙ eta : Submodule ℂ K) := by
    intro y
    exact hdense.induction_on y hclosed fun b ↦ by
      change P (sigma b eta) ∈ (ℂ ∙ eta : Submodule ℂ K)
      rw [horbit b]
      exact (ℂ ∙ eta).smul_mem (phi b) (Submodule.mem_span_singleton_self eta)
  exact hall ⟨x, hx⟩

/-- The common fixed projection for class `i` vanishes on the cyclic piece
of a different selected class `j`.  Every nonzero vector in the ambient
fixed range would itself carry class `i`, so orthogonality and the projection
norm identity exclude such a component. -/
theorem initialFixedProjection_eq_zero_on_otherCyclic
    (family : RepresentativeShellFamily)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (sigma : Representation Limit K)
    {i j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit} (hij : i ≠ j)
    (eta_j : K) (heta_j : ‖eta_j‖ = 1)
    (hstate_j : Representation.vectorFunctional sigma eta_j =
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState j).1)
    {x : K} (hx : x ∈ Representation.cyclicSubspace sigma eta_j) :
    commonFixedProjection (fun n ↦ sigma (transportedFlag family i n)) x = 0 := by
  let q := transportedFlag family i
  let phi : Limit →L[ℂ] ℂ :=
    (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1
  let F := commonFixedSubspace (fun n ↦ sigma (q n))
  let P : K →L[ℂ] K := commonFixedProjection (fun n ↦ sigma (q n))
  let y : K := P x
  by_contra hyzero
  have hy_ne : y ≠ 0 := hyzero
  let z : K := NormedSpace.normalize y
  have hz_norm : ‖z‖ = 1 := NormedSpace.norm_normalize hy_ne
  have hy_fixed (n : ℕ) : sigma (q n) y = y := by
    exact commonFixedProjection_apply_fixed (fun n ↦ sigma (q n)) n x
  have hz_fixed (n : ℕ) : sigma (q n) z = z := by
    change sigma (q n) (((‖y‖⁻¹ : ℝ) : ℂ) • y) =
      ((‖y‖⁻¹ : ℝ) : ℂ) • y
    rw [map_smul, hy_fixed]
  have hz_state : Representation.vectorFunctional sigma z = phi := by
    apply vectorFunctional_eq_of_compression_tendsto sigma q phi
      (fun n ↦ (isStarProjection_transportedFlag family i n).isSelfAdjoint.star_eq)
      (tendsto_representative_transported_compression family i)
      z hz_norm hz_fixed
  have horth := isOrtho_cyclicSubspace_of_selectedStates sigma hij z eta_j
    hz_norm heta_j hz_state hstate_j
  have hzx : inner ℂ z x = 0 := horth.inner_eq
    (Representation.self_mem_cyclicSubspace sigma z) hx
  have hy_eq : y = (‖y‖ : ℂ) • z := by
    simpa [z, Complex.real_smul] using (NormedSpace.norm_smul_normalize y).symm
  have hyx : inner ℂ y x = 0 := by
    rw [hy_eq, inner_smul_left, hzx, mul_zero]
  have hnormsq := Submodule.re_inner_starProjection_eq_normSq F x
  change (inner ℂ (P x) x).re = ‖P x‖ ^ 2 at hnormsq
  have hnorm_zero : ‖y‖ ^ 2 = 0 := by
    calc
      ‖y‖ ^ 2 = (inner ℂ y x).re := hnormsq.symm
      _ = 0 := by rw [hyx]; rfl
  exact hy_ne (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm_zero))

/-- The cyclic copies of all selected pure states assemble to an isometric
source intertwiner from the displayed arbitrary-index atomic Hilbert sum into
the target Hilbert space.  The ambient fixed projection for class `i` maps
the isometry range into the distinguished line carried by the `i`-th selected
vector (and hence back into the isometry range).  Surjectivity is deliberately
not asserted here; it is the remaining generated-target reduction step. -/
theorem exists_selectedAtomicCyclicIsometry
    (family : RepresentativeShellFamily)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (sigma : Representation Limit K)
    (eta : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit → K)
    (heta : ∀ i, ‖eta i‖ = 1)
    (hstate : ∀ i, Representation.vectorFunctional sigma (eta i) =
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1) :
    ∃ W : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →ₗᵢ[ℂ] K,
      (∀ i x, W (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i x) ∈
        Representation.cyclicSubspace sigma (eta i)) ∧
      (∀ i, W (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
        (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)) = eta i) ∧
      (∀ i x, commonFixedProjection
        (fun n ↦ sigma (transportedFlag family i n)) (W x) ∈
          ℂ ∙ eta i) ∧
      ∀ a,
        W.toContinuousLinearMap.comp
            (selectedAtomicRepresentation a) =
          (sigma a).comp
            W.toContinuousLinearMap := by
  classical
  let M (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :=
    Representation.cyclicSubspace sigma (eta i)
  letI instComplete (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) : CompleteSpace (M i) :=
    (Representation.isClosed_cyclicSubspace sigma (eta i)).completeSpace_coe
  have hex (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
      ∃ U : MathlibAnnex.CStarAlgebra.PureState.SelectedGNS completedRootPureState i ≃ₗᵢ[ℂ] M i,
        let tau := Representation.restrictToReducing sigma (M i)
          (Representation.reduces_cyclicSubspace sigma (eta i))
        tau.IsIrreducible ∧
        U (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i) =
          (⟨eta i, Representation.self_mem_cyclicSubspace sigma (eta i)⟩ : M i) ∧
        ∀ a, (U : MathlibAnnex.CStarAlgebra.PureState.SelectedGNS completedRootPureState i →L[ℂ] M i).comp
            (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i a) =
          (tau a).comp
            (U : MathlibAnnex.CStarAlgebra.PureState.SelectedGNS completedRootPureState i →L[ℂ] M i) := by
    simpa [M] using
      exists_selectedCyclicUnitary sigma i (eta i) (heta i) (hstate i)
  choose U hU using hex
  let V (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
      MathlibAnnex.CStarAlgebra.PureState.SelectedGNS completedRootPureState i →ₗᵢ[ℂ] K :=
    (M i).subtypeₗᵢ.comp (U i).toLinearIsometry
  have hVortho : OrthogonalFamily ℂ
      (MathlibAnnex.CStarAlgebra.PureState.SelectedGNS completedRootPureState) V := by
    intro i j hij x y
    have horth := isOrtho_cyclicSubspace_of_selectedStates sigma hij
      (eta i) (eta j) (heta i) (heta j) (hstate i) (hstate j)
    exact horth.inner_eq (by
      change (U i x : K) ∈ Representation.cyclicSubspace sigma (eta i)
      exact (U i x).property) (by
      change (U j y : K) ∈ Representation.cyclicSubspace sigma (eta j)
      exact (U j y).property)
  let W : MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →ₗᵢ[ℂ] K :=
    hVortho.linearIsometry
  have hWpoint (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
      W (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
        (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)) = eta i := by
    have hsingle := OrthogonalFamily.linearIsometry_apply_single hVortho
      (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)
    calc
      W (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i
          (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i)) =
          V i (MathlibAnnex.CStarAlgebra.PureState.selectedVector completedRootPureState i) := by
            simpa [W, MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding,
              MathlibAnnex.Analysis.InnerProductSpace.coordinateEmbedding_apply] using hsingle
      _ = eta i := by
        have h := congrArg Subtype.val ((hU i).2.1)
        simpa [V] using h
  have hVintertwines (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (a : Limit)
      (x : MathlibAnnex.CStarAlgebra.PureState.SelectedGNS completedRootPureState i) :
      V i (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i a x) =
        sigma a (V i x) := by
    have h := congrArg
      (fun T : MathlibAnnex.CStarAlgebra.PureState.SelectedGNS completedRootPureState i →L[ℂ] M i ↦ T x)
      ((hU i).2.2 a)
    have h' := congrArg Subtype.val h
    simpa [V, ContinuousLinearMap.comp_apply,
      Representation.restrictToReducing_apply_coe] using h'
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · intro i x
    have hsingle := OrthogonalFamily.linearIsometry_apply_single hVortho x
    have heq : W (MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding completedRootPureState i x) =
        V i x := by
      simpa [W, MathlibAnnex.CStarAlgebra.PureState.selectedEmbedding,
        MathlibAnnex.Analysis.InnerProductSpace.coordinateEmbedding_apply] using hsingle
    rw [heq]
    change (U i x : K) ∈ Representation.cyclicSubspace sigma (eta i)
    exact (U i x).property
  · intro i
    exact hWpoint i
  · intro i x
    let P : K →L[ℂ] K := commonFixedProjection
      (fun n ↦ sigma (transportedFlag family i n))
    have hsum : Summable (fun j ↦ V j (x j)) := hVortho.summable_of_lp x
    have hother (j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (hji : j ≠ i) :
        P (V j (x j)) = 0 := by
      apply initialFixedProjection_eq_zero_on_otherCyclic family sigma hji.symm
        (eta j) (heta j) (hstate j)
      change (U j (x j) : K) ∈ Representation.cyclicSubspace sigma (eta j)
      exact (U j (x j)).property
    have hcollapse : (∑' j, P (V j (x j))) = P (V i (x i)) := by
      exact tsum_eq_single i hother
    have hfixed_i (n : ℕ) :
        sigma (transportedFlag family i n) (eta i) = eta i := by
      apply projection_apply_eq_self_of_vectorFunctional_eq_one sigma
        (transportedFlag family i n) (isStarProjection_transportedFlag family i n)
        (eta i) (heta i)
      rw [hstate i]
      calc
        (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1
            (transportedFlag family i n) = rootState (rootFlag n) :=
          (representativeShellData family i).state_eq (rootFlag n)
        _ = 1 := rootState_rootFlag n
    have hown : P (V i (x i)) ∈ (ℂ ∙ eta i : Submodule ℂ K) := by
      apply initialFixedProjection_maps_ownCyclic family sigma i (eta i)
        hfixed_i
      change (U i (x i) : K) ∈ Representation.cyclicSubspace sigma (eta i)
      exact (U i (x i)).property
    have hPW : P (W x) = P (V i (x i)) := by
      calc
        P (W x) = P (∑' j, V j (x j)) := by
          rw [OrthogonalFamily.linearIsometry_apply hVortho]
        _ = ∑' j, P (V j (x j)) := P.map_tsum hsum
        _ = P (V i (x i)) := hcollapse
    rw [hPW]
    exact hown
  · intro a
    apply ContinuousLinearMap.ext
    intro x
    change W (selectedAtomicRepresentation a x) = sigma a (W x)
    calc
      W (selectedAtomicRepresentation a x) =
          ∑' i, V i ((selectedAtomicRepresentation a x) i) := by
            exact OrthogonalFamily.linearIsometry_apply hVortho _
      _ = ∑' i, V i
          (MathlibAnnex.CStarAlgebra.PureState.selectedRepresentation completedRootPureState i a (x i)) := by
            apply tsum_congr
            intro i
            rw [selectedAtomicRepresentation]
            rfl
      _ = ∑' i, sigma a (V i (x i)) := by
            apply tsum_congr
            intro i
            exact hVintertwines i a (x i)
      _ = sigma a (∑' i, V i (x i)) := by
            exact ((sigma a).map_tsum (hVortho.summable_of_lp x)).symm
      _ = sigma a (W x) := by
            rw [OrthogonalFamily.linearIsometry_apply hVortho]

end MathlibAnnex.CStarAlgebra.CAR
