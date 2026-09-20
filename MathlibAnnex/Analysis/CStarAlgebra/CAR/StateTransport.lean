import MathlibAnnex.Analysis.CStarAlgebra.CAR.LocalTransport
import MathlibAnnex.Analysis.CStarAlgebra.CAR.StagePurification

/-!
# Local transport of CAR vector states

This file separates the exact same-representation correction from the
finite-stage approximation used between different representations.  The
protected finite set and its tolerance are fixed before the state tests; a
later target finite set is handled by finite-stage purification.
-/

set_option autoImplicit false

noncomputable section

open MathlibAnnex.Analysis.CStarAlgebra

namespace MathlibAnnex.CStarAlgebra.CAR

set_option maxHeartbeats 800000 in
/-- A target vector state in another representation can be approximated on
any later finite set while the implementing inner automorphism nearly fixes
an earlier protected finite set.  Closeness on the fixed stage tests is the
only hypothesis connecting the two original vector states. -/
theorem exists_stageTests_crossRepresentation_path_approx
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (F : Finset Limit) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ n, ∃ delta > 0,
      ∀ {K : Type*}
        [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
        (sigma : Representation Limit K) (xi : H) (eta : K),
      ‖xi‖ = 1 → ‖eta‖ = 1 →
      (∀ i j : Fin (2 ^ n),
        ‖Representation.vectorFunctional rho xi (limitMatrixUnit n i j) -
          Representation.vectorFunctional sigma eta (limitMatrixUnit n i j)‖ < delta) →
      ∀ (F' : Finset Limit) (epsilon' : ℝ), 0 < epsilon' →
        ∃ u : unitary Limit,
          ∃ p : Path 1 u,
          (∀ t, ∀ a ∈ F,
            ‖(p t : Limit) * a * star (p t : Limit) - a‖ < epsilon ∧
            ‖star (p t : Limit) * a * (p t : Limit) - a‖ < epsilon) ∧
          ∀ a ∈ F',
            ‖Representation.vectorFunctional rho (rho (u : Limit) xi) a -
              Representation.vectorFunctional sigma eta a‖ < epsilon' := by
  classical
  obtain ⟨n, delta, hdelta, hlocal⟩ :=
    exists_stageTests_exact_unitary_path_apply_eq_and_conjugate_sub_norm_lt
      rho hrho F hepsilon
  refine ⟨n, delta, hdelta, ?_⟩
  intro K _ _ _ sigma xi eta hxi heta hstate F' epsilon' hepsilon'
  obtain ⟨m, hm⟩ := exists_common_stage_approx F'
    (show 0 < epsilon' / 3 by positivity)
  let N : ℕ := max n m
  have hnN : n ≤ N := le_max_left n m
  have hmN : m ≤ N := le_max_right n m
  obtain ⟨zeta, hzeta, hzstage⟩ :=
    exists_unitVector_vectorFunctional_eq_on_stage rho
      ((Representation.isIrreducible_iff_starAlgHom rho).mpr hrho)
      sigma N eta heta
  have hzmatrix (i j : Fin (2 ^ n)) :
      Representation.vectorFunctional rho zeta (limitMatrixUnit n i j) =
        Representation.vectorFunctional sigma eta (limitMatrixUnit n i j) := by
    have h := hzstage (embed n N hnN (matrixUnit n i j))
    simpa only [ofStage_embed, limitMatrixUnit] using h
  obtain ⟨u, huapply, p, huprotect⟩ := hlocal xi zeta hxi hzeta (by
    intro i j
    rw [hzmatrix i j]
    exact hstate i j)
  refine ⟨u, p, huprotect, ?_⟩
  intro a ha
  obtain ⟨c, hc⟩ := hm a ha
  let d : Limit := ofStage N (embed m N hmN c)
  have hd : d = ofStage m c := by
    dsimp only [d]
    rw [ofStage_embed]
  have htarget :
      Representation.vectorFunctional rho zeta d =
        Representation.vectorFunctional sigma eta d := by
    dsimp only [d]
    exact hzstage (embed m N hmN c)
  rw [huapply]
  have hdecomp :
      Representation.vectorFunctional rho zeta a -
          Representation.vectorFunctional sigma eta a =
        Representation.vectorFunctional rho zeta (a - d) +
          Representation.vectorFunctional sigma eta (d - a) := by
    rw [map_sub, map_sub, htarget]
    ring
  rw [hdecomp]
  calc
    _ ≤ ‖Representation.vectorFunctional rho zeta (a - d)‖ +
        ‖Representation.vectorFunctional sigma eta (d - a)‖ := norm_add_le _ _
    _ ≤ ‖a - d‖ + ‖d - a‖ := by
      exact add_le_add
        (Representation.norm_vectorFunctional_apply_le rho hzeta (a - d))
        (Representation.norm_vectorFunctional_apply_le sigma heta (d - a))
    _ = 2 * ‖a - d‖ := by rw [norm_sub_rev d a]; ring
    _ < epsilon' := by
      rw [hd]
      linarith

set_option maxHeartbeats 800000 in
/-- Endpoint-only compatibility wrapper for
`exists_stageTests_crossRepresentation_path_approx`. -/
theorem exists_stageTests_crossRepresentation_approx
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (F : Finset Limit) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ n, ∃ delta > 0,
      ∀ {K : Type*}
        [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
        (sigma : Representation Limit K) (xi : H) (eta : K),
      ‖xi‖ = 1 → ‖eta‖ = 1 →
      (∀ i j : Fin (2 ^ n),
        ‖Representation.vectorFunctional rho xi (limitMatrixUnit n i j) -
          Representation.vectorFunctional sigma eta (limitMatrixUnit n i j)‖ < delta) →
      ∀ (F' : Finset Limit) (epsilon' : ℝ), 0 < epsilon' →
        ∃ u : unitary Limit,
          (∀ a ∈ F,
            ‖(u : Limit) * a * star (u : Limit) - a‖ < epsilon ∧
            ‖star (u : Limit) * a * (u : Limit) - a‖ < epsilon) ∧
          ∀ a ∈ F',
            ‖Representation.vectorFunctional rho (rho (u : Limit) xi) a -
              Representation.vectorFunctional sigma eta a‖ < epsilon' := by
  obtain ⟨n, delta, hdelta, hmain⟩ :=
    exists_stageTests_crossRepresentation_path_approx rho hrho F hepsilon
  refine ⟨n, delta, hdelta, ?_⟩
  intro K _ _ _ sigma xi eta hxi heta hstate F' epsilon' hepsilon'
  obtain ⟨u, p, hprotect, happrox⟩ :=
    hmain sigma xi eta hxi heta hstate F' epsilon' hepsilon'
  refine ⟨u, ?_, happrox⟩
  intro a ha
  simpa only [p.target] using hprotect (1 : Set.Icc (0 : ℝ) 1) a ha

set_option maxHeartbeats 800000 in
/-- With no near-centrality requirement, one irreducible CAR representation
can approximate an arbitrary unit vector state from another representation on
any finite set.  Stage zero supplies the exact transitivity step, while
finite-stage purification supplies the requested state accuracy. -/
theorem exists_unitary_crossRepresentation_path_approx
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (sigma : Representation Limit K) (xi : H) (eta : K)
    (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1)
    (F : Finset Limit) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ u : unitary Limit, ∃ p : Path 1 u, ∀ a ∈ F,
      ‖Representation.vectorFunctional rho (rho (u : Limit) xi) a -
        Representation.vectorFunctional sigma eta a‖ < epsilon := by
  classical
  obtain ⟨m, hm⟩ := exists_common_stage_approx F
    (show 0 < epsilon / 3 by positivity)
  obtain ⟨zeta, hzeta, hzstage⟩ :=
    exists_unitVector_vectorFunctional_eq_on_stage rho
      ((Representation.isIrreducible_iff_starAlgHom rho).mpr hrho)
      sigma m eta heta
  obtain ⟨delta, hdelta, htrans⟩ :=
    exists_delta_exact_unitary_path_apply_eq_and_stage_commutator
      rho hrho 0 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨u, huapply, p, _⟩ := htrans xi zeta hxi hzeta (by
    intro i j
    have hunit : limitMatrixUnit 0 (0 : Fin (2 ^ 0)) (0 : Fin (2 ^ 0)) = 1 := by
      simpa using sum_limitMatrixUnit_diag 0
    have hij : limitMatrixUnit 0 i j = 1 := by
      rw [← hunit]
      congr <;> apply Fin.ext <;> simp
    rw [hij, Representation.vectorFunctional_one rho hxi,
      Representation.vectorFunctional_one rho hzeta, sub_self, norm_zero]
    exact hdelta)
  refine ⟨u, p, ?_⟩
  intro a ha
  obtain ⟨c, hc⟩ := hm a ha
  have htarget := hzstage c
  rw [huapply]
  have hdecomp :
      Representation.vectorFunctional rho zeta a -
          Representation.vectorFunctional sigma eta a =
        Representation.vectorFunctional rho zeta (a - ofStage m c) +
          Representation.vectorFunctional sigma eta (ofStage m c - a) := by
    rw [map_sub, map_sub, htarget]
    ring
  rw [hdecomp]
  calc
    _ ≤ ‖Representation.vectorFunctional rho zeta (a - ofStage m c)‖ +
        ‖Representation.vectorFunctional sigma eta (ofStage m c - a)‖ :=
      norm_add_le _ _
    _ ≤ ‖a - ofStage m c‖ + ‖ofStage m c - a‖ := by
      exact add_le_add
        (Representation.norm_vectorFunctional_apply_le rho hzeta _)
        (Representation.norm_vectorFunctional_apply_le sigma heta _)
    _ = 2 * ‖a - ofStage m c‖ := by
      rw [norm_sub_rev (ofStage m c) a]
      ring
    _ < epsilon := by linarith

set_option maxHeartbeats 800000 in
/-- Endpoint-only compatibility wrapper for
`exists_unitary_crossRepresentation_path_approx`. -/
theorem exists_unitary_crossRepresentation_approx
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (sigma : Representation Limit K) (xi : H) (eta : K)
    (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1)
    (F : Finset Limit) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ u : unitary Limit, ∀ a ∈ F,
      ‖Representation.vectorFunctional rho (rho (u : Limit) xi) a -
        Representation.vectorFunctional sigma eta a‖ < epsilon := by
  obtain ⟨u, -, happrox⟩ := exists_unitary_crossRepresentation_path_approx
    rho hrho sigma xi eta hxi heta F hepsilon
  exact ⟨u, happrox⟩

set_option maxHeartbeats 800000 in
/-- Pure-state form of cross-representation local transport.  For a fixed
source pure state and protected finite set, the finite stage tests are chosen
before the target pure state and before the later approximation request. -/
theorem exists_stageTests_pureState_path_approx
    (phi : Limit →L[ℂ] ℂ) (hphi : MathlibAnnex.CStarAlgebra.IsPureState Limit phi)
    (F : Finset Limit) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ n, ∃ delta > 0,
      ∀ (psi : Limit →L[ℂ] ℂ), MathlibAnnex.CStarAlgebra.IsPureState Limit psi →
      (∀ i j : Fin (2 ^ n),
        ‖phi (limitMatrixUnit n i j) - psi (limitMatrixUnit n i j)‖ < delta) →
      ∀ (F' : Finset Limit) (epsilon' : ℝ), 0 < epsilon' →
        ∃ u : unitary Limit,
          ∃ p : Path 1 u,
          (∀ t, ∀ a ∈ F,
            ‖star (p t : Limit) * a * (p t : Limit) - a‖ < epsilon) ∧
          ∀ a ∈ F',
            ‖phi (star (u : Limit) * a * (u : Limit)) - psi a‖ < epsilon' := by
  have hphiState : phi ∈ stateSpace Limit := extremePoints_subset hphi
  let fphi := positiveLinearMapOfMemStateSpace phi hphiState
  let rho : Representation Limit fphi.GNS := fphi.gnsStarAlgHom
  let xi : fphi.GNS := fphi.gnsCyclicVector
  have hxi : ‖xi‖ = 1 := by
    change ‖stateGNSVector phi hphiState‖ = 1
    exact norm_stateGNSVector phi hphiState
  letI : Nontrivial fphi.GNS := by
    apply nontrivial_of_ne xi 0
    intro hzero
    have hnorm := congrArg norm hzero
    rw [hxi, norm_zero] at hnorm
    norm_num at hnorm
  have hrho : StarAlgHom.IsIrreducible rho := by
    simpa [rho, fphi] using
      isIrreducible_pureState_gnsStarAlgHom phi hphiState hphi
  have hphiVF : Representation.vectorFunctional rho xi = phi := by
    apply ContinuousLinearMap.ext
    intro a
    rw [Representation.vectorFunctional_apply]
    change inner ℂ (stateGNSVector phi hphiState)
      ((positiveLinearMapOfMemStateSpace phi hphiState).gnsStarAlgHom a
        (stateGNSVector phi hphiState)) = phi a
    exact inner_gnsStarAlgHom_stateGNSVector phi hphiState a
  obtain ⟨n, delta, hdelta, hcross⟩ :=
    exists_stageTests_crossRepresentation_path_approx rho hrho F hepsilon
  refine ⟨n, delta, hdelta, ?_⟩
  intro psi hpsi hstate F' epsilon' hepsilon'
  have hpsiState : psi ∈ stateSpace Limit := extremePoints_subset hpsi
  let fpsi := positiveLinearMapOfMemStateSpace psi hpsiState
  let sigma : Representation Limit fpsi.GNS := fpsi.gnsStarAlgHom
  let eta : fpsi.GNS := fpsi.gnsCyclicVector
  have heta : ‖eta‖ = 1 := by
    change ‖stateGNSVector psi hpsiState‖ = 1
    exact norm_stateGNSVector psi hpsiState
  have hpsiVF : Representation.vectorFunctional sigma eta = psi := by
    apply ContinuousLinearMap.ext
    intro a
    rw [Representation.vectorFunctional_apply]
    change inner ℂ (stateGNSVector psi hpsiState)
      ((positiveLinearMapOfMemStateSpace psi hpsiState).gnsStarAlgHom a
        (stateGNSVector psi hpsiState)) = psi a
    exact inner_gnsStarAlgHom_stateGNSVector psi hpsiState a
  obtain ⟨u, p, hprotect, happrox⟩ :=
    hcross sigma xi eta hxi heta (by
      intro i j
      rw [hphiVF, hpsiVF]
      exact hstate i j) F' epsilon' hepsilon'
  refine ⟨u, p, (fun t a ha => (hprotect t a ha).2), ?_⟩
  intro a ha
  have h := happrox a ha
  rw [Representation.vectorFunctional_map_apply, hphiVF, hpsiVF] at h
  exact h

set_option maxHeartbeats 800000 in
/-- Endpoint-only compatibility wrapper for
`exists_stageTests_pureState_path_approx`. -/
theorem exists_stageTests_pureState_approx
    (phi : Limit →L[ℂ] ℂ) (hphi : MathlibAnnex.CStarAlgebra.IsPureState Limit phi)
    (F : Finset Limit) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ n, ∃ delta > 0,
      ∀ (psi : Limit →L[ℂ] ℂ), MathlibAnnex.CStarAlgebra.IsPureState Limit psi →
      (∀ i j : Fin (2 ^ n),
        ‖phi (limitMatrixUnit n i j) - psi (limitMatrixUnit n i j)‖ < delta) →
      ∀ (F' : Finset Limit) (epsilon' : ℝ), 0 < epsilon' →
        ∃ u : unitary Limit,
          (∀ a ∈ F,
            ‖star (u : Limit) * a * (u : Limit) - a‖ < epsilon) ∧
          ∀ a ∈ F',
            ‖phi (star (u : Limit) * a * (u : Limit)) - psi a‖ < epsilon' := by
  obtain ⟨n, delta, hdelta, hmain⟩ :=
    exists_stageTests_pureState_path_approx phi hphi F hepsilon
  refine ⟨n, delta, hdelta, ?_⟩
  intro psi hpsi hstate F' epsilon' hepsilon'
  obtain ⟨u, p, hprotect, happrox⟩ :=
    hmain psi hpsi hstate F' epsilon' hepsilon'
  refine ⟨u, ?_, happrox⟩
  intro a ha
  simpa only [p.target] using hprotect (1 : Set.Icc (0 : ℝ) 1) a ha

set_option maxHeartbeats 800000 in
/-- Any pure CAR state can be approximated on a finite set by an inner
translate of any other pure state.  This is the unprotected initialization
step for the alternating intertwining construction. -/
theorem exists_unitary_pureState_path_approx
    (phi psi : Limit →L[ℂ] ℂ)
    (hphi : MathlibAnnex.CStarAlgebra.IsPureState Limit phi) (hpsi : MathlibAnnex.CStarAlgebra.IsPureState Limit psi)
    (F : Finset Limit) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ u : unitary Limit, ∃ p : Path 1 u, ∀ a ∈ F,
      ‖phi (star (u : Limit) * a * (u : Limit)) - psi a‖ < epsilon := by
  have hphiState : phi ∈ stateSpace Limit := extremePoints_subset hphi
  let fphi := positiveLinearMapOfMemStateSpace phi hphiState
  let rho : Representation Limit fphi.GNS := fphi.gnsStarAlgHom
  let xi : fphi.GNS := fphi.gnsCyclicVector
  have hxi : ‖xi‖ = 1 := by
    change ‖stateGNSVector phi hphiState‖ = 1
    exact norm_stateGNSVector phi hphiState
  letI : Nontrivial fphi.GNS := by
    apply nontrivial_of_ne xi 0
    intro hzero
    have hnorm := congrArg norm hzero
    rw [hxi, norm_zero] at hnorm
    norm_num at hnorm
  have hrho : StarAlgHom.IsIrreducible rho := by
    simpa [rho, fphi] using
      isIrreducible_pureState_gnsStarAlgHom phi hphiState hphi
  have hphiVF : Representation.vectorFunctional rho xi = phi := by
    apply ContinuousLinearMap.ext
    intro a
    rw [Representation.vectorFunctional_apply]
    change inner ℂ (stateGNSVector phi hphiState)
      ((positiveLinearMapOfMemStateSpace phi hphiState).gnsStarAlgHom a
        (stateGNSVector phi hphiState)) = phi a
    exact inner_gnsStarAlgHom_stateGNSVector phi hphiState a
  have hpsiState : psi ∈ stateSpace Limit := extremePoints_subset hpsi
  let fpsi := positiveLinearMapOfMemStateSpace psi hpsiState
  let sigma : Representation Limit fpsi.GNS := fpsi.gnsStarAlgHom
  let eta : fpsi.GNS := fpsi.gnsCyclicVector
  have heta : ‖eta‖ = 1 := by
    change ‖stateGNSVector psi hpsiState‖ = 1
    exact norm_stateGNSVector psi hpsiState
  have hpsiVF : Representation.vectorFunctional sigma eta = psi := by
    apply ContinuousLinearMap.ext
    intro a
    rw [Representation.vectorFunctional_apply]
    change inner ℂ (stateGNSVector psi hpsiState)
      ((positiveLinearMapOfMemStateSpace psi hpsiState).gnsStarAlgHom a
        (stateGNSVector psi hpsiState)) = psi a
    exact inner_gnsStarAlgHom_stateGNSVector psi hpsiState a
  obtain ⟨u, p, hu⟩ := exists_unitary_crossRepresentation_path_approx
    rho hrho sigma xi eta hxi heta F hepsilon
  refine ⟨u, p, ?_⟩
  intro a ha
  have h := hu a ha
  rw [Representation.vectorFunctional_map_apply, hphiVF, hpsiVF] at h
  exact h

set_option maxHeartbeats 800000 in
/-- Endpoint-only compatibility wrapper for
`exists_unitary_pureState_path_approx`. -/
theorem exists_unitary_pureState_approx
    (phi psi : Limit →L[ℂ] ℂ)
    (hphi : MathlibAnnex.CStarAlgebra.IsPureState Limit phi) (hpsi : MathlibAnnex.CStarAlgebra.IsPureState Limit psi)
    (F : Finset Limit) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ u : unitary Limit, ∀ a ∈ F,
      ‖phi (star (u : Limit) * a * (u : Limit)) - psi a‖ < epsilon := by
  obtain ⟨u, -, happrox⟩ :=
    exists_unitary_pureState_path_approx phi psi hphi hpsi F hepsilon
  exact ⟨u, happrox⟩

end MathlibAnnex.CStarAlgebra.CAR
