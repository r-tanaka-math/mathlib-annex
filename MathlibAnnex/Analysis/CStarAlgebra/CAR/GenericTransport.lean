import MathlibAnnex.Analysis.CStarAlgebra.LocalPathTransport
import MathlibAnnex.Analysis.CStarAlgebra.CAR.Homogeneity
import MathlibAnnex.Analysis.CStarAlgebra.CAR.StateTransport

/-!
# CAR specialization of generic finite path transport

The generic local-to-global theorem is instantiated here from the existing
CAR cross-representation suppliers.  The family consists exactly of the two
inner orbits of the input vector functionals, so no global orbit hypothesis
is smuggled into the generic theorem.
-/

set_option autoImplicit false

noncomputable section

open Filter MathlibAnnex.Analysis.CStarAlgebra MathlibAnnex.CStarAlgebra

namespace MathlibAnnex.CStarAlgebra.CAR

universe uX uY uH uK

variable {H : Type uH} {K : Type uK}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K]

/-- The disjoint union of two inner vector-functional orbits. -/
noncomputable def pairOrbitFunctional
    (rho : Representation Limit H) (sigma : Representation Limit K)
    (xi : H) (eta : K) : Sum (unitary Limit) (unitary Limit) →
      Limit →L[ℂ] ℂ
  | .inl u => Representation.vectorFunctional rho (rho (u : Limit) xi)
  | .inr u => Representation.vectorFunctional sigma (sigma (u : Limit) eta)

noncomputable def pairOrbitFamily
    (rho : Representation Limit H) (sigma : Representation Limit K)
    (xi : H) (eta : K) : Set (Limit →L[ℂ] ℂ) :=
  Set.range (pairOrbitFunctional rho sigma xi eta)

theorem norm_rep_unitary
    (pi : Representation Limit H) (u : unitary Limit) (x : H)
    (hx : ‖x‖ = 1) : ‖pi (u : Limit) x‖ = 1 := by
  rw [(pi (u : Limit)).norm_map_of_mem_unitary
    (Unitary.map_mem pi u.property), hx]

theorem pull_vectorFunctional_unitary
    (pi : Representation Limit H) (x : H) (u v : unitary Limit) :
    pull (Representation.vectorFunctional pi (pi (u : Limit) x)) v =
      Representation.vectorFunctional pi (pi ((v * u : unitary Limit) : Limit) x) := by
  apply ContinuousLinearMap.ext
  intro a
  calc
    pull (Representation.vectorFunctional pi (pi (u : Limit) x)) v a =
        Representation.vectorFunctional pi (pi (u : Limit) x)
          (star (v : Limit) * a * (v : Limit)) := by
      simp [pull_apply, innerAt]
    _ = Representation.vectorFunctional pi (pi (v : Limit) (pi (u : Limit) x)) a :=
      (Representation.vectorFunctional_map_apply pi (pi (u : Limit) x)
        (v : Limit) a).symm
    _ = Representation.vectorFunctional pi
        (pi ((v * u : unitary Limit) : Limit) x) a := by
      congr 2
      change pi (v : Limit) (pi (u : Limit) x) =
        pi ((v : Limit) * (u : Limit)) x
      rw [map_mul, mul_apply_eq_comp]

theorem pairOrbitFamily_pull_mem
    (rho : Representation Limit H) (sigma : Representation Limit K)
    (xi : H) (eta : K) {phi : Limit →L[ℂ] ℂ}
    (hphi : phi ∈ pairOrbitFamily rho sigma xi eta) (v : unitary Limit) :
    pull phi v ∈ pairOrbitFamily rho sigma xi eta := by
  obtain ⟨u, rfl⟩ := hphi
  cases u with
  | inl u =>
      refine ⟨Sum.inl (v * u), ?_⟩
      dsimp only [pairOrbitFunctional]
      exact (pull_vectorFunctional_unitary rho xi u v).symm
  | inr u =>
      refine ⟨Sum.inr (v * u), ?_⟩
      dsimp only [pairOrbitFunctional]
      exact (pull_vectorFunctional_unitary sigma eta u v).symm

set_option maxHeartbeats 800000 in
theorem pairOrbitFamily_norm_le_one
    (rho : Representation Limit H) (sigma : Representation Limit K)
    (xi : H) (eta : K) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1)
    {phi : Limit →L[ℂ] ℂ} (hphi : phi ∈ pairOrbitFamily rho sigma xi eta) :
    ‖phi‖ ≤ 1 := by
  obtain ⟨u, rfl⟩ := hphi
  cases u with
  | inl u =>
      dsimp only [pairOrbitFunctional]
      apply ContinuousLinearMap.opNorm_le_bound
        (f := Representation.vectorFunctional rho (rho (u : Limit) xi))
        (M := 1) (by norm_num)
      intro a
      simpa only [one_mul] using Representation.norm_vectorFunctional_apply_le rho
        (norm_rep_unitary rho u xi hxi) a
  | inr u =>
      dsimp only [pairOrbitFunctional]
      apply ContinuousLinearMap.opNorm_le_bound
        (f := Representation.vectorFunctional sigma (sigma (u : Limit) eta))
        (M := 1) (by norm_num)
      intro a
      simpa only [one_mul] using Representation.norm_vectorFunctional_apply_le sigma
        (norm_rep_unitary sigma u eta heta) a

set_option maxHeartbeats 800000 in
theorem exists_orbit_path_approx
    {X : Type uX} {Y : Type uY}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [Nontrivial X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    [Nontrivial Y]
    (pi : Representation Limit X) (hpi : StarAlgHom.IsIrreducible pi)
    (tau : Representation Limit Y) (x : X) (y : Y)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (F : Finset Limit) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ u : unitary Limit, ∃ p : Path 1 u,
      ∀ a ∈ F, ‖pull (Representation.vectorFunctional pi x) u a -
        Representation.vectorFunctional tau y a‖ < epsilon := by
  obtain ⟨u, p, happrox⟩ := exists_unitary_crossRepresentation_path_approx
    pi hpi tau x y hx hy F hepsilon
  refine ⟨u, p, ?_⟩
  intro a ha
  have hh := happrox a ha
  have hpull :
      pull (Representation.vectorFunctional pi x) u a =
        Representation.vectorFunctional pi (pi (u : Limit) x) a := by
    calc
      _ = Representation.vectorFunctional pi x
          (star (u : Limit) * a * (u : Limit)) := by
        simp [pull_apply, innerAt]
      _ = _ := (Representation.vectorFunctional_map_apply
        pi x (u : Limit) a).symm
  rw [hpull]
  exact hh

noncomputable def orbitStageTests (n : ℕ) : Finset Limit := by
  classical
  exact (Finset.univ.product Finset.univ).image
    (fun ij : Fin (2 ^ n) × Fin (2 ^ n) => limitMatrixUnit n ij.1 ij.2)

theorem mem_orbitStageTests (n : ℕ) (i j : Fin (2 ^ n)) :
    limitMatrixUnit n i j ∈ orbitStageTests n := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨(i, j), Finset.mem_product.mpr
    ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩

set_option maxHeartbeats 1200000 in
theorem exists_orbit_protected_path_approx
    {X : Type uX}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [Nontrivial X]
    (pi : Representation Limit X) (hpi : StarAlgHom.IsIrreducible pi)
    (x : X) (hx : ‖x‖ = 1)
    (F : Finset Limit) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ G : Finset Limit, ∃ delta : ℝ, 0 < delta ∧
      ∀ {Y : Type uY}
        [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
        [Nontrivial Y]
        (tau : Representation Limit Y) (y : Y), ‖y‖ = 1 →
        (∀ a ∈ G, ‖Representation.vectorFunctional pi x a -
          Representation.vectorFunctional tau y a‖ < delta) →
        ∀ H' : Finset Limit, ∀ eta' : ℝ, 0 < eta' →
          ∃ u : unitary Limit, ∃ p : Path 1 u,
            PathCentralOn p F epsilon ∧
              ∀ a ∈ H', ‖pull (Representation.vectorFunctional pi x) u a -
                Representation.vectorFunctional tau y a‖ < eta' := by
  obtain ⟨n, delta, hdelta, hmain⟩ :=
    @exists_stageTests_crossRepresentation_path_approx.{uX, uY} X
      _ _ _ _ pi hpi F epsilon hepsilon
  refine ⟨orbitStageTests n, delta, hdelta, ?_⟩
  intro Y _ _ _ _ tau y hy hclose H' eta' heta'
  have hmatrix : ∀ i j : Fin (2 ^ n),
      ‖Representation.vectorFunctional pi x (limitMatrixUnit n i j) -
        Representation.vectorFunctional tau y (limitMatrixUnit n i j)‖ < delta := by
    intro i j
    exact hclose _ (mem_orbitStageTests n i j)
  obtain ⟨u, p, hcentral, happrox⟩ :=
    hmain tau x y hx hy hmatrix H' eta' heta'
  refine ⟨u, p, hcentral, ?_⟩
  intro a ha
  have hh := happrox a ha
  have hpull :
      pull (Representation.vectorFunctional pi x) u a =
        Representation.vectorFunctional pi (pi (u : Limit) x) a := by
    calc
      _ = Representation.vectorFunctional pi x
          (star (u : Limit) * a * (u : Limit)) := by
        simp [pull_apply, innerAt]
      _ = _ := (Representation.vectorFunctional_map_apply
        pi x (u : Limit) a).symm
  rw [hpull]
  exact hh

set_option maxHeartbeats 1600000 in
theorem finitePathTransport_pairOrbit
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (sigma : Representation Limit K) (hsigma : StarAlgHom.IsIrreducible sigma)
    (xi : H) (eta : K) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1) :
    FinitePathTransport (pairOrbitFamily rho sigma xi eta) := by
  classical
  let S := pairOrbitFamily rho sigma xi eta
  refine {
    norm_le_one := fun phi hphi =>
      pairOrbitFamily_norm_le_one rho sigma xi eta hxi heta hphi
    pull_mem := fun phi hphi u =>
      pairOrbitFamily_pull_mem rho sigma xi eta hphi u
    approximate := ?_
    protected_approximate := ?_ }
  · intro phi hphi psi hpsi F epsilon hepsilon
    obtain ⟨s, rfl⟩ := hphi
    obtain ⟨t, rfl⟩ := hpsi
    cases s with
    | inl u =>
        cases t with
        | inl v =>
            exact exists_orbit_path_approx rho hrho rho
              (rho (u : Limit) xi) (rho (v : Limit) xi)
              (norm_rep_unitary rho u xi hxi) (norm_rep_unitary rho v xi hxi)
              F hepsilon
        | inr v =>
            exact exists_orbit_path_approx rho hrho sigma
              (rho (u : Limit) xi) (sigma (v : Limit) eta)
              (norm_rep_unitary rho u xi hxi) (norm_rep_unitary sigma v eta heta)
              F hepsilon
    | inr u =>
        cases t with
        | inl v =>
            exact exists_orbit_path_approx sigma hsigma rho
              (sigma (u : Limit) eta) (rho (v : Limit) xi)
              (norm_rep_unitary sigma u eta heta) (norm_rep_unitary rho v xi hxi)
              F hepsilon
        | inr v =>
            exact exists_orbit_path_approx sigma hsigma sigma
              (sigma (u : Limit) eta) (sigma (v : Limit) eta)
              (norm_rep_unitary sigma u eta heta) (norm_rep_unitary sigma v eta heta)
              F hepsilon
  · intro phi hphi F epsilon hepsilon
    obtain ⟨s, rfl⟩ := hphi
    cases s with
    | inl u =>
        obtain ⟨GH, dH, hdH, hmainH⟩ :=
          exists_orbit_protected_path_approx.{uH, uH}
            rho hrho (rho (u : Limit) xi)
            (norm_rep_unitary rho u xi hxi) F hepsilon
        obtain ⟨GK, dK, hdK, hmainK⟩ :=
          exists_orbit_protected_path_approx.{uH, uK}
            rho hrho (rho (u : Limit) xi)
            (norm_rep_unitary rho u xi hxi) F hepsilon
        refine ⟨GH ∪ GK, min dH dK, lt_min hdH hdK, ?_⟩
        intro psi hpsi hclose H' eta' heta'
        obtain ⟨t, rfl⟩ := hpsi
        cases t with
        | inl v =>
            dsimp only [pairOrbitFunctional] at hclose ⊢
            apply hmainH rho (rho (v : Limit) xi)
              (norm_rep_unitary rho v xi hxi) _ H' eta' heta'
            intro a ha
            exact lt_of_lt_of_le (hclose a (Finset.mem_union_left _ ha))
              (min_le_left _ _)
        | inr v =>
            dsimp only [pairOrbitFunctional] at hclose ⊢
            apply hmainK sigma (sigma (v : Limit) eta)
              (norm_rep_unitary sigma v eta heta) _ H' eta' heta'
            intro a ha
            exact lt_of_lt_of_le (hclose a (Finset.mem_union_right _ ha))
              (min_le_right _ _)
    | inr u =>
        obtain ⟨GH, dH, hdH, hmainH⟩ :=
          exists_orbit_protected_path_approx.{uK, uH}
            sigma hsigma (sigma (u : Limit) eta)
            (norm_rep_unitary sigma u eta heta) F hepsilon
        obtain ⟨GK, dK, hdK, hmainK⟩ :=
          exists_orbit_protected_path_approx.{uK, uK}
            sigma hsigma (sigma (u : Limit) eta)
            (norm_rep_unitary sigma u eta heta) F hepsilon
        refine ⟨GH ∪ GK, min dH dK, lt_min hdH hdK, ?_⟩
        intro psi hpsi hclose H' eta' heta'
        obtain ⟨t, rfl⟩ := hpsi
        cases t with
        | inl v =>
            dsimp only [pairOrbitFunctional] at hclose ⊢
            apply hmainH rho (rho (v : Limit) xi)
              (norm_rep_unitary rho v xi hxi) _ H' eta' heta'
            intro a ha
            exact lt_of_lt_of_le (hclose a (Finset.mem_union_left _ ha))
              (min_le_left _ _)
        | inr v =>
            dsimp only [pairOrbitFunctional] at hclose ⊢
            apply hmainK sigma (sigma (v : Limit) eta)
              (norm_rep_unitary sigma v eta heta) _ H' eta' heta'
            intro a ha
            exact lt_of_lt_of_le (hclose a (Finset.mem_union_right _ ha))
              (min_le_right _ _)

set_option maxHeartbeats 1600000 in
theorem asymptoticallyInner_vectorFunctional_from_finitePath
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (sigma : Representation Limit K) (hsigma : StarAlgHom.IsIrreducible sigma)
    (xi : H) (eta : K) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1) :
    ∃ alpha : StarAlgEquiv ℂ Limit Limit,
      IsAsymptoticallyInnerFromOne alpha ∧
        ∀ a, Representation.vectorFunctional rho xi (alpha a) =
          Representation.vectorFunctional sigma eta a := by
  let transport := finitePathTransport_pairOrbit
    rho hrho sigma hsigma xi eta hxi heta
  have hleft : Representation.vectorFunctional rho xi ∈
      pairOrbitFamily rho sigma xi eta := by
    refine ⟨Sum.inl 1, ?_⟩
    simp [pairOrbitFunctional]
  have hright : Representation.vectorFunctional sigma eta ∈
      pairOrbitFamily rho sigma xi eta := by
    refine ⟨Sum.inr 1, ?_⟩
    simp [pairOrbitFunctional]
  exact transport.exists_asymptoticallyInner
    (Representation.vectorFunctional rho xi) hleft
    (Representation.vectorFunctional sigma eta) hright

set_option maxHeartbeats 1600000 in
/-- Actual CAR specialization of the generic local-to-global theorem.  The
finite protected suppliers are built above from the CAR local path theorem;
the previously completed CAR global homogeneity theorem is not used. -/
theorem asymptoticallyInnerHomogeneity_from_finitePath :
    AsymptoticallyInnerPureStateHomogeneity := by
  intro phi psi hphi hpsi
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
  letI : Nontrivial fpsi.GNS := by
    apply nontrivial_of_ne eta 0
    intro hzero
    have hnorm := congrArg norm hzero
    rw [heta, norm_zero] at hnorm
    norm_num at hnorm
  have hsigma : StarAlgHom.IsIrreducible sigma := by
    simpa [sigma, fpsi] using
      isIrreducible_pureState_gnsStarAlgHom psi hpsiState hpsi
  have hpsiVF : Representation.vectorFunctional sigma eta = psi := by
    apply ContinuousLinearMap.ext
    intro a
    rw [Representation.vectorFunctional_apply]
    change inner ℂ (stateGNSVector psi hpsiState)
      ((positiveLinearMapOfMemStateSpace psi hpsiState).gnsStarAlgHom a
        (stateGNSVector psi hpsiState)) = psi a
    exact inner_gnsStarAlgHom_stateGNSVector psi hpsiState a
  obtain ⟨alpha, hAInn, hstate⟩ :=
    asymptoticallyInner_vectorFunctional_from_finitePath
      rho hrho sigma hsigma xi eta hxi heta
  obtain ⟨U, hU, hU0, hforward⟩ := hAInn
  refine ⟨alpha, U, hU, hU0, ?_, hforward, ?_⟩
  · intro a
    rw [← hphiVF, ← hpsiVF]
    exact hstate a
  · exact tendsto_symm_apply_atTop_of_tendsto
      (fun t => Unitary.conjStarAlgAut ℂ Limit (U t)) alpha hforward

end MathlibAnnex.CStarAlgebra.CAR
