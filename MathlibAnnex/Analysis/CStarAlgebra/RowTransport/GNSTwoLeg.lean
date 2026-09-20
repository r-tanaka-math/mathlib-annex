import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.GramAssistedTwoLeg
import MathlibAnnex.Analysis.CStarAlgebra.State.Irreducible

set_option autoImplicit false
noncomputable section
namespace MathlibAnnex.Analysis.CStarAlgebra


variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem pure_gns_source_data
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi) :
    let pi := (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom
    let ξ := stateGNSVector phi hphi
    StarAlgHom.IsIrreducible pi ∧
    ‖ξ‖ = 1 ∧
    (∀ a : A, phi a = inner ℂ ξ (pi a ξ)) ∧
    (∀ a : A, pi a = 0 → phi a = 0) := by
  dsimp
  refine ⟨isIrreducible_pureState_gnsStarAlgHom phi hphi hpure,
    norm_stateGNSVector phi hphi, ?_, ?_⟩
  · intro a
    exact (inner_gnsStarAlgHom_stateGNSVector phi hphi a).symm
  · intro a ha
    exact state_eq_zero_of_gnsStarAlgHom_eq_zero phi hphi ha

theorem pure_gns_g_assisted_two_leg_local_path_finite
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi)
    (hno : Representation.HasNoNonzeroCompactImage
      (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom)
    (F : Finset A) {ε : ℝ} (hε : 0 < ε)
    {n : ℕ} (x : Fin n → A)
    (hq : ‖MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x‖ ≤ 1)
    (hqξ : ((positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom
      (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x))
      (stateGNSVector phi hphi) = stateGNSVector phi hphi)
    (hprotect : ∀ a ∈ F, ∀ h : A,
      ‖a * MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h -
        MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h * a‖ ≤
        (ε / (8 * Real.pi)) * ‖h‖) :
    let f := positiveLinearMapOfMemStateSpace phi hphi
    let pi := f.gnsStarAlgHom
    let ξ := stateGNSVector phi hphi
    ∃ μ : ℝ, 0 < μ ∧
      ∀ η : f.GNS, ‖η‖ = 1 →
        (∀ i j : Fin n,
          ‖phi (x i * star (x j)) -
            inner ℂ η (pi (x i * star (x j)) η)‖ < μ) →
        ‖phi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) -
          inner ℂ η (pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) η)‖ < μ →
        ∃ u : unitary A, ∃ p : Path 1 u,
          pi (u : A) ξ = η ∧
          ∀ t : Set.Icc (0 : ℝ) 1, ∀ a ∈ F,
            ‖(p t : A) * a * star (p t : A) - a‖ ≤ ε ∧
            ‖star (p t : A) * a * (p t : A) - a‖ ≤ ε := by
  dsimp
  let f := positiveLinearMapOfMemStateSpace phi hphi
  let pi := f.gnsStarAlgHom
  let ξ := stateGNSVector phi hphi
  obtain ⟨hirred, hξ, hcoeff, hker⟩ := pure_gns_source_data phi hphi hpure
  have hξne : ξ ≠ 0 := by
    intro hz
    change ‖ξ‖ = 1 at hξ
    rw [hz, norm_zero] at hξ
    norm_num at hξ
  letI : Nontrivial f.GNS := ⟨ξ, 0, hξne⟩
  exact Representation.exists_g_assisted_two_leg_local_path_finite pi
    hirred hno phi hphi hpure hker ξ hξ hcoeff F hε x hq hqξ hprotect

end MathlibAnnex.Analysis.CStarAlgebra
