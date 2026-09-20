import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.SameKernelFamily
import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.FiniteAverageAssembly
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.KernelGlobalState
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.ApproximateRankOnePath

/-!
# Same-kernel KOS assembly without simplicity

C05 source, UNBUILT. Compact and essential cases are split separately for
EACH current GNS representation. No claim that a primitive quotient is
simple, no classification of compact-image representations, and no
preservation of essentiality by changing the state is needed.
The only outstanding analytic existence input is the explicitly named
finite-central-average supplier assigned to source-author A.
-/
set_option autoImplicit false
noncomputable section
open scoped InnerProduct ComplexOrder
namespace MathlibAnnex.CStarAlgebra
open MathlibAnnex.CStarAlgebra MathlibAnnex.Analysis.CStarAlgebra
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem sameKernel_gns_path_approx
    (phi psi : A →L[ℂ] ℂ) (hphi : IsPureState A phi) (hpsi : IsPureState A psi)
    (hker : stateGNSKernel phi = stateGNSKernel psi)
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ u : unitary A, ∃ p : Path 1 u,
      ∀ a ∈ F, ‖pull phi u a - psi a‖ < epsilon := by
  let f := positiveLinearMapOfMemStateSpace phi hphi.1
  let pi : Representation A f.GNS := f.gnsStarAlgHom
  let xi : f.GNS := stateGNSVector phi hphi.1
  have hxi : ‖xi‖ = 1 := norm_stateGNSVector phi hphi.1
  have hxi0 : xi ≠ 0 := by intro hz; simp [hz] at hxi
  letI : Nontrivial f.GNS := nontrivial_of_ne xi 0 hxi0
  have hirr : StarAlgHom.IsIrreducible pi :=
    isIrreducible_pureState_gnsStarAlgHom phi hphi.1 hphi
  have hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi) :=
    fun a => (inner_gnsStarAlgHom_stateGNSVector phi hphi.1 a).symm
  exact pi.exists_path_state_approx_of_kernel hirr phi xi hxi hcoeff
    psi hpsi.1 hpsi
    (annihilates_gnsKernel_of_stateGNSKernel_eq phi psi hphi.1 hpsi.1 hker)
    F hepsilon

/-- The uniform protected field is valid on a fixed kernel fibre. Tests and
radius are fixed BEFORE psi, and psi is fixed BEFORE the later T,eta. -/
theorem sameKernel_gns_protected_of_rowSupplier
    (hrow : PureGNSProtectedRowSupplier A)
    (phi : A →L[ℂ] ℂ) (hphi : IsPureState A phi)
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ G : Finset A, ∃ delta : ℝ, 0 < delta ∧
      ∀ psi : A →L[ℂ] ℂ, IsPureState A psi →
        stateGNSKernel phi = stateGNSKernel psi →
        (∀ a ∈ G, ‖phi a - psi a‖ < delta) →
        ∀ T : Finset A, ∀ eta : ℝ, 0 < eta →
          ∃ u : unitary A, ∃ p : Path 1 u,
            PathCentralOn p F epsilon ∧
              ∀ a ∈ T, ‖pull phi u a - psi a‖ < eta := by
  classical
  let f := positiveLinearMapOfMemStateSpace phi hphi.1
  let pi : Representation A f.GNS := f.gnsStarAlgHom
  let xi : f.GNS := stateGNSVector phi hphi.1
  have hxi : ‖xi‖ = 1 := norm_stateGNSVector phi hphi.1
  have hxi0 : xi ≠ 0 := by intro hz; simp [hz] at hxi
  letI : Nontrivial f.GNS := nontrivial_of_ne xi 0 hxi0
  have hirr : StarAlgHom.IsIrreducible pi :=
    isIrreducible_pureState_gnsStarAlgHom phi hphi.1 hphi
  have hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi) :=
    fun a => (inner_gnsStarAlgHom_stateGNSVector phi hphi.1 a).symm
  have hkerphi : ∀ a : A, pi a = 0 → phi a = 0 :=
    fun _ ha => state_eq_zero_of_gnsStarAlgHom_eq_zero phi hphi.1 ha
  by_cases hno : pi.HasNoNonzeroCompactImage
  · obtain ⟨n, x, hq, hfix, hprotect⟩ := hrow phi hphi F epsilon hepsilon
    obtain ⟨G, delta, hdelta, hlocal⟩ :=
      pi.exists_protected_state_transport_of_row hirr hno phi hphi.1 hphi
        hkerphi xi hxi hcoeff F hepsilon x hq hfix hprotect
    refine ⟨G, delta, hdelta, ?_⟩
    intro psi hpsi hker hclose T eta heta
    exact hlocal psi hpsi.1 hpsi
      (annihilates_gnsKernel_of_stateGNSKernel_eq phi psi hphi.1 hpsi.1 hker)
      hclose T eta heta
  · change ¬ (∀ a : A, IsCompactOperator (pi a) → pi a = 0) at hno
    push_neg at hno
    obtain ⟨k, hk, hk0⟩ := hno
    obtain ⟨G, delta, hdelta, hlocal⟩ :=
      pi.exists_protected_state_transport_of_compact_image hirr k hk hk0
        phi xi hxi hcoeff F hepsilon
    refine ⟨G, delta, hdelta, ?_⟩
    intro psi hpsi hker hclose T eta heta
    exact hlocal psi hpsi.1 hpsi
      (annihilates_gnsKernel_of_stateGNSKernel_eq phi psi hphi.1 hpsi.1 hker)
      hclose T eta heta

/-- All four fields; no simplicity or dimension assumption on A. -/
theorem finitePathTransport_sameKernelPure_of_rowSupplier
    (hrow : PureGNSProtectedRowSupplier A) (I : Set A) :
    FinitePathTransport (sameKernelPureStates I) where
  toInnerInvariantFamily := innerInvariantFamily_sameKernelPure I
  approximate := by
    intro phi hphi psi hpsi F epsilon hepsilon
    exact sameKernel_gns_path_approx phi psi hphi.1 hpsi.1
      (sameKernelPure_kernel_eq phi psi hphi hpsi) F hepsilon
  protected_approximate := by
    intro phi hphi F epsilon hepsilon
    obtain ⟨G, delta, hdelta, hlocal⟩ :=
      sameKernel_gns_protected_of_rowSupplier hrow phi hphi.1 F hepsilon
    refine ⟨G, delta, hdelta, ?_⟩
    intro psi hpsi hclose T eta heta
    exact hlocal psi hpsi.1 (sameKernelPure_kernel_eq phi psi hphi hpsi)
      hclose T eta heta

/-- The same alpha satisfies the exact equation and the start-at-one path
condition. The explicit finite-average premise is NOT discharged here. -/
theorem sameKernel_exists_asymptoticallyInner_of_representationAverages
    [TopologicalSpace.SeparableSpace A] (havg : HasRepresentationAverages A)
    (phi psi : A →L[ℂ] ℂ) (hphi : IsPureState A phi) (hpsi : IsPureState A psi)
    (hker : stateGNSKernel phi = stateGNSKernel psi) :
    ∃ alpha : A ≃⋆ₐ[ℂ] A,
      IsAsymptoticallyInnerFromOne alpha ∧ ∀ a : A, phi (alpha a) = psi a := by
  let I := stateGNSKernel phi
  have ht := finitePathTransport_sameKernelPure_of_rowSupplier
    (pureGNSRowSupplier_of_representationAverages A havg) I
  exact ht.exists_asymptoticallyInner phi ⟨hphi, rfl⟩ psi ⟨hpsi, hker.symm⟩

/-- Equivalent endpoint expressed with the actual two GNS representations. -/
theorem gnsKernel_exists_asymptoticallyInner_of_representationAverages
    [TopologicalSpace.SeparableSpace A] (havg : HasRepresentationAverages A)
    (phi psi : A →L[ℂ] ℂ) (hphi : IsPureState A phi) (hpsi : IsPureState A psi)
    (hker : ∀ a : A,
      (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom a = 0 ↔
      (positiveLinearMapOfMemStateSpace psi hpsi.1).gnsStarAlgHom a = 0) :
    ∃ alpha : A ≃⋆ₐ[ℂ] A,
      IsAsymptoticallyInnerFromOne alpha ∧ ∀ a : A, phi (alpha a) = psi a := by
  exact sameKernel_exists_asymptoticallyInner_of_representationAverages havg
    phi psi hphi hpsi ((stateGNSKernel_eq_iff phi psi hphi.1 hpsi.1).2 hker)

end MathlibAnnex.CStarAlgebra
