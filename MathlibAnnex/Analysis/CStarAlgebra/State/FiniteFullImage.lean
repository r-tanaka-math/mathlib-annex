import MathlibAnnex.Analysis.CStarAlgebra.State.VectorApproximation
import MathlibAnnex.Analysis.CStarAlgebra.Representation.FullImage

set_option autoImplicit false
noncomputable section
open Metric Set
open scoped ComplexOrder ComplexStarModule InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

open Representation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem nonpos_of_inner_neg_on_unit
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hneg : ∀ z : H, ‖z‖ = 1 → (inner ℂ z (T z)).re < 0) :
    T ≤ 0 := by
  have hmul : T * T⁺ = T⁺ * T⁺ := by
    calc
      T * T⁺ = (T⁺ - T⁻) * T⁺ :=
        congrArg (fun S : H →L[ℂ] H => S * T⁺) (CFC.posPart_sub_negPart T hT).symm
      _ = T⁺ * T⁺ := by rw [sub_mul, CFC.negPart_mul_posPart, sub_zero]
  have hnonneg {y : H} (hyrange : y ∈ T⁺.range) :
      0 ≤ (inner ℂ y (T y)).re := by
    obtain ⟨x, rfl⟩ := hyrange
    have hTy : T (T⁺ x) = T⁺ (T⁺ x) := by
      simpa only [ContinuousLinearMap.mul_apply] using
        congrArg (fun S : H →L[ℂ] H => S x) hmul
    change 0 ≤ (inner ℂ (T⁺ x) (T (T⁺ x))).re
    rw [hTy]
    simpa using
      (RCLike.nonneg_iff.mp ((CFC.posPart_nonneg T).inner_nonneg_right (T⁺ x))).1
  have hzero {y : H} (hyrange : y ∈ T⁺.range) : y = 0 := by
    by_contra hy0
    have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    let z : H := (‖y‖⁻¹ : ℂ) • y
    have hzunit : ‖z‖ = 1 := by
      simp [z, norm_smul, abs_of_pos hynorm, hynorm.ne']
    have hzrange : z ∈ T⁺.range := T⁺.range.smul_mem (‖y‖⁻¹ : ℂ) hyrange
    exact (not_lt_of_ge (hnonneg hzrange)) (hneg z hzunit)
  have hpluszero : T⁺ = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    exact hzero ⟨x, rfl⟩
  simpa [hpluszero] using CFC.le_posPart hT

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem representation_reflect_nonpos
    (pi : Representation A H) (hinj : Function.Injective pi)
    (hsurj : Function.Surjective pi) (d : A)
    (h : pi d ≤ 0) : d ≤ 0 := by
  let e : A ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
    StarAlgEquiv.ofBijective pi ⟨hinj, hsurj⟩
  have hneg : 0 ≤ e.symm (- pi d) :=
    map_nonneg e.symm (neg_nonneg.mpr h)
  have he : e.symm (pi d) = d := by
    change e.symm (e d) = d
    exact e.symm_apply_apply d
  rw [map_neg, he] at hneg
  exact neg_nonneg.mp hneg

local instance finiteVectorWeakDualIsScalarTower :
    IsScalarTower ℝ ℂ (WeakDual ℂ A) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ A))

local instance finiteVectorWeakDualLocallyConvexSpace :
    LocallyConvexSpace ℝ (WeakDual ℂ A) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ A)))

local instance finiteVectorWeakDualContinuousRealSMul :
    ContinuousSMul ℝ (WeakDual ℂ A) :=
  WeakDual.instContinuousSMul ℝ

private theorem representation_mem_convex_closure_of_full
    [Nontrivial H]
    (pi : Representation A H) (hinj : Function.Injective pi)
    (hsurj : Function.Surjective pi)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) :
    StrongDual.toWeakDual phi ∈
      closure (convexHull ℝ (pi.orthogonalVectorStates ⊥)) := by
  by_contra hmem
  obtain ⟨l, r, hl, hphi_sep⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      (convex_convexHull ℝ _).closure isClosed_closure hmem
  obtain ⟨a, ha⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℂ A) l
  let b : A := (ℜ a : A)
  let d : A := b - r • (1 : A)
  have hb : IsSelfAdjoint b := (ℜ a).2
  have hd : IsSelfAdjoint d :=
    hb.sub ((IsSelfAdjoint.all r).smul (IsSelfAdjoint.one A))
  have hl_eval (omega : WeakDual ℂ A) : l omega = omega a := by
    have := congrArg (fun g : StrongDual ℂ (WeakDual ℂ A) => g omega) ha
    exact this.symm
  have hstate_real (omega : WeakDual ℂ A) (homega : omega ∈ weakStateSpace A) :
      omega b = (omega a).re :=
    state_apply_realPart omega.toStrongDual homega a
  have hneg (z : H) (hzunit : ‖z‖ = 1) :
      (inner ℂ z (pi d z)).re < 0 := by
    let omega : WeakDual ℂ A := StrongDual.toWeakDual (vectorFunctional pi z)
    have homegaV : omega ∈ pi.orthogonalVectorStates ⊥ := by
      refine ⟨z, hzunit, ?_, rfl⟩
      simp
    have homegaState : omega ∈ weakStateSpace A :=
      pi.orthogonalVectorStates_subset_weakStateSpace ⊥ homegaV
    have hsep := hl omega
      (subset_closure (subset_convexHull ℝ _ homegaV))
    rw [hl_eval omega] at hsep
    have hreal : omega b = (omega a).re := hstate_real omega homegaState
    have hdval : omega d = omega b - (r : ℂ) • omega 1 := by
      change omega.toStrongDual d = _
      dsimp [d]
      rw [map_sub, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
      rfl
    change (omega d).re < 0
    rw [hdval, hreal, homegaState.2]
    simpa [Complex.real_smul] using sub_neg.mpr hsep
  have hphi_d_pos : 0 < (phi d).re := by
    rw [hl_eval (StrongDual.toWeakDual phi)] at hphi_sep
    dsimp [d]
    rw [map_sub, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, hphi.2,
      state_apply_realPart phi hphi a]
    simpa [Complex.real_smul] using sub_pos.mpr hphi_sep
  have hpid : IsSelfAdjoint (pi d) := by
    rw [isSelfAdjoint_iff, ← map_star, hd.star_eq]
  have hpid_le : pi d ≤ 0 := nonpos_of_inner_neg_on_unit (pi d) hpid hneg
  have hd_le : d ≤ 0 := representation_reflect_nonpos pi hinj hsurj d hpid_le
  let p : A →ₚ[ℂ] ℂ := positiveLinearMapOfMemStateSpace phi hphi
  have hle : p d ≤ p 0 := OrderHomClass.mono p hd_le
  have hre : (phi d).re ≤ 0 := by
    have hn := RCLike.nonneg_iff.mp (sub_nonneg.mpr hle)
    simpa [p] using hn.1
  exact (not_lt_of_ge hre) hphi_d_pos

private theorem representation_mem_closure_unitVectorStates_of_full
    [Nontrivial H]
    (pi : Representation A H) (hinj : Function.Injective pi)
    (hsurj : Function.Surjective pi)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi) :
    StrongDual.toWeakDual phi ∈ closure (pi.orthogonalVectorStates ⊥) := by
  exact @mem_closure_of_mem_extremePoints_of_mem_closure_convexHull
    (WeakDual ℂ A) inferInstance (WeakDual.instModule' ℝ) inferInstance
    inferInstance inferInstance finiteVectorWeakDualContinuousRealSMul
    finiteVectorWeakDualLocallyConvexSpace
    (weakStateSpace A) (pi.orthogonalVectorStates ⊥) (StrongDual.toWeakDual phi)
    isCompact_weakStateSpace convex_weakStateSpace
    (pi.orthogonalVectorStates_subset_weakStateSpace ⊥)
    (toWeakDual_mem_extremePoints phi hpure)
    (representation_mem_convex_closure_of_full pi hinj hsurj phi hphi)

private theorem representation_exists_unit_vector_approx_of_full
    [Nontrivial H]
    (pi : Representation A H) (hinj : Function.Injective pi)
    (hsurj : Function.Surjective pi)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi)
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z : H, ‖z‖ = 1 ∧
      ∀ a ∈ F, ‖phi a - inner ℂ z (pi a z)‖ < epsilon := by
  let U : Set (WeakDual ℂ A) :=
    ⋂ a ∈ F, (fun omega : WeakDual ℂ A => omega a) ⁻¹' ball (phi a) epsilon
  have hUopen : IsOpen U :=
    isOpen_biInter_finset fun a ha =>
      isOpen_ball.preimage (WeakDual.eval_continuous a)
  have hphiU : StrongDual.toWeakDual phi ∈ U := by
    apply mem_iInter₂.mpr
    intro a ha
    change StrongDual.toWeakDual phi a ∈ ball (phi a) epsilon
    simpa using (Metric.mem_ball_self (x := phi a) hepsilon)
  have hclosure := representation_mem_closure_unitVectorStates_of_full
    pi hinj hsurj phi hphi hpure
  obtain ⟨omega, homegaU, homega⟩ :=
    mem_closure_iff.mp hclosure U hUopen hphiU
  obtain ⟨z, hzunit, _hzorth, rfl⟩ := homega
  refine ⟨z, hzunit, ?_⟩
  intro a ha
  have hball : StrongDual.toWeakDual (vectorFunctional pi z) a ∈
      ball (phi a) epsilon :=
    mem_iInter₂.mp homegaU a ha
  rw [mem_ball, dist_comm, dist_eq_norm] at hball
  simpa only [StrongDual.toWeakDual_apply, vectorFunctional_apply] using hball

theorem representation_exists_exact_unit_vector_of_full_finite
    [Nontrivial H] [FiniteDimensional ℂ H]
    (pi : Representation A H) (hinj : Function.Injective pi)
    (hsurj : Function.Surjective pi)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi) :
    ∃ z : H, ‖z‖ = 1 ∧
      ∀ a : A, phi a = inner ℂ z (pi a z) := by
  let f : H → WeakDual ℂ A := fun z =>
    StrongDual.toWeakDual (vectorFunctional pi z)
  have hf : Continuous f := by
    apply WeakBilin.continuous_of_continuous_eval
    intro a
    change Continuous (fun z : H => inner ℂ z (pi a z))
    exact continuous_id.inner ((pi a).continuous.comp continuous_id)
  have hcompact : IsCompact (sphere (0 : H) 1) := isCompact_sphere 0 1
  have hclosed : IsClosed (f '' sphere (0 : H) 1) :=
    (hcompact.image hf).isClosed
  have hset : pi.orthogonalVectorStates ⊥ = f '' sphere (0 : H) 1 := by
    ext omega
    constructor
    · rintro ⟨z, hz, _hzorth, rfl⟩
      exact ⟨z, by simpa using hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, by simpa using hz, by simp, rfl⟩
  have hcl := representation_mem_closure_unitVectorStates_of_full
    pi hinj hsurj phi hphi hpure
  rw [hset, hclosed.closure_eq] at hcl
  obtain ⟨z, hz, heq⟩ := hcl
  refine ⟨z, by simpa using hz, ?_⟩
  intro a
  have h := congrArg (fun omega : WeakDual ℂ A => omega a) heq
  simpa [f, vectorFunctional_apply] using h.symm

end MathlibAnnex.Analysis.CStarAlgebra

