import MathlibAnnex.Analysis.CStarAlgebra.State.VectorApproximation

/-! C05: pure-vector approximation using kernel annihilation alone.
Source proof adapted from State.FiniteFullImage; no finite-dimensional,
full-image, essential-image, or injectivity assumption. UNBUILT. -/

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

local instance kernelVectorWeakDualIsScalarTower :
    IsScalarTower ℝ ℂ (WeakDual ℂ A) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ A))

local instance kernelVectorWeakDualLocallyConvexSpace :
    LocallyConvexSpace ℝ (WeakDual ℂ A) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ A)))

local instance kernelVectorWeakDualContinuousRealSMul :
    ContinuousSMul ℝ (WeakDual ℂ A) :=
  WeakDual.instContinuousSMul ℝ

theorem Representation.mem_convex_closure_unitVectorStates_of_kernel
    [Nontrivial H]
    (pi : Representation A H)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hker : ∀ a : A, pi a = 0 → phi a = 0) :
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
  have hmap : pi d⁺ = (pi d)⁺ := by
    rw [CFC.posPart_def, cfcₙ_eq_cfc, CFC.posPart_def, cfcₙ_eq_cfc]
    exact pi.map_cfc (·⁺ : ℝ → ℝ) d
      (hφ := (Representation.continuousLinearMap pi).continuous)
      (ha := hd) (hφa := hpid)
  have hplus : pi d⁺ = 0 := by
    rw [hmap]
    exact (CFC.posPart_eq_zero_iff (pi d) hpid).mpr hpid_le
  have hphiPlus : phi d⁺ = 0 := hker d⁺ hplus
  let p : A →ₚ[ℂ] ℂ := positiveLinearMapOfMemStateSpace phi hphi
  have hle : p d ≤ p d⁺ := OrderHomClass.mono p (CFC.le_posPart hd)
  have hre : (phi d).re ≤ 0 := by
    have hn := RCLike.nonneg_iff.mp (sub_nonneg.mpr hle)
    simpa [p, hphiPlus] using hn.1
  exact (not_lt_of_ge hre) hphi_d_pos

theorem Representation.mem_closure_unitVectorStates_of_kernel
    [Nontrivial H]
    (pi : Representation A H)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi)
    (hker : ∀ a : A, pi a = 0 → phi a = 0) :
    StrongDual.toWeakDual phi ∈ closure (pi.orthogonalVectorStates ⊥) := by
  exact @mem_closure_of_mem_extremePoints_of_mem_closure_convexHull
    (WeakDual ℂ A) inferInstance (WeakDual.instModule' ℝ) inferInstance
    inferInstance inferInstance kernelVectorWeakDualContinuousRealSMul
    kernelVectorWeakDualLocallyConvexSpace
    (weakStateSpace A) (pi.orthogonalVectorStates ⊥) (StrongDual.toWeakDual phi)
    isCompact_weakStateSpace convex_weakStateSpace
    (pi.orthogonalVectorStates_subset_weakStateSpace ⊥)
    (toWeakDual_mem_extremePoints phi hpure)
    (pi.mem_convex_closure_unitVectorStates_of_kernel phi hphi hker)

theorem Representation.exists_unit_vector_approx_of_kernel
    [Nontrivial H]
    (pi : Representation A H)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi)
    (hker : ∀ a : A, pi a = 0 → phi a = 0)
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
  have hclosure := pi.mem_closure_unitVectorStates_of_kernel phi hphi hpure hker
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


end MathlibAnnex.Analysis.CStarAlgebra
