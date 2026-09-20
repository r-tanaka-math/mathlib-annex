import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import MathlibAnnex.Analysis.CStarAlgebra.PureState
import MathlibAnnex.Analysis.CStarAlgebra.State.Purity
import MathlibAnnex.Analysis.Convex.Milman

/-!
# Finite-test approximation of pure states by vector states

The main result starts from an essential Hilbert-space representation and a
state which vanishes on its kernel.  It first proves weak-star convex density
of unit vector states outside a prescribed finite-dimensional subspace.  For
pure states, Milman's converse then replaces a convex combination by one unit
vector for all of a given finite family of tests.
-/

set_option autoImplicit false

open Metric Set
open scoped ComplexOrder ComplexStarModule Convex InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance vectorApproximationWeakDualIsScalarTower :
    IsScalarTower ℝ ℂ (WeakDual ℂ A) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ A))

local instance vectorApproximationWeakDualLocallyConvexSpace :
    LocallyConvexSpace ℝ (WeakDual ℂ A) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ A)))

local instance vectorApproximationWeakDualContinuousRealSMul :
    ContinuousSMul ℝ (WeakDual ℂ A) :=
  WeakDual.instContinuousSMul ℝ

/-- A state, evaluated on the adjoint of an element. -/
theorem state_apply_star (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) (a : A) :
    phi (star a) = star (phi a) := by
  let p : A →ₚ[ℂ] ℂ := positiveLinearMapOfMemStateSpace phi hphi
  exact map_star p a

/-- Evaluation of a state on the self-adjoint real part. -/
theorem state_apply_realPart (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) (a : A) :
    phi (ℜ a : A) = (phi a).re := by
  rw [realPart_apply_coe, ContinuousLinearMap.map_smul_of_tower, map_add,
    state_apply_star phi hphi]
  apply Complex.ext <;> simp <;> ring

/-- The weak-star state space is convex. -/
theorem convex_weakStateSpace : Convex ℝ (weakStateSpace A) := by
  intro phi hphi psi hpsi s t hs ht hst
  constructor
  · intro a ha
    change 0 ≤ s • phi a + t • psi a
    exact add_nonneg (smul_nonneg hs (hphi.1 a ha)) (smul_nonneg ht (hpsi.1 a ha))
  · change s • phi 1 + t • psi 1 = 1
    rw [hphi.2, hpsi.2, ← add_smul, hst, one_smul]

/-- The weak-star state space is compact, with no separability assumption. -/
theorem isCompact_weakStateSpace : IsCompact (weakStateSpace A) :=
  (WeakDual.isCompact_closedBall (𝕜 := ℂ) (E := A) 0 1).of_isClosed_subset
    isClosed_weakStateSpace fun phi hphi => by
      simpa only [mem_preimage, mem_closedBall_zero_iff] using
        norm_le_one_of_mem_weakStateSpace hphi

namespace Representation

/-- Weak-star vector states carried by unit vectors in the orthogonal
complement of `K`. -/
def orthogonalVectorStates (pi : Representation A H) (K : Submodule ℂ H) :
    Set (WeakDual ℂ A) :=
  {omega | ∃ xi : H, ‖xi‖ = 1 ∧ xi ∈ Kᗮ ∧
    omega = StrongDual.toWeakDual (vectorFunctional pi xi)}

theorem orthogonalVectorStates_subset_weakStateSpace
    (pi : Representation A H) (K : Submodule ℂ H) :
    orthogonalVectorStates pi K ⊆ weakStateSpace A := by
  rintro omega ⟨xi, hxi, -, rfl⟩
  exact vectorFunctional_mem_stateSpace pi xi hxi

end Representation

section PositiveRange

/-- If a self-adjoint operator has strictly negative quadratic form on the
unit sphere of `Kᗮ`, then its positive part has finite-dimensional range and
is compact. -/
theorem isCompactOperator_posPart_of_inner_lt_on_orthogonal
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (K : Submodule ℂ H)
    [FiniteDimensional ℂ K]
    (hneg : ∀ z : H, ‖z‖ = 1 → z ∈ Kᗮ → (inner ℂ z (T z)).re < 0) :
    IsCompactOperator (T⁺ : H →L[ℂ] H) := by
  have hmul : T * T⁺ = T⁺ * T⁺ := by
    calc
      T * T⁺ = (T⁺ - T⁻) * T⁺ :=
        congrArg (fun S : H →L[ℂ] H => S * T⁺) (CFC.posPart_sub_negPart T hT).symm
      _ = T⁺ * T⁺ := by rw [sub_mul, CFC.negPart_mul_posPart, sub_zero]
  have hnonneg {y : H} (hy : y ∈ T⁺.range) : 0 ≤ (inner ℂ y (T y)).re := by
    obtain ⟨x, rfl⟩ := hy
    have hTy : T (T⁺ x) = T⁺ (T⁺ x) := by
      simpa only [ContinuousLinearMap.mul_apply] using congrArg (fun S : H →L[ℂ] H => S x) hmul
    change 0 ≤ (inner ℂ (T⁺ x) (T (T⁺ x))).re
    rw [hTy]
    simpa using
      (RCLike.nonneg_iff.mp ((CFC.posPart_nonneg T).inner_nonneg_right (T⁺ x))).1
  have hzero {y : H} (hyrange : y ∈ T⁺.range) (hyorth : y ∈ Kᗮ) : y = 0 := by
    by_contra hy0
    have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    let z : H := (‖y‖⁻¹ : ℂ) • y
    have hzunit : ‖z‖ = 1 := by
      simp [z, norm_smul, abs_of_pos hynorm, hynorm.ne']
    have hzorth : z ∈ Kᗮ := (Kᗮ).smul_mem (‖y‖⁻¹ : ℂ) hyorth
    have hzrange : z ∈ T⁺.range := T⁺.range.smul_mem (‖y‖⁻¹ : ℂ) hyrange
    exact (not_lt_of_ge (hnonneg hzrange)) (hneg z hzunit hzorth)
  let q : T⁺.range →ₗ[ℂ] K :=
    K.orthogonalProjectionOnto.toLinearMap.comp T⁺.range.subtype
  have hq : Function.Injective q := by
    intro y z hyz
    apply Subtype.ext
    have hproj : K.orthogonalProjectionOnto ((y : H) - (z : H)) = 0 := by
      dsimp [q] at hyz ⊢
      rw [map_sub]
      rw [hyz, sub_self]
    have horth : (y : H) - (z : H) ∈ Kᗮ :=
      Submodule.orthogonalProjectionOnto_eq_zero_iff.mp hproj
    have hrange : (y : H) - (z : H) ∈ T⁺.range :=
      T⁺.range.sub_mem y.2 z.2
    exact sub_eq_zero.mp (hzero hrange horth)
  letI : FiniteDimensional ℂ T⁺.range := FiniteDimensional.of_injective q hq
  have hrangeCompact : IsCompactOperator (T⁺.rangeRestrict : H → T⁺.range) := by
    simpa [Function.comp_def, ContinuousLinearMap.coe_rangeRestrict] using
      (isCompactOperator_id (E := T⁺.range)).comp_clm T⁺.rangeRestrict
  have hcompact := hrangeCompact.clm_comp T⁺.range.subtypeL
  simpa [Function.comp_def] using hcompact

end PositiveRange

section ConvexDensity

variable [Nontrivial H]

/-- Essentiality in the form needed by the vector-state density argument. -/
def Representation.HasNoNonzeroCompactImage (pi : Representation A H) : Prop :=
  ∀ a : A, IsCompactOperator (pi a) → pi a = 0

/-- A state which vanishes on the kernel of an essential representation is in
the weak-star closed convex hull of unit vector states outside every prescribed
finite-dimensional subspace. -/
theorem Representation.mem_closure_convexHull_orthogonalVectorStates
    (pi : Representation A H) (hpi : pi.HasNoNonzeroCompactImage)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hker : ∀ a : A, pi a = 0 → phi a = 0)
    (K : Submodule ℂ H) [FiniteDimensional ℂ K] :
    StrongDual.toWeakDual phi ∈
      closure (convexHull ℝ (pi.orthogonalVectorStates K)) := by
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
      omega b = (omega a).re := by
    exact state_apply_realPart omega.toStrongDual homega a
  have hneg (z : H) (hzunit : ‖z‖ = 1) (hzorth : z ∈ Kᗮ) :
      (inner ℂ z (pi d z)).re < 0 := by
    let omega : WeakDual ℂ A := StrongDual.toWeakDual (vectorFunctional pi z)
    have homegaV : omega ∈ pi.orthogonalVectorStates K :=
      ⟨z, hzunit, hzorth, rfl⟩
    have homegaState : omega ∈ weakStateSpace A :=
      pi.orthogonalVectorStates_subset_weakStateSpace K homegaV
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
  let c : A := d⁺
  have hpid : IsSelfAdjoint (pi d) := by
    rw [isSelfAdjoint_iff, ← map_star, hd.star_eq]
  have hpi_cont : Continuous pi :=
    (Representation.continuousLinearMap pi).continuous
  have hmap_c : pi c = (pi d)⁺ := by
    dsimp [c]
    rw [CFC.posPart_def, cfcₙ_eq_cfc, CFC.posPart_def, cfcₙ_eq_cfc]
    exact pi.map_cfc (·⁺ : ℝ → ℝ) d
      (hφ := hpi_cont) (ha := hd) (hφa := hpid)
  have hcompact_c : IsCompactOperator (pi c) := by
    rw [hmap_c]
    exact isCompactOperator_posPart_of_inner_lt_on_orthogonal (pi d) hpid K hneg
  have hpic : pi c = 0 := hpi c hcompact_c
  have hphic : phi c = 0 := hker c hpic
  let p : A →ₚ[ℂ] ℂ := positiveLinearMapOfMemStateSpace phi hphi
  have hle : p d ≤ p c := OrderHomClass.mono p (CFC.le_posPart hd)
  have hre : (phi d).re ≤ 0 := by
    have hn := RCLike.nonneg_iff.mp (sub_nonneg.mpr hle)
    simpa [p, c, hphic] using hn.1
  exact (not_lt_of_ge hre) hphi_d_pos

end ConvexDensity

section PureApproximation

variable [Nontrivial H]

/-- Purity is unchanged when the continuous dual is equipped with its
weak-star topology. -/
theorem toWeakDual_mem_extremePoints
    (phi : A →L[ℂ] ℂ) (hpure : IsPureState A phi) :
    StrongDual.toWeakDual phi ∈ (weakStateSpace A).extremePoints ℝ := by
  rw [IsPureState, mem_extremePoints_iff_left] at hpure
  rw [mem_extremePoints_iff_left]
  refine ⟨hpure.1, ?_⟩
  intro psi hpsi theta htheta hseg
  have hseg' : phi ∈ openSegment ℝ psi.toStrongDual theta.toStrongDual := by
    obtain ⟨s, t, hs, ht, hst, hconv⟩ := hseg
    refine ⟨s, t, hs, ht, hst, ?_⟩
    apply ContinuousLinearMap.ext
    intro a
    exact congrArg (fun omega : WeakDual ℂ A => omega a) hconv
  have heq : psi.toStrongDual = phi :=
    hpure.2 psi.toStrongDual hpsi theta.toStrongDual htheta hseg'
  apply DFunLike.ext _ _
  intro a
  exact congrArg (fun f : StrongDual ℂ A => f a) heq

/-- For a pure state, convex density by orthogonal vector states improves to
ordinary weak-star density by the same vector states. -/
theorem Representation.mem_closure_orthogonalVectorStates
    (pi : Representation A H) (hpi : pi.HasNoNonzeroCompactImage)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi)
    (hker : ∀ a : A, pi a = 0 → phi a = 0)
    (K : Submodule ℂ H) [FiniteDimensional ℂ K] :
    StrongDual.toWeakDual phi ∈ closure (pi.orthogonalVectorStates K) := by
  exact @mem_closure_of_mem_extremePoints_of_mem_closure_convexHull
    (WeakDual ℂ A) inferInstance (WeakDual.instModule' ℝ) inferInstance
    inferInstance inferInstance vectorApproximationWeakDualContinuousRealSMul
    vectorApproximationWeakDualLocallyConvexSpace
    (weakStateSpace A) (pi.orthogonalVectorStates K) (StrongDual.toWeakDual phi)
    isCompact_weakStateSpace convex_weakStateSpace
    (pi.orthogonalVectorStates_subset_weakStateSpace K)
    (toWeakDual_mem_extremePoints phi hpure)
    (pi.mem_closure_convexHull_orthogonalVectorStates hpi phi hphi hker K)

/-- One unit vector outside `K` simultaneously approximates a pure state on
all members of a finite test set. -/
theorem Representation.exists_unit_mem_orthogonal_approx
    (pi : Representation A H) (hpi : pi.HasNoNonzeroCompactImage)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi)
    (hker : ∀ a : A, pi a = 0 → phi a = 0)
    (K : Submodule ℂ H) [FiniteDimensional ℂ K]
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z : H, ‖z‖ = 1 ∧ z ∈ Kᗮ ∧
      ∀ a ∈ F, ‖phi a - inner ℂ z (pi a z)‖ < epsilon := by
  let U : Set (WeakDual ℂ A) :=
    ⋂ a ∈ F, (fun omega : WeakDual ℂ A => omega a) ⁻¹' ball (phi a) epsilon
  have hUopen : IsOpen U := by
    exact isOpen_biInter_finset fun a ha =>
      isOpen_ball.preimage (WeakDual.eval_continuous a)
  have hphiU : StrongDual.toWeakDual phi ∈ U := by
    apply mem_iInter₂.mpr
    intro a ha
    change StrongDual.toWeakDual phi a ∈ ball (phi a) epsilon
    simpa using (Metric.mem_ball_self (x := phi a) hepsilon)
  have hclosure := pi.mem_closure_orthogonalVectorStates hpi phi hphi hpure hker K
  obtain ⟨omega, homegaU, homega⟩ :=
    mem_closure_iff.mp hclosure U hUopen hphiU
  obtain ⟨z, hzunit, hzorth, rfl⟩ := homega
  refine ⟨z, hzunit, hzorth, ?_⟩
  intro a ha
  have hball : StrongDual.toWeakDual (vectorFunctional pi z) a ∈
      ball (phi a) epsilon := by
    exact mem_iInter₂.mp homegaU a ha
  rw [mem_ball, dist_comm, dist_eq_norm] at hball
  simpa only [StrongDual.toWeakDual_apply, vectorFunctional_apply] using hball

/-- A state vanishes on every element acting as zero in its own GNS
representation.  This is a representation-kernel statement, not the kernel
of the scalar functional. -/
theorem state_eq_zero_of_gnsStarAlgHom_eq_zero
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) {a : A}
    (ha : (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom a = 0) :
    phi a = 0 := by
  rw [← inner_gnsStarAlgHom_stateGNSVector phi hphi a, ha]
  simp

/-- Finite-test approximation when the represented kernel agrees with the
GNS representation kernel of the pure state. -/
theorem Representation.exists_unit_mem_orthogonal_approx_of_ker_eq_gns
    (pi : Representation A H) (hpi : pi.HasNoNonzeroCompactImage)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi)
    (hker : ∀ a : A, pi a = 0 ↔
      (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom a = 0)
    (K : Submodule ℂ H) [FiniteDimensional ℂ K]
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z : H, ‖z‖ = 1 ∧ z ∈ Kᗮ ∧
      ∀ a ∈ F, ‖phi a - inner ℂ z (pi a z)‖ < epsilon := by
  apply pi.exists_unit_mem_orthogonal_approx hpi phi hphi hpure
    (fun a ha => state_eq_zero_of_gnsStarAlgHom_eq_zero phi hphi ((hker a).mp ha))
    K F hepsilon

end PureApproximation

section TransformedFamilies

variable [Nontrivial H]

/-- The finite-dimensional forbidden space generated by the two transformed
families needed for Gram-matrix comparisons. -/
def Representation.transformedForbiddenSpace {n : ℕ}
    (pi : Representation A H) (x : Fin n → A) (xi eta : H) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range fun p : (Fin n × Fin n) × Bool =>
    if p.2 then pi (x p.1.1 * star (x p.1.2)) xi
    else pi (x p.1.1 * star (x p.1.2)) eta)

theorem Representation.finiteDimensional_transformedForbiddenSpace {n : ℕ}
    (pi : Representation A H) (x : Fin n → A) (xi eta : H) :
    FiniteDimensional ℂ (pi.transformedForbiddenSpace x xi eta) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

/-- The single approximating vector can be chosen so that both transformed
families are orthogonal to it, while all requested state moments are
simultaneously approximated. -/
theorem Representation.exists_unit_approx_and_transformed_orthogonal {n : ℕ}
    (pi : Representation A H) (hpi : pi.HasNoNonzeroCompactImage)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi)
    (hker : ∀ a : A, pi a = 0 → phi a = 0)
    (x : Fin n → A) (xi eta : H) (F : Finset A)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z : H, ‖z‖ = 1 ∧
      (∀ i j : Fin n,
        inner ℂ (pi (star (x i)) z) (pi (star (x j)) xi) = 0) ∧
      (∀ i j : Fin n,
        inner ℂ (pi (star (x i)) z) (pi (star (x j)) eta) = 0) ∧
      (∀ a ∈ F, ‖phi a - inner ℂ z (pi a z)‖ < epsilon) := by
  let K : Submodule ℂ H := pi.transformedForbiddenSpace x xi eta
  letI : FiniteDimensional ℂ K :=
    pi.finiteDimensional_transformedForbiddenSpace x xi eta
  obtain ⟨z, hzunit, hzorth, happrox⟩ :=
    pi.exists_unit_mem_orthogonal_approx hpi phi hphi hpure hker K F hepsilon
  have hzK : ∀ w : H, w ∈ K → inner ℂ z w = 0 :=
    (Submodule.mem_orthogonal' K z).mp hzorth
  have hxi (i j : Fin n) :
      inner ℂ (pi (star (x i)) z) (pi (star (x j)) xi) = 0 := by
    have hgen : pi (x i * star (x j)) xi ∈ K := by
      apply Submodule.subset_span
      exact ⟨((i, j), true), by simp [K, Representation.transformedForbiddenSpace]⟩
    have hadj : ContinuousLinearMap.adjoint (pi (star (x i))) = pi (x i) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_star]
    calc
      inner ℂ (pi (star (x i)) z) (pi (star (x j)) xi) =
          inner ℂ z (ContinuousLinearMap.adjoint (pi (star (x i)))
            (pi (star (x j)) xi)) :=
        (ContinuousLinearMap.adjoint_inner_right
          (pi (star (x i))) z (pi (star (x j)) xi)).symm
      _ = inner ℂ z (pi (x i * star (x j)) xi) := by
        rw [hadj, map_mul, ContinuousLinearMap.mul_apply]
      _ = 0 := hzK _ hgen
  have heta (i j : Fin n) :
      inner ℂ (pi (star (x i)) z) (pi (star (x j)) eta) = 0 := by
    have hgen : pi (x i * star (x j)) eta ∈ K := by
      apply Submodule.subset_span
      exact ⟨((i, j), false), by simp [K, Representation.transformedForbiddenSpace]⟩
    have hadj : ContinuousLinearMap.adjoint (pi (star (x i))) = pi (x i) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_star]
    calc
      inner ℂ (pi (star (x i)) z) (pi (star (x j)) eta) =
          inner ℂ z (ContinuousLinearMap.adjoint (pi (star (x i)))
            (pi (star (x j)) eta)) :=
        (ContinuousLinearMap.adjoint_inner_right
          (pi (star (x i))) z (pi (star (x j)) eta)).symm
      _ = inner ℂ z (pi (x i * star (x j)) eta) := by
        rw [hadj, map_mul, ContinuousLinearMap.mul_apply]
      _ = 0 := hzK _ hgen
  exact ⟨z, hzunit, hxi, heta, happrox⟩

end TransformedFamilies

end MathlibAnnex.Analysis.CStarAlgebra
