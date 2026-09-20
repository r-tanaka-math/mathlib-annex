import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.Representation
import MathlibAnnex.Analysis.CStarAlgebra.State.VectorApproximation

/-!
# Finite vector approximation for genuinely nonunital C-star algebras

This file passes the unital finite-test theorem through the minimal
unitization.  It first records the nondegeneracy and essential-image bridges;
the state-extension bridge is developed below without assuming that the
unitized representation is faithful.
-/

set_option autoImplicit false

open Filter Metric Set
open scoped ComplexOrder InnerProduct Topology

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- Nondegeneracy in the common-kernel form.  For star representations this
is equivalent to density of the represented ranges. -/
def IsNondegenerate (pi : NonUnitalCStarRepresentation A H) : Prop :=
  ∀ x : H, (∀ a : A, pi a x = 0) → x = 0

/-- Essentiality for a genuinely nonunital representation. -/
def HasNoNonzeroCompactImage (pi : NonUnitalCStarRepresentation A H) : Prop :=
  ∀ a : A, IsCompactOperator (pi a) → pi a = 0

private theorem eq_zero_of_mul_eq_zero
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (T : H →L[ℂ] H) (hT : ∀ a : A, T * pi a = 0) : T = 0 := by
  have hadj : ContinuousLinearMap.adjoint T = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    apply hnd
    intro a
    have hcomp : T.comp (pi (star a)) = 0 := hT (star a)
    have hzero := congrArg ContinuousLinearMap.adjoint hcomp
    rw [ContinuousLinearMap.adjoint_comp] at hzero
    have hpiadj : ContinuousLinearMap.adjoint (pi (star a)) = pi a := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_star]
    rw [hpiadj] at hzero
    simpa using congrArg (fun S : H →L[ℂ] H => S x) hzero
  have := congrArg ContinuousLinearMap.adjoint hadj
  simpa using this

/-- A nondegenerate essential representation stays essential after canonical
unitization, without any faithfulness assumption on that unitization. -/
theorem hasNoNonzeroCompactImage_unitization
    (pi : NonUnitalCStarRepresentation A H)
    (hnd : pi.IsNondegenerate) (hpi : pi.HasNoNonzeroCompactImage) :
    pi.unitization.HasNoNonzeroCompactImage := by
  intro z hz
  apply eq_zero_of_mul_eq_zero pi hnd (pi.unitization z)
  intro b
  have hcompact : IsCompactOperator (pi.unitization z * pi b) := by
    exact hz.comp_clm (pi b)
  have hbelongs : pi.unitization z * pi b =
      pi (z.fst • b + z.snd * b) := by
    calc
      pi.unitization z * pi b =
          pi.unitization z * pi.unitization (Unitization.inr b) := by
            rw [unitization_inr]
      _ = pi.unitization (z * Unitization.inr b) := by rw [map_mul]
      _ = pi (z.fst • b + z.snd * b) := by
        induction z using Unitization.ind with
        | inl_add_inr c a => simp [unitization]
  rw [hbelongs] at hcompact ⊢
  exact hpi _ hcompact

end NonUnitalCStarRepresentation

section States

/-- Norm-one positive functionals on a genuinely nonunital C-star algebra. -/
def nonUnitalStateSpace (A : Type u) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] : Set (A →L[ℂ] ℂ) :=
  {phi | (∀ a : A, 0 ≤ a → 0 ≤ phi a) ∧ ‖phi‖ = 1}

/-- Purity for a nonunital state is extremality in the norm-one positive
state space. -/
def IsPureNonUnitalState (A : Type u) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (phi : A →L[ℂ] ℂ) : Prop :=
  phi ∈ (nonUnitalStateSpace A).extremePoints ℝ

/-- The canonical linear extension `phi~(lambda,a) = lambda + phi(a)` to the
minimal unitization. -/
noncomputable def unitizationExtension (phi : A →L[ℂ] ℂ) :
    Unitization ℂ A →L[ℂ] ℂ where
  toFun z := z.fst + phi z.snd
  map_add' z w := by simp; ring
  map_smul' c z := by simp [mul_add]
  cont := Unitization.continuous_fst.add
    (phi.continuous.comp Unitization.continuous_snd)

@[simp]
theorem unitizationExtension_apply (phi : A →L[ℂ] ℂ)
    (z : Unitization ℂ A) :
    unitizationExtension phi z = z.fst + phi z.snd :=
  rfl

@[simp]
theorem unitizationExtension_inr (phi : A →L[ℂ] ℂ) (a : A) :
    unitizationExtension phi (Unitization.inr a) = phi a := by
  simp [unitizationExtension]

@[simp]
theorem unitizationExtension_one (phi : A →L[ℂ] ℂ) :
    unitizationExtension phi 1 = 1 := by
  simp [unitizationExtension]

/-- Cauchy--Schwarz for a positive functional, obtained from its pre-GNS
inner product. -/
theorem norm_apply_star_mul_le
    (phi : A →L[ℂ] ℂ) (hphi : ∀ a : A, 0 ≤ a → 0 ≤ phi a)
    (x y : A) :
    ‖phi (star x * y)‖ ≤
      √(phi (star x * x)).re * √(phi (star y * y)).re := by
  let f : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ phi.toLinearMap hphi
  have h := norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS x) (f.toPreGNS y)
  change ‖phi (star x * y)‖ ≤
    √(phi (star x * x)).re * √(phi (star y * y)).re at h
  exact h

theorem sq_norm_apply_star_mul_le
    (phi : A →L[ℂ] ℂ) (hphi : ∀ a : A, 0 ≤ a → 0 ≤ phi a)
    (x y : A) :
    ‖phi (star x * y)‖ ^ 2 ≤
      (phi (star x * x)).re * (phi (star y * y)).re := by
  have hx0 : 0 ≤ (phi (star x * x)).re :=
    (RCLike.nonneg_iff.mp (hphi _ (star_mul_self_nonneg x))).1
  have hy0 : 0 ≤ (phi (star y * y)).re :=
    (RCLike.nonneg_iff.mp (hphi _ (star_mul_self_nonneg y))).1
  calc
    ‖phi (star x * y)‖ ^ 2 ≤
        (√(phi (star x * x)).re * √(phi (star y * y)).re) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
        (norm_apply_star_mul_le phi hphi x y)
    _ = (phi (star x * x)).re * (phi (star y * y)).re := by
      rw [mul_pow, Real.sq_sqrt hx0, Real.sq_sqrt hy0]

theorem mul_self_le_self_of_nonneg_of_norm_le_one
    (e : A) (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1) : e * e ≤ e := by
  have heU0 : 0 ≤ (e : Unitization ℂ A) :=
    Unitization.inr_nonneg_iff.mpr he0
  have heU1 : (e : Unitization ℂ A) ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (e : Unitization ℂ A) heU0).mp (by
      simpa only [Unitization.norm_inr] using he1)
  have hp := CStarAlgebra.pow_antitone heU0 heU1
    (show (1 : ℕ) ≤ 2 by norm_num)
  have hee0 : 0 ≤ e * e := by
    simpa only [he0.isSelfAdjoint.star_eq] using star_mul_self_nonneg e
  apply (Unitization.inr_le_iff (e * e) e hee0.isSelfAdjoint
    he0.isSelfAdjoint).mp
  simpa [pow_two] using hp

/-- A norm-one positive functional converges to one along the canonical
increasing approximate unit. -/
theorem tendsto_apply_approximateUnit
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ nonUnitalStateSpace A) :
    Tendsto (fun e : A => phi e) (CStarAlgebra.approximateUnit A) (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let eta : ℝ := min (epsilon / 4) (1 / 4)
  have heta0 : 0 < eta := by
    exact lt_min (div_pos hepsilon (by norm_num)) (by norm_num)
  have heta_epsilon : eta ≤ epsilon / 4 := min_le_left _ _
  have heta_quarter : eta ≤ 1 / 4 := min_le_right _ _
  let r : ℝ := 1 - eta
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hrnorm : r < ‖phi‖ := by rw [hphi.2]; dsimp [r]; linarith
  obtain ⟨a, ha_norm, ha_phi⟩ := phi.exists_lt_apply_of_lt_opNorm hrnorm
  have hae_tendsto :
      Tendsto (fun e : A => ‖phi (a * e)‖)
        (CStarAlgebra.approximateUnit A) (𝓝 ‖phi a‖) := by
    exact (continuous_norm.comp phi.continuous).tendsto (a) |>.comp
      ((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left a)
  have hae_eventually :
      ∀ᶠ e : A in CStarAlgebra.approximateUnit A, r < ‖phi (a * e)‖ :=
    hae_tendsto (isOpen_Ioi.mem_nhds ha_phi)
  filter_upwards
    [(CStarAlgebra.increasingApproximateUnit A).eventually_nonneg,
      (CStarAlgebra.increasingApproximateUnit A).eventually_norm,
      hae_eventually] with e he0 he1 hae
  have hphie0 := RCLike.nonneg_iff.mp (hphi.1 e he0)
  have hphie_real : phi e = ((phi e).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hphie0.2
  have hnorm_phie : ‖phi e‖ = (phi e).re := by
    calc
      ‖phi e‖ = ‖((phi e).re : ℂ)‖ := congrArg norm hphie_real
      _ = |(phi e).re| := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ = (phi e).re := abs_of_nonneg hphie0.1
  have hphie_le : (phi e).re ≤ 1 := by
    rw [← hnorm_phie]
    calc
      ‖phi e‖ ≤ ‖phi‖ * ‖e‖ := phi.le_opNorm e
      _ ≤ 1 * 1 := mul_le_mul (le_of_eq hphi.2) he1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have haa0 : 0 ≤ a * star a := by
    simpa using (star_mul_self_nonneg (star a))
  have hx0 : 0 ≤ (phi (a * star a)).re :=
    (RCLike.nonneg_iff.mp (hphi.1 _ haa0)).1
  have hx_le : (phi (a * star a)).re ≤ 1 := by
    calc
      (phi (a * star a)).re ≤ ‖phi (a * star a)‖ := Complex.re_le_norm _
      _ ≤ ‖phi‖ * ‖a * star a‖ := phi.le_opNorm _
      _ = 1 * ‖a * star a‖ := by rw [hphi.2]
      _ ≤ 1 * (‖a‖ * ‖star a‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le a (star a)) zero_le_one
      _ ≤ 1 * (1 * 1) := by
        rw [norm_star]
        gcongr
      _ = 1 := by ring
  have hee_le : e * e ≤ e :=
    mul_self_le_self_of_nonneg_of_norm_le_one e he0 he1
  have hy_le : (phi (e * e)).re ≤ (phi e).re := by
    have horder : phi (e * e) ≤ phi e := by
      apply sub_nonneg.mp
      rw [← map_sub]
      exact hphi.1 _ (sub_nonneg.mpr hee_le)
    have hre := (RCLike.nonneg_iff.mp (sub_nonneg.mpr horder)).1
    simpa using hre
  have hy0 : 0 ≤ (phi (e * e)).re := by
    have hee0 : 0 ≤ e * e := by
      simpa only [he0.isSelfAdjoint.star_eq] using star_mul_self_nonneg e
    exact (RCLike.nonneg_iff.mp (hphi.1 _ hee0)).1
  have hcs := sq_norm_apply_star_mul_le phi hphi.1 (star a) e
  simp only [star_star, he0.isSelfAdjoint.star_eq] at hcs
  have hcs' : ‖phi (a * e)‖ ^ 2 ≤ (phi e).re := by
    refine hcs.trans ?_
    calc
      (phi (a * star a)).re * (phi (e * e)).re ≤ 1 * (phi e).re :=
        mul_le_mul hx_le hy_le hy0 zero_le_one
      _ = (phi e).re := one_mul _
  have hr_sq_lt : r ^ 2 < ‖phi (a * e)‖ ^ 2 :=
    (sq_lt_sq₀ hr0 (norm_nonneg _)).2 hae
  have hphie_lower : r ^ 2 < (phi e).re := hr_sq_lt.trans_le hcs'
  have hr_error : 1 - r ^ 2 < epsilon := by
    dsimp [r]
    nlinarith
  rw [hphie_real, Complex.dist_eq]
  calc
    ‖((phi e).re : ℂ) - 1‖ = |(phi e).re - 1| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
    _ = 1 - (phi e).re := by
      simpa only [neg_sub] using abs_of_nonpos (sub_nonpos.mpr hphie_le)
    _ < epsilon := by linarith

theorem unitization_mul_inr (z : Unitization ℂ A) (a : A) :
    z * Unitization.inr a =
      Unitization.inr (z.fst • a + z.snd * a) := by
  induction z using Unitization.ind with
  | inl_add_inr c b =>
      simp [add_mul, Unitization.inl_mul_inr, Unitization.inr_mul]

/-- The values obtained by multiplying a unitization element into the
approximate unit converge to its canonical extended-state value. -/
theorem tendsto_apply_unitization_mul_approximateUnit
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ nonUnitalStateSpace A)
    (z : Unitization ℂ A) :
    Tendsto (fun e : A => phi (z.fst • e + z.snd * e))
      (CStarAlgebra.approximateUnit A) (𝓝 (unitizationExtension phi z)) := by
  have hscalar :
      Tendsto (fun e : A => z.fst • phi e)
        (CStarAlgebra.approximateUnit A) (𝓝 (z.fst • (1 : ℂ))) :=
    (continuous_const_smul z.fst).tendsto (1 : ℂ) |>.comp
      (tendsto_apply_approximateUnit phi hphi)
  have hmul :
      Tendsto (fun e : A => phi (z.snd * e))
        (CStarAlgebra.approximateUnit A) (𝓝 (phi z.snd)) :=
    phi.continuous.tendsto z.snd |>.comp
      ((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left z.snd)
  simpa [unitizationExtension, map_add, map_smul] using hscalar.add hmul

/-- The canonical unitization extension of a nonunital state is contractive. -/
theorem norm_unitizationExtension_apply_le
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ nonUnitalStateSpace A)
    (z : Unitization ℂ A) :
    ‖unitizationExtension phi z‖ ≤ ‖z‖ := by
  have htend :
      Tendsto (fun e : A => ‖phi (z.fst • e + z.snd * e)‖)
        (CStarAlgebra.approximateUnit A) (𝓝 ‖unitizationExtension phi z‖) :=
    continuous_norm.tendsto _ |>.comp
      (tendsto_apply_unitization_mul_approximateUnit phi hphi z)
  apply le_of_tendsto htend
  filter_upwards [(CStarAlgebra.increasingApproximateUnit A).eventually_norm]
    with e he
  calc
    ‖phi (z.fst • e + z.snd * e)‖ ≤
        ‖phi‖ * ‖z.fst • e + z.snd * e‖ := phi.le_opNorm _
    _ = ‖z.fst • e + z.snd * e‖ := by rw [hphi.2, one_mul]
    _ = ‖(Unitization.inr (z.fst • e + z.snd * e) : Unitization ℂ A)‖ := by
      rw [Unitization.norm_inr]
    _ = ‖z * Unitization.inr e‖ := by rw [unitization_mul_inr]
    _ ≤ ‖z‖ * ‖(Unitization.inr e : Unitization ℂ A)‖ := norm_mul_le _ _
    _ = ‖z‖ * ‖e‖ := by rw [Unitization.norm_inr]
    _ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left he (norm_nonneg z)
    _ = ‖z‖ := mul_one _

/-- The canonical extension is a state on the minimal unitization. -/
theorem unitizationExtension_mem_stateSpace
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ nonUnitalStateSpace A) :
    unitizationExtension phi ∈ stateSpace (Unitization ℂ A) := by
  have hnorm : ‖unitizationExtension phi‖ ≤ 1 := by
    apply (unitizationExtension phi).opNorm_le_bound zero_le_one
    intro z
    simpa only [one_mul] using norm_unitizationExtension_apply_le phi hphi z
  exact ⟨nonnegative_of_norm_le_one_of_apply_one
    (unitizationExtension phi) hnorm (unitizationExtension_one phi),
    unitizationExtension_one phi⟩

/-- Restriction of a functional on the unitization to the original
nonunital algebra. -/
noncomputable def unitizationRestriction
    (psi : Unitization ℂ A →L[ℂ] ℂ) : A →L[ℂ] ℂ where
  toFun a := psi (Unitization.inr a)
  map_add' a b := by simp
  map_smul' c a := by simp
  cont := psi.continuous.comp Unitization.continuous_inr

@[simp]
theorem unitizationRestriction_apply
    (psi : Unitization ℂ A →L[ℂ] ℂ) (a : A) :
    unitizationRestriction psi a = psi (Unitization.inr a) :=
  rfl

@[simp]
theorem unitizationRestriction_extension (phi : A →L[ℂ] ℂ) :
    unitizationRestriction (unitizationExtension phi) = phi := by
  ext a
  simp

theorem unitizationRestriction_nonnegative
    (psi : Unitization ℂ A →L[ℂ] ℂ)
    (hpsi : psi ∈ stateSpace (Unitization ℂ A)) :
    ∀ a : A, 0 ≤ a → 0 ≤ unitizationRestriction psi a := by
  intro a ha
  exact hpsi.1 (Unitization.inr a) (Unitization.inr_nonneg_iff.mpr ha)

theorem norm_unitizationRestriction_le_one
    (psi : Unitization ℂ A →L[ℂ] ℂ)
    (hpsi : psi ∈ stateSpace (Unitization ℂ A)) :
    ‖unitizationRestriction psi‖ ≤ 1 := by
  have hweak : StrongDual.toWeakDual psi ∈
      weakStateSpace (Unitization ℂ A) := hpsi
  have hnorm : ‖psi‖ ≤ 1 := by
    simpa using (norm_le_one_of_mem_weakStateSpace hweak)
  apply (unitizationRestriction psi).opNorm_le_bound zero_le_one
  intro a
  calc
    ‖unitizationRestriction psi a‖ ≤ ‖psi‖ * ‖(Unitization.inr a : Unitization ℂ A)‖ :=
      psi.le_opNorm _
    _ ≤ 1 * ‖(Unitization.inr a : Unitization ℂ A)‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = 1 * ‖a‖ := by rw [Unitization.norm_inr]

/-- A unitization state is determined by its restriction whenever that
restriction is the canonical norm-one state. -/
theorem eq_unitizationExtension_of_restriction_eq
    (phi : A →L[ℂ] ℂ) (psi : Unitization ℂ A →L[ℂ] ℂ)
    (hpsi : psi ∈ stateSpace (Unitization ℂ A))
    (hrest : unitizationRestriction psi = phi) :
    psi = unitizationExtension phi := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using Unitization.ind with
  | inl_add_inr c a =>
      have ha := congrArg (fun f : A →L[ℂ] ℂ => f a) hrest
      have hc : psi (Unitization.inl c) = c := by
        change psi (algebraMap ℂ (Unitization ℂ A) c) = c
        rw [Algebra.algebraMap_eq_smul_one, map_smul, hpsi.2]
        simp
      rw [unitizationExtension_apply, map_add]
      rw [hc]
      simpa using ha

/-- Purity of a norm-one positive functional passes to its canonical
unitization extension. -/
theorem isPureState_unitizationExtension
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ nonUnitalStateSpace A)
    (hpure : IsPureNonUnitalState A phi) :
    IsPureState (Unitization ℂ A) (unitizationExtension phi) := by
  rw [IsPureNonUnitalState, mem_extremePoints_iff_left] at hpure
  rw [IsPureState, mem_extremePoints_iff_left]
  refine ⟨unitizationExtension_mem_stateSpace phi hphi, ?_⟩
  intro psi hpsi theta htheta hsegment
  rcases hsegment with ⟨s, t, hs, ht, hst, hcomb⟩
  let psiA : A →L[ℂ] ℂ := unitizationRestriction psi
  let thetaA : A →L[ℂ] ℂ := unitizationRestriction theta
  have hpsi_nonneg : ∀ a : A, 0 ≤ a → 0 ≤ psiA a :=
    unitizationRestriction_nonnegative psi hpsi
  have htheta_nonneg : ∀ a : A, 0 ≤ a → 0 ≤ thetaA a :=
    unitizationRestriction_nonnegative theta htheta
  have hpsi_norm_le : ‖psiA‖ ≤ 1 :=
    norm_unitizationRestriction_le_one psi hpsi
  have htheta_norm_le : ‖thetaA‖ ≤ 1 :=
    norm_unitizationRestriction_le_one theta htheta
  have hcombA : s • psiA + t • thetaA = phi := by
    apply ContinuousLinearMap.ext
    intro a
    have hvalue := congrArg
      (fun q : Unitization ℂ A →L[ℂ] ℂ => q (Unitization.inr a)) hcomb
    simpa [psiA, thetaA] using hvalue
  have hnorm_lower :
      1 ≤ s * ‖psiA‖ + t * ‖thetaA‖ := by
    calc
      1 = ‖phi‖ := hphi.2.symm
      _ = ‖s • psiA + t • thetaA‖ := congrArg norm hcombA.symm
      _ ≤ ‖s • psiA‖ + ‖t • thetaA‖ := norm_add_le _ _
      _ = s * ‖psiA‖ + t * ‖thetaA‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos hs, abs_of_pos ht]
  have hpsi_norm : ‖psiA‖ = 1 := by
    have hpsi0 := norm_nonneg psiA
    have htheta0 := norm_nonneg thetaA
    nlinarith
  have htheta_norm : ‖thetaA‖ = 1 := by
    have hpsi0 := norm_nonneg psiA
    have htheta0 := norm_nonneg thetaA
    nlinarith
  have hpsiA : psiA ∈ nonUnitalStateSpace A :=
    ⟨hpsi_nonneg, hpsi_norm⟩
  have hthetaA : thetaA ∈ nonUnitalStateSpace A :=
    ⟨htheta_nonneg, htheta_norm⟩
  have hsegmentA : phi ∈ openSegment ℝ psiA thetaA :=
    ⟨s, t, hs, ht, hst, hcombA⟩
  have hrest : psiA = phi := hpure.2 psiA hpsiA thetaA hthetaA hsegmentA
  exact eq_unitizationExtension_of_restriction_eq phi psi hpsi hrest

/-- Kernel vanishing also passes to the canonical unitization extension.  No
faithfulness of the unitized representation is used. -/
theorem unitizationExtension_eq_zero_of_unitization_eq_zero
    (pi : NonUnitalCStarRepresentation A H)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ nonUnitalStateSpace A)
    (hker : ∀ a : A, pi a = 0 → phi a = 0)
    {z : Unitization ℂ A} (hz : pi.unitization z = 0) :
    unitizationExtension phi z = 0 := by
  have hvalue (e : A) : phi (z.fst • e + z.snd * e) = 0 := by
    apply hker
    calc
      pi (z.fst • e + z.snd * e) =
          pi.unitization (Unitization.inr (z.fst • e + z.snd * e)) := by
            rw [NonUnitalCStarRepresentation.unitization_inr]
      _ = pi.unitization (z * Unitization.inr e) := by
        rw [unitization_mul_inr]
      _ = pi.unitization z * pi.unitization (Unitization.inr e) := by
        rw [map_mul]
      _ = 0 := by rw [hz, zero_mul]
  have htend := tendsto_apply_unitization_mul_approximateUnit phi hphi z
  have hconst :
      Tendsto (fun _e : A => (0 : ℂ)) (CStarAlgebra.approximateUnit A) (𝓝 0) :=
    tendsto_const_nhds
  apply tendsto_nhds_unique htend
  exact hconst.congr' (Eventually.of_forall fun e => (hvalue e).symm)

/-- Finite-test pure-state approximation for a genuinely nonunital source.
The output uses the original representation and original algebra elements. -/
theorem NonUnitalCStarRepresentation.exists_unit_mem_orthogonal_approx
    (pi : NonUnitalCStarRepresentation A H)
    (hnd : pi.IsNondegenerate) (hpi : pi.HasNoNonzeroCompactImage)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ nonUnitalStateSpace A)
    (hpure : IsPureNonUnitalState A phi)
    (hker : ∀ a : A, pi a = 0 → phi a = 0)
    (K : Submodule ℂ H) [FiniteDimensional ℂ K]
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z : H, ‖z‖ = 1 ∧ z ∈ Kᗮ ∧
      ∀ a ∈ F, ‖phi a - inner ℂ z (pi a z)‖ < epsilon := by
  classical
  have hnz : pi.IsNonzero := by
    rw [NonUnitalCStarRepresentation.IsNonzero]
    by_contra hzero
    have hzero' : ∀ a : A, pi a = 0 := fun a =>
      not_ne_iff.mp (not_exists.mp hzero a)
    have hphi0 : phi = 0 := by
      apply ContinuousLinearMap.ext
      intro a
      exact hker a (hzero' a)
    have := hphi.2
    rw [hphi0, norm_zero] at this
    norm_num at this
  letI : Nontrivial H := pi.nontrivial_of_isNonzero hnz
  let FU : Finset (Unitization ℂ A) := F.image Unitization.inr
  obtain ⟨z, hzunit, hzorth, hzapprox⟩ :=
    pi.unitization.exists_unit_mem_orthogonal_approx
      (pi.hasNoNonzeroCompactImage_unitization hnd hpi)
      (unitizationExtension phi) (unitizationExtension_mem_stateSpace phi hphi)
      (isPureState_unitizationExtension phi hphi hpure)
      (fun _ hz => unitizationExtension_eq_zero_of_unitization_eq_zero
        pi phi hphi hker hz)
      K FU hepsilon
  refine ⟨z, hzunit, hzorth, ?_⟩
  intro a ha
  have hmem : Unitization.inr a ∈ FU := by
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  simpa only [unitizationExtension_inr,
    NonUnitalCStarRepresentation.unitization_inr] using
      hzapprox (Unitization.inr a) hmem

end States

end MathlibAnnex.Analysis.CStarAlgebra
