import MathlibAnnex.Analysis.CStarAlgebra.CAR.Completion
import MathlibAnnex.Analysis.CStarAlgebra.GNSCyclic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Faithfulness and closed-ideal simplicity of the completed CAR algebra
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped ComplexOrder InnerProductSpace

namespace MathlibAnnex.CStarAlgebra.CAR

/-- The positive-linear-map form of the completed root state. -/
noncomputable def rootPositiveState : Limit →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ rootState.toLinearMap rootState_nonneg

@[simp]
theorem rootPositiveState_apply (x : Limit) : rootPositiveState x = rootState x := rfl

@[simp]
theorem rootPositiveState_one : rootPositiveState 1 = 1 := rootState_one

noncomputable instance rootGNSNontrivial : Nontrivial rootPositiveState.GNS := by
  refine ⟨⟨0, rootPositiveState.gnsCyclicVector, ?_⟩⟩
  intro h
  have hn := rootPositiveState.norm_gnsCyclicVector rootPositiveState_one
  rw [← h, norm_zero] at hn
  exact zero_ne_one hn

theorem norm_leftMulMapPreGNS_apply_le (x : Limit) (y : rootPositiveState.PreGNS) :
    ‖rootPositiveState.leftMulMapPreGNS x y‖ ≤ ‖x‖ * ‖y‖ := by
  rw [PositiveLinearMap.leftMulMapPreGNS_apply]
  rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow,
    ← RCLike.ofReal_le_ofReal (K := ℂ), RCLike.ofReal_pow,
    RCLike.ofReal_eq_complex_ofReal, PositiveLinearMap.preGNS_norm_sq]
  have horder :
      star (rootPositiveState.ofPreGNS y) * star x *
          (x * rootPositiveState.ofPreGNS y) ≤
        ‖x‖ ^ 2 • star (rootPositiveState.ofPreGNS y) *
          rootPositiveState.ofPreGNS y := by
    rw [← mul_assoc, mul_assoc _ (star x), sq,
      ← CStarRing.norm_star_mul_self (x := x), smul_mul_assoc]
    exact CStarAlgebra.star_left_conjugate_le_norm_smul
  calc
    _ ≤ rootPositiveState
        (‖x‖ ^ 2 • star (rootPositiveState.ofPreGNS y) *
          rootPositiveState.ofPreGNS y) := by
      simpa using OrderHomClass.mono rootPositiveState horder
    _ = _ := by
      simp [← Complex.coe_smul, PositiveLinearMap.preGNS_norm_sq]

theorem norm_leftMulMapPreGNS_le (x : Limit) :
    ‖rootPositiveState.leftMulMapPreGNS x‖ ≤ ‖x‖ := by
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
    (norm_leftMulMapPreGNS_apply_le x)

theorem norm_rootRepresentation_le (x : Limit) :
    ‖rootPositiveState.gnsStarAlgHom x‖ ≤ ‖x‖ := by
  change ‖rootPositiveState.leftMulMapPreGNS x |>.completion‖ ≤ ‖x‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
  intro y
  refine UniformSpace.Completion.induction_on
    (p := fun y => ‖rootPositiveState.leftMulMapPreGNS x |>.completion y‖ ≤
      ‖x‖ * ‖y‖) y ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro z
    simpa using norm_leftMulMapPreGNS_apply_le x z

/-- The root GNS representation, bundled as a continuous linear map in its algebra argument. -/
noncomputable def rootRepresentationCLM :
    Limit →L[ℂ] (rootPositiveState.GNS →L[ℂ] rootPositiveState.GNS) :=
  (rootPositiveState.gnsStarAlgHom).toLinearMap.mkContinuous 1 fun x => by
    simpa using norm_rootRepresentation_le x

@[simp]
theorem rootRepresentationCLM_apply (x : Limit) :
    rootRepresentationCLM x = rootPositiveState.gnsStarAlgHom x := by rfl

theorem rootRepresentation_stage_injective (n : ℕ) :
    Function.Injective (rootPositiveState.gnsStarAlgHom.comp (ofStage n)) :=
  (rootPositiveState.gnsStarAlgHom.comp (ofStage n)).toRingHom.injective

theorem norm_rootRepresentation_stage (n : ℕ) (x : Stage n) :
    ‖rootPositiveState.gnsStarAlgHom (ofStage n x)‖ = ‖ofStage n x‖ := by
  exact NonUnitalStarAlgHom.norm_map
    (rootPositiveState.gnsStarAlgHom.comp (ofStage n))
    (rootRepresentation_stage_injective n) x |>.trans (norm_ofStage n x).symm

theorem norm_rootRepresentation (x : Limit) :
    ‖rootPositiveState.gnsStarAlgHom x‖ = ‖x‖ := by
  let f : Limit → ℝ := fun x => ‖rootRepresentationCLM x‖
  let g : Limit → ℝ := fun x => ‖x‖
  have hfg : f = g := (rootRepresentationCLM.continuous.norm).ext_on
      dense_stageRange continuous_norm fun x hx => by
    rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
    rcases hn with ⟨a, rfl⟩
    exact norm_rootRepresentation_stage n a
  exact congrFun hfg x

theorem rootRepresentation_injective :
    Function.Injective rootPositiveState.gnsStarAlgHom :=
  fun x y hxy => by
    rw [← sub_eq_zero, ← norm_eq_zero, ← norm_rootRepresentation]
    rw [map_sub, hxy, sub_self, norm_zero]

/-- Matrix coefficients of the cyclic root vector separate elements because its
GNS representation is faithful. -/
theorem exists_rootState_mul_ne_zero {x : Limit} (hx : x ≠ 0) :
    ∃ b c : Limit, rootState (b * x * c) ≠ 0 := by
  by_contra h
  push Not at h
  have horbit (c : Limit) :
      rootPositiveState.gnsStarAlgHom x
        (rootPositiveState.gnsStarAlgHom c rootPositiveState.gnsCyclicVector) = 0 := by
    apply norm_eq_zero.mp
    calc
      ‖rootPositiveState.gnsStarAlgHom x
          (rootPositiveState.gnsStarAlgHom c rootPositiveState.gnsCyclicVector)‖ =
          ‖rootPositiveState.gnsStarAlgHom (x * c)
            rootPositiveState.gnsCyclicVector‖ := by
        rw [map_mul]
        rfl
      _ = ‖(rootPositiveState.toPreGNS (x * c) : rootPositiveState.GNS)‖ := by
        rw [PositiveLinearMap.gnsStarAlgHom_apply_gnsCyclicVector]
      _ = ‖rootPositiveState.toPreGNS (x * c)‖ :=
        UniformSpace.Completion.norm_coe _
      _ = 0 := by
        have hs : ((‖rootPositiveState.toPreGNS (x * c)‖ ^ 2 : ℝ) : ℂ) = 0 := by
          calc
            ((‖rootPositiveState.toPreGNS (x * c)‖ ^ 2 : ℝ) : ℂ) =
                rootPositiveState (star (x * c) * (x * c)) := by
              simpa using rootPositiveState.preGNS_norm_sq
                (rootPositiveState.toPreGNS (x * c))
            _ = 0 := by
              change rootState (star (x * c) * (x * c)) = 0
              rw [star_mul]
              simpa only [mul_assoc] using h (star c * star x) c
        exact (sq_eq_zero_iff).mp (Complex.ofReal_injective hs)
  have hop : rootPositiveState.gnsStarAlgHom x = 0 := by
    apply ContinuousLinearMap.coeFn_injective
    exact (rootPositiveState.gnsStarAlgHom x).continuous.ext_on
      rootPositiveState.denseRange_gnsStarAlgHom_apply_gnsCyclicVector
      continuous_zero fun y hy => by
        rcases hy with ⟨c, rfl⟩
        exact horbit c
  apply hx
  apply rootRepresentation_injective
  simpa using hop

private theorem rootProjection_ne_zero (n : ℕ) : rootProjection n ≠ 0 := by
  intro h
  have hentry := congrArg (fun x : Stage n => x 0 0) h
  simp [rootProjection] at hentry

/-- A nonzero element of a two-sided ideal forces one projection of the root flag
into that ideal. The inverse is obtained by a Neumann-series perturbation of `1`. -/
theorem exists_rootFlag_mem_of_ne_zero_mem (I : TwoSidedIdeal Limit)
    {x : Limit} (hx : x ≠ 0) (hxI : x ∈ I) :
    ∃ n, rootFlag n ∈ I := by
  obtain ⟨b, c, hbc⟩ := exists_rootState_mul_ne_zero hx
  let y := b * x * c
  let lam := rootState y
  have hlam : lam ≠ 0 := hbc
  have hyI : y ∈ I := by
    exact I.mul_mem_right (b * x) c (I.mul_mem_left b x hxI)
  have hinv : (lam⁻¹ : ℂ) ≠ 0 := inv_ne_zero hlam
  let δ : ℝ := 1 / (2 * ‖(lam⁻¹ : ℂ)‖)
  have hden : 0 < 2 * ‖(lam⁻¹ : ℂ)‖ := mul_pos two_pos (norm_pos_iff.mpr hinv)
  have hδ : 0 < δ := one_div_pos.mpr hden
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_norm_compressionError y) δ hδ
  have herr : ‖compressionError N y‖ < δ := by
    have := hN N le_rfl
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using this
  let q := rootFlag N
  let z := q * y * q
  have hq : IsStarProjection q := isStarProjection_rootFlag N
  have hzI : z ∈ I := I.mul_mem_right (q * y) q (I.mul_mem_left q y hyI)
  have herr' : ‖z - lam • q‖ < δ := by
    simpa [compressionError, q, z, lam] using herr
  have hscaled_eq : q - lam⁻¹ • z = -(lam⁻¹ • (z - lam • q)) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hlam, one_smul]
    abel
  have hhalf : ‖(lam⁻¹ : ℂ)‖ * δ = (1 : ℝ) / 2 := by
    dsimp [δ]
    rw [one_div, mul_inv_rev, ← mul_assoc,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hinv), one_mul]
    norm_num
  have hsmall : ‖q - lam⁻¹ • z‖ < 1 := by
    rw [hscaled_eq, norm_neg, norm_smul]
    calc
      ‖(lam⁻¹ : ℂ)‖ * ‖z - lam • q‖ <
          ‖(lam⁻¹ : ℂ)‖ * δ :=
        mul_lt_mul_of_pos_left herr' (norm_pos_iff.mpr hinv)
      _ = (1 : ℝ) / 2 := hhalf
      _ < 1 := by norm_num
  have hu : IsUnit (1 - (q - lam⁻¹ • z)) :=
    isUnit_one_sub_of_norm_lt_one hsmall
  have hzq : z * q = z := by
    dsimp [z]
    rw [mul_assoc, hq.isIdempotentElem.eq]
  have huq : (1 - (q - lam⁻¹ • z)) * q = lam⁻¹ • z := by
    rw [sub_mul, one_mul, sub_mul, hq.isIdempotentElem.eq, smul_mul_assoc, hzq]
    abel
  let U := hu.unit
  have hU : (U : Limit) = 1 - (q - lam⁻¹ • z) := hu.unit_spec
  have hqexpr : q = (↑(U⁻¹) : Limit) * (lam⁻¹ • z) := by
    calc
      q = (↑(U⁻¹) : Limit) * ((U : Limit) * q) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = (↑(U⁻¹) : Limit) * (lam⁻¹ • z) := by rw [hU, huq]
  refine ⟨N, ?_⟩
  rw [show rootFlag N = q by rfl, hqexpr, Algebra.smul_def]
  exact I.mul_mem_left (↑(U⁻¹) : Limit) _
    (I.mul_mem_left (algebraMap ℂ Limit lam⁻¹) z hzI)

noncomputable instance limitIsSimpleRing : IsSimpleRing Limit :=
  IsSimpleRing.of_eq_bot_or_eq_top fun I => by
    by_cases hI : I = ⊥
    · exact Or.inl hI
    · right
      obtain ⟨x, hxI, hx⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
      have hx0 : x ≠ 0 := by simpa using hx
      obtain ⟨n, hflagI⟩ := exists_rootFlag_mem_of_ne_zero_mem I hx0 hxI
      let J : TwoSidedIdeal (Stage n) := TwoSidedIdeal.comap (ofStage n).toRingHom I
      have hpJ : rootProjection n ∈ J := by
        exact TwoSidedIdeal.mem_comap (ofStage n).toRingHom |>.2 hflagI
      have honeJ : (1 : Stage n) ∈ J :=
        IsSimpleRing.one_mem_of_ne_zero_mem J (rootProjection_ne_zero n) hpJ
      apply TwoSidedIdeal.eq_top
      have honeI : (1 : Limit) ∈ I := by
        have := TwoSidedIdeal.mem_comap (ofStage n).toRingHom |>.1 honeJ
        rw [← (ofStage n).map_one]
        exact this
      exact honeI

/-- The completed CAR algebra is simple in the stipulated closed-two-sided-ideal sense. -/
theorem isSimpleCStarAlgebra_limit : MathlibAnnex.CStarAlgebra.IsSimpleCStarAlgebra Limit := by
  constructor
  · infer_instance
  · intro I _
    exact eq_bot_or_eq_top I

end MathlibAnnex.CStarAlgebra.CAR
