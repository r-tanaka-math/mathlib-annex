import MathlibAnnex.Analysis.CStarAlgebra.CAR.CornerLift
import MathlibAnnex.Analysis.CStarAlgebra.CAR.StagePurification
import MathlibAnnex.Analysis.CStarAlgebra.SmallUnitary
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Adapters
import MathlibAnnex.Analysis.InnerProductSpace.InvolutionExponential

set_option autoImplicit false

noncomputable section

open NormedSpace
open scoped CStarAlgebra
open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

namespace MathlibAnnex.CStarAlgebra.CAR

abbrev rootCornerSubspace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (rho : Representation Limit H) (n : ℕ) : Submodule ℂ H :=
  LinearMap.range (rho (limitMatrixUnit n 0 0)).toLinearMap

theorem representation_liftedCornerExponential_apply_of_root
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (rho : Representation Limit H) (n : ℕ)
    (h : selfAdjoint Limit)
    (heh : limitMatrixUnit n 0 0 * (h : Limit) = h)
    (hhe : (h : Limit) * limitMatrixUnit n 0 0 = h)
    (x : H) (hx : rho (limitMatrixUnit n 0 0) x = x) :
    rho (liftedCornerExponential n h heh hhe : Limit) x =
      rho (cornerExponential n h) x := by
  let z := cornerExponential n h
  have hz := isRootCornerUnitary_cornerExponential n h heh hhe
  change rho (cornerLift n z) x = rho z x
  rw [representation_cornerLift_apply]
  rw [Finset.sum_eq_single (0 : Fin (2 ^ n))]
  · simp only [z]
    rw [show rho (limitMatrixUnit n 0 0) x = x by exact hx]
    change rho (limitMatrixUnit n 0 0) (rho (cornerExponential n h) x) = _
    rw [← mul_apply_eq_comp, ← map_mul, hz.2.2.1]
  · intro i _ hi
    have h0i : rho (limitMatrixUnit n 0 i) x = 0 := by
      rw [← hx, ← mul_apply_eq_comp, ← map_mul]
      simp [hi]
    simp [h0i]
  · simp

set_option maxHeartbeats 800000 in
theorem exists_rootCornerSupported_exponential_apply_eq_involution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (n d : ℕ) (v : Fin d → rootCornerSubspace rho n)
    (U : rootCornerSubspace rho n ≃ₗᵢ[ℂ] rootCornerSubspace rho n)
    (hU : ∀ x, U (U x) = x) :
    ∃ h : selfAdjoint Limit,
      limitMatrixUnit n 0 0 * (h : Limit) = h ∧
      (h : Limit) * limitMatrixUnit n 0 0 = h ∧
      ∀ i, rho (cornerExponential n h) (v i : H) = (U (v i) : H) := by
  let e : Limit := limitMatrixUnit n 0 0
  let K : Submodule ℂ H := rootCornerSubspace rho n
  have hroot : IsStarProjection (rho e) := by
    exact (isStarProjection_limitMatrixUnit_zero_zero n).map rho
  letI : CompleteSpace K := IsComplete.completeSpace_coe
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      hroot.isIdempotentElem).isComplete
  have hKnot : ¬ FiniteDimensional ℂ K := by
    simpa [K, e, rootCornerSubspace] using
      not_finiteDimensional_range_rootCorner rho
        ((MathlibAnnex.Analysis.CStarAlgebra.Representation.isIrreducible_iff_starAlgHom rho).mpr
          hrho) n
  letI : Nontrivial K := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply hKnot
    letI : Subsingleton K := hsub
    exact FiniteDimensional.of_rank_eq_zero (rank_subsingleton' ℂ K)
  letI : NormedRing (K →L[ℂ] K) := ContinuousLinearMap.toNormedRing
  letI : K.HasOrthogonalProjection := by
    simpa [K] using
      (ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
        hroot.isIdempotentElem)
  let P : K →L[ℂ] K := U.involutionProjection
  have hPstar : IsStarProjection P := U.isStarProjection_involutionProjection hU
  let PH : H →L[ℂ] H :=
    MathlibAnnex.Analysis.CStarAlgebra.zeroExtension K P
  let T : H →L[ℂ] H := (Real.pi : ℂ) • PH
  let S : Set H :=
    Set.range (fun i => (v i : H)) ∪ Set.range (fun i => (U (v i) : H))
  let E : Submodule ℂ H := Submodule.span ℂ S
  letI : FiniteDimensional ℂ E :=
    FiniteDimensional.span_of_finite ℂ
      ((Set.finite_range fun i => (v i : H)).union
        (Set.finite_range fun i => (U (v i) : H)))
  letI : E.HasOrthogonalProjection := inferInstance
  have hKfix (x : K) : rho e (x : H) = (x : H) := by
    exact (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap
        hroot.isIdempotentElem)).mp x.property
  have hvE (i : Fin d) : (v i : H) ∈ E :=
    Submodule.subset_span (Or.inl (Set.mem_range_self i))
  have hUvE (i : Fin d) : (U (v i) : H) ∈ E :=
    Submodule.subset_span (Or.inr (Set.mem_range_self i))
  have hEroot : ∀ x : H, x ∈ E → rho e x = x := by
    intro x hx
    refine Submodule.span_induction
      (p := fun x _ => rho e x = x) ?_ (by simp) ?_ ?_ hx
    · intro x hx
      rcases hx with hx | hx
      · obtain ⟨i, rfl⟩ := hx
        exact hKfix (v i)
      · obtain ⟨i, rfl⟩ := hx
        exact hKfix (U (v i))
    · intro x y _ _ hx hy
      simpa using congrArg₂ (· + ·) hx hy
    · intro c x _ hx
      simpa using congrArg (fun y => c • y) hx
  have hPHself : IsSelfAdjoint PH :=
    MathlibAnnex.Analysis.CStarAlgebra.isSelfAdjoint_zeroExtension
      K P hPstar.isSelfAdjoint
  have hTself : IsSelfAdjoint T := by
    dsimp only [T]
    rw [isSelfAdjoint_iff, star_smul, hPHself.star_eq]
    simp
  have hTroot : rho e * T = T := by
    apply ContinuousLinearMap.ext
    intro x
    change rho e (T x) = T x
    exact hKfix ⟨T x, by
      dsimp only [T]
      rw [ContinuousLinearMap.smul_apply]
      apply K.smul_mem
      dsimp [PH, MathlibAnnex.Analysis.CStarAlgebra.zeroExtension]
      exact (P (K.orthogonalProjectionOnto x)).property⟩
  have hTmap : Set.MapsTo T E E := by
    intro x hx
    refine Submodule.span_induction
      (p := fun x _ => T x ∈ E) ?_ (by simp [T]) ?_ ?_ hx
    · intro x hx
      rcases hx with hx | hx
      · obtain ⟨i, rfl⟩ := hx
        rw [show T (v i : H) =
            (Real.pi : ℂ) • ((2 : ℂ)⁻¹ •
              ((v i : H) - (U (v i) : H))) by
          simp [T, PH, P,
            MathlibAnnex.Analysis.CStarAlgebra.zeroExtension_apply_of_mem,
            LinearIsometryEquiv.involutionProjection_apply, smul_smul]
          module]
        exact E.smul_mem _ (E.smul_mem _ (E.sub_mem (hvE i) (hUvE i)))
      · obtain ⟨i, rfl⟩ := hx
        rw [show T (U (v i) : H) =
            (Real.pi : ℂ) • ((2 : ℂ)⁻¹ •
              ((U (v i) : H) - (v i : H))) by
          simp [T, PH, P,
            MathlibAnnex.Analysis.CStarAlgebra.zeroExtension_apply_of_mem,
            LinearIsometryEquiv.involutionProjection_apply, hU, smul_smul]
          module]
        exact E.smul_mem _ (E.smul_mem _ (E.sub_mem (hUvE i) (hvE i)))
    · intro x y _ _ hx hy
      simpa using E.add_mem hx hy
    · intro c x _ hx
      simpa using E.smul_mem c hx
  obtain ⟨h, -, heh, hhe, hexp⟩ :=
    exists_rootCornerSupported_exponential_eq_on
      rho hrho n E hEroot T hTself hTroot hTmap
  refine ⟨h, heh, hhe, fun i => ?_⟩
  rw [hexp (v i : H) (hvE i)]
  have hsmul : Complex.I • T =
      ((Real.pi : ℂ) * Complex.I) • PH := by
    dsimp only [T]
    module
  rw [hsmul]
  have hzero : ((Real.pi : ℂ) * Complex.I) • PH =
      MathlibAnnex.Analysis.CStarAlgebra.zeroExtension K
        (((Real.pi : ℂ) * Complex.I) • P) := by
    ext x
    simp [PH, MathlibAnnex.Analysis.CStarAlgebra.zeroExtension, smul_smul]
  rw [hzero, MathlibAnnex.Analysis.CStarAlgebra.exp_zeroExtension_apply
    K (((Real.pi : ℂ) * Complex.I) • P) (v i)]
  exact congrArg Subtype.val
    (MathlibAnnex.Analysis.InnerProductSpace.exp_pi_mul_involutionProjection_apply
      U hU (v i))

/-- The ambient unitary obtained by amplifying the same corner exponential
acts as the prescribed involution on the selected root-corner family. -/
theorem exists_liftedCornerExponential_apply_eq_involution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (n d : ℕ) (v : Fin d → rootCornerSubspace rho n)
    (U : rootCornerSubspace rho n ≃ₗᵢ[ℂ] rootCornerSubspace rho n)
    (hU : ∀ x, U (U x) = x) :
    ∃ (h : selfAdjoint Limit)
      (heh : limitMatrixUnit n 0 0 * (h : Limit) = h)
      (hhe : (h : Limit) * limitMatrixUnit n 0 0 = h),
      ∀ i, rho (liftedCornerExponential n h heh hhe : Limit) (v i : H) =
        (U (v i) : H) := by
  obtain ⟨h, heh, hhe, hcorner⟩ :=
    exists_rootCornerSupported_exponential_apply_eq_involution
      rho hrho n d v U hU
  refine ⟨h, heh, hhe, fun i => ?_⟩
  rw [representation_liftedCornerExponential_apply_of_root
    rho n h heh hhe (v i) ?_]
  · exact hcorner i
  · exact (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap
        ((isStarProjection_limitMatrixUnit_zero_zero n).map rho).isIdempotentElem)).mp
      (v i).property

end MathlibAnnex.CStarAlgebra.CAR
