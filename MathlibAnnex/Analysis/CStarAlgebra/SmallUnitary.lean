import MathlibAnnex.Analysis.CStarAlgebra.InvariantExponential
import MathlibAnnex.Analysis.InnerProductSpace.TwoVectorUnitary
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected

set_option autoImplicit false

noncomputable section

open NormedSpace
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

noncomputable def zeroExtension
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (T : E →L[ℂ] E) : H →L[ℂ] H :=
  E.subtypeL.comp (T.comp E.orthogonalProjectionOnto)

theorem zeroExtension_apply_of_mem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (T : E →L[ℂ] E) {x : H} (hx : x ∈ E) :
    zeroExtension E T x = (T ⟨x, hx⟩ : E) := by
  simp only [zeroExtension, ContinuousLinearMap.comp_apply]
  rw [show E.orthogonalProjectionOnto x = ⟨x, hx⟩ by
    simpa using E.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hx⟩]
  rfl

theorem mapsTo_zeroExtension
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (T : E →L[ℂ] E) : Set.MapsTo (zeroExtension E T) E E := by
  intro x hx
  rw [zeroExtension_apply_of_mem E T hx]
  exact (T ⟨x, hx⟩).property

theorem isSelfAdjoint_zeroExtension
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    [CompleteSpace E] (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (zeroExtension E T) := by
  rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint]
  have hadj : ContinuousLinearMap.adjoint T = T := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hT
  simp [zeroExtension, ContinuousLinearMap.adjoint_comp,
    E.adjoint_subtypeL, E.adjoint_orthogonalProjectionOnto,
    hadj]
  rw [ContinuousLinearMap.comp_assoc]

theorem norm_zeroExtension_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (T : E →L[ℂ] E) : ‖zeroExtension E T‖ ≤ ‖T‖ := by
  dsimp [zeroExtension]
  calc
    _ ≤ ‖E.subtypeL‖ * ‖T.comp E.orthogonalProjectionOnto‖ :=
      E.subtypeL.opNorm_comp_le _
    _ ≤ 1 * ‖T.comp E.orthogonalProjectionOnto‖ := by
      gcongr
      exact E.norm_subtypeL_le
    _ ≤ 1 * (‖T‖ * ‖E.orthogonalProjectionOnto‖) := by
      gcongr
      exact T.opNorm_comp_le E.orthogonalProjectionOnto
    _ ≤ 1 * (‖T‖ * 1) := by
      gcongr
      exact E.orthogonalProjectionOnto_norm_le
    _ = ‖T‖ := by ring

theorem exp_zeroExtension_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    [CompleteSpace E] [Nontrivial E] [IsTopologicalRing (E →L[ℂ] E)]
    (T : E →L[ℂ] E) (x : E) :
    exp (zeroExtension E T) (x : H) = (exp T x : H) := by
  have hpow (n : ℕ) (y : E) :
      ((zeroExtension E T) ^ n) (y : H) = ((T ^ n) y : H) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ']
      change zeroExtension E T (((zeroExtension E T) ^ n) (y : H)) =
        (T ((T ^ n) y) : E)
      rw [ih, zeroExtension_apply_of_mem]
  let ev : (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H (x : H)
  let evE : (E →L[ℂ] E) →L[ℂ] E := ContinuousLinearMap.apply ℂ E x
  have hHsum := (expSeries_hasSum_exp (𝕂 := ℂ) (zeroExtension E T)).map ev ev.continuous
  have hEsumE := (expSeries_hasSum_exp (𝕂 := ℂ) T).map evE evE.continuous
  have hEsum := hEsumE.map E.subtypeL E.subtypeL.continuous
  apply HasSum.unique hHsum
  convert hEsum using 1
  · funext n
    simp only [ev, Function.comp_apply, ContinuousLinearMap.apply_apply,
      expSeries_apply_eq, map_smul, evE]
    rw [hpow n x]
    rfl
  · rfl

set_option maxHeartbeats 800000 in
/-- In an irreducible representation, sufficiently close unit vectors are
carried exactly by a unitary of the represented algebra which is uniformly
close to the identity. -/
theorem StarAlgHom.exists_unitary_apply_eq_and_norm_sub_one_lt
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta > 0, ∀ (xi eta : H), ‖xi‖ = 1 → ‖eta‖ = 1 →
      ‖xi - eta‖ < delta →
      ∃ v : unitary A,
        pi (v : A) xi = eta ∧ ‖(v : A) - 1‖ < epsilon := by
  have hexpContinuous :
      ContinuousAt (selfAdjoint.expUnitary : selfAdjoint A → unitary A) 0 :=
    selfAdjoint.continuous_expUnitary.continuousAt
  rw [Metric.continuousAt_iff] at hexpContinuous
  obtain ⟨gamma, hgamma, hexp⟩ := hexpContinuous epsilon hepsilon
  let f : ℝ → ℝ := fun t => Real.arccos (1 - t ^ 2 / 2)
  have hf : Continuous f := by
    fun_prop
  have hf0 : f 0 = 0 := by simp [f]
  have hfContinuous : ContinuousAt f 0 := hf.continuousAt
  rw [Metric.continuousAt_iff] at hfContinuous
  obtain ⟨r, hr, harg⟩ := hfContinuous (gamma / 2) (half_pos hgamma)
  refine ⟨min r 2, by positivity, ?_⟩
  intro xi eta hxi heta hdist
  let E : Submodule ℂ H := Submodule.span ℂ {xi, eta}
  letI : FiniteDimensional ℂ E :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite {xi, eta})
  letI : E.HasOrthogonalProjection := inferInstance
  have hxiE : xi ∈ E := Submodule.subset_span (Set.mem_insert xi {eta})
  have hetaE : eta ∈ E := Submodule.subset_span (Set.mem_insert_of_mem xi (Set.mem_singleton eta))
  let xiE : E := ⟨xi, hxiE⟩
  let etaE : E := ⟨eta, hetaE⟩
  have hxiEne : xiE ≠ 0 := by
    intro hzero
    have : xi = 0 := congrArg Subtype.val hzero
    rw [this, norm_zero] at hxi
    norm_num at hxi
  letI : Nontrivial E := ⟨⟨xiE, 0, hxiEne⟩⟩
  letI : NormedRing (E →L[ℂ] E) := ContinuousLinearMap.toNormedRing
  obtain ⟨u, huxi, hunorm⟩ :=
    MathlibAnnex.Analysis.InnerProductSpace.exists_unitary_apply_eq_and_norm_sub_one_eq
      xiE etaE (by simpa [xiE] using hxi) (by simpa [etaE] using heta)
  have hur : ‖(u : E →L[ℂ] E) - 1‖ < r := by
    rw [hunorm]
    exact hdist.trans_le (min_le_left _ _)
  have huTwo : ‖(u : E →L[ℂ] E) - 1‖ < 2 := by
    rw [hunorm]
    exact hdist.trans_le (min_le_right _ _)
  let t : selfAdjoint (E →L[ℂ] E) := Unitary.argSelfAdjoint u
  have htSmall : ‖t‖ < gamma / 2 := by
    have harg' := harg (x := ‖(u : E →L[ℂ] E) - 1‖) (by
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hur)
    rw [Unitary.norm_argSelfAdjoint huTwo]
    simpa [f, hf0, Real.dist_eq, abs_of_nonneg (Real.arccos_nonneg _)] using harg'
  let T : H →L[ℂ] H := zeroExtension E (t : E →L[ℂ] E)
  have hTself : IsSelfAdjoint T :=
    isSelfAdjoint_zeroExtension E (t : E →L[ℂ] E) t.property
  have hTmap : Set.MapsTo T E E :=
    mapsTo_zeroExtension E (t : E →L[ℂ] E)
  obtain ⟨h, hhself, hhnorm, hheq⟩ :=
    exists_selfAdjoint_norm_le_two_mul_and_eq_on pi hpi E T hTself
  let hs : selfAdjoint A := ⟨h, hhself⟩
  let v : unitary A := selfAdjoint.expUnitary hs
  refine ⟨v, ?_, ?_⟩
  · calc
      pi (v : A) xi = exp (Complex.I • T) xi :=
        MathlibAnnex.Analysis.CStarAlgebra.StarAlgHom.expUnitary_apply_eq_of_eqOn_of_mapsTo
          pi hs T E hheq hTmap hxiE
      _ = (exp (Complex.I • (t : E →L[ℂ] E)) xiE : E) := by
        have hsmul : Complex.I • T =
            zeroExtension E (Complex.I • (t : E →L[ℂ] E)) := by
          ext z
          simp [T, zeroExtension, ContinuousLinearMap.comp_apply]
        rw [hsmul, exp_zeroExtension_apply E (Complex.I • (t : E →L[ℂ] E)) xiE]
      _ = eta := by
        have hlog : selfAdjoint.expUnitary t = u := expUnitary_argSelfAdjoint huTwo
        have happ := congrArg (fun q : unitary (E →L[ℂ] E) =>
          (q : E →L[ℂ] E) xiE) hlog
        rw [selfAdjoint.expUnitary_coe] at happ
        exact congrArg Subtype.val (happ.trans huxi)
  · have hhsSmall : ‖hs‖ < gamma := by
      calc
        ‖hs‖ = ‖h‖ := rfl
        _ ≤ 2 * ‖T‖ := hhnorm
        _ ≤ 2 * ‖(t : E →L[ℂ] E)‖ := by
          gcongr
          exact norm_zeroExtension_le E (t : E →L[ℂ] E)
        _ = 2 * ‖t‖ := rfl
        _ < gamma := by linarith
    have hvSmall := hexp (x := hs) (by
      simpa [Subtype.dist_eq, dist_eq_norm] using hhsSmall)
    simpa [v, hs, Subtype.dist_eq, dist_eq_norm] using hvSmall

end MathlibAnnex.Analysis.CStarAlgebra
