import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import MathlibAnnex.Analysis.InnerProductSpace.GramUnitary

set_option autoImplicit false

noncomputable section

open NormedSpace

namespace MathlibAnnex.Analysis.InnerProductSpace

theorem exp_smul_idempotent_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (P : H →L[ℂ] H) (hP : P * P = P) (c : ℂ) (x : H) :
    exp (c • P) x = x + (Complex.exp c - 1) • P x := by
  have hPP (y : H) : P (P y) = P y := by
    have := congrArg (fun Q : H →L[ℂ] H => Q y) hP
    simpa [mul_apply_eq_comp] using this
  have hpow (n : ℕ) : ((c • P) ^ (n + 1)) x = c ^ (n + 1) • P x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      change (c • P) (((c • P) ^ (n + 1)) x) = _
      rw [ih]
      simp only [ContinuousLinearMap.smul_apply, map_smul, hPP, smul_smul,
        pow_succ']
      congr 1
      ring
  let ev : (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H x
  let L : ℂ →L[ℂ] H :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (P x)
  have hop := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) (c • P)).map
    ev ev.continuous
  have hscalar := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) c).map
    L L.continuous
  have hsingle := hasSum_ite_eq 0 (x - P x)
  apply HasSum.unique hop
  convert hscalar.add hsingle using 1
  · funext n
    rcases n with _ | n
    · simp [ev, L, NormedSpace.expSeries]
    · simp only [ev, L, Function.comp_apply, ContinuousLinearMap.apply_apply,
        NormedSpace.expSeries_apply_eq, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
      rw [hpow n]
      simp only [Nat.succ_ne_zero, if_false, add_zero, smul_smul]
      congr 1
  · rw [← Complex.exp_eq_exp_ℂ]
    simp [L, sub_smul]
    abel

theorem exp_pi_mul_involutionProjection_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (U : H ≃ₗᵢ[ℂ] H) (hU : ∀ x, U (U x) = x) (x : H) :
    exp (((Real.pi : ℂ) * Complex.I) • U.involutionProjection) x = U x := by
  rw [exp_smul_idempotent_apply U.involutionProjection
    (U.isStarProjection_involutionProjection hU).isIdempotentElem]
  rw [Complex.exp_pi_mul_I]
  simp [LinearIsometryEquiv.involutionProjection_apply]
  module

end MathlibAnnex.Analysis.InnerProductSpace
