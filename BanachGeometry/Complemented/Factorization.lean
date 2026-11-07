import BanachGeometry.AlmostIsometric.PointedBiLip
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Split embeddings and perturbation repair, with all maps explicit.
The small-norm condition is an ordinary local premise. FinitePerturbation
and Localization apply these algebraic lemmas using the shift/tail estimates;
Corner supplies the joint corner bound. -/

noncomputable section
namespace BanachGeometry
namespace Factorization

variable {E V W : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem linearCopy_of_split (J : E →L[ℝ] V) (P : V →L[ℝ] E)
    (hPJ : P.comp J = ContinuousLinearMap.id ℝ E) : ContainsLinearCopy E V := by
  refine ⟨J, (‖P‖ + 1)⁻¹, inv_pos.mpr (by positivity), ?_⟩
  intro x
  have hx : P (J x) = x := congrArg (fun f : E →L[ℝ] E => f x) hPJ
  have hb : ‖x‖ ≤ ‖P‖ * ‖J x‖ := by
    calc
      ‖x‖ = ‖P (J x)‖ := congrArg norm hx.symm
      _ ≤ ‖P‖ * ‖J x‖ := P.le_opNorm _
  have hd : 0 < ‖P‖ + 1 := by positivity
  have hdiv : ‖x‖ / (‖P‖ + 1) ≤ ‖J x‖ :=
    (div_le_iff₀ hd).2 (by nlinarith [norm_nonneg (J x)])
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

theorem projection_idempotent (J : E →L[ℝ] V) (P : V →L[ℝ] E)
    (hPJ : P.comp J = ContinuousLinearMap.id ℝ E) :
    (J.comp P).comp (J.comp P) = J.comp P := by
  ext x
  have h : P (J (P x)) = P x := congrArg (fun f : E →L[ℝ] E => f (P x)) hPJ
  exact congrArg J h

/-- The common complemented-copy predicate is invariant under Banach isomorphism. -/
theorem complemented_transport (e : V ≃L[ℝ] W)
    (hV : ContainsComplementedCopy E V) : ContainsComplementedCopy E W := by
  obtain ⟨J, P, hPJ⟩ := hV
  refine ⟨e.toContinuousLinearMap.comp J, P.comp e.symm.toContinuousLinearMap, ?_⟩
  ext x
  change P (e.symm (e (J x))) = x
  rw [e.symm_apply_apply]
  exact congrArg (fun f : E →L[ℝ] E => f x) hPJ

theorem nonisomorphic_of_complemented_distinction
    (hV : ContainsComplementedCopy E V) (hW : ¬ ContainsComplementedCopy E W) :
    IsEmpty (V ≃L[ℝ] W) :=
  ⟨fun e => hW (complemented_transport e hV)⟩

/-- Neumann repair of an approximate left inverse. Completeness is an ordinary
space hypothesis; no inverse or unproved mathematical proposition is an instance. -/
theorem repair_left_inverse [CompleteSpace E]
    (J : E →L[ℝ] V) (P : V →L[ℝ] E) (Δ : E →L[ℝ] E)
    (hΔ : ‖Δ‖ < 1) (hPJ : P.comp J = ContinuousLinearMap.id ℝ E - Δ) :
    ∃ R : V →L[ℝ] E, R.comp J = ContinuousLinearMap.id ℝ E := by
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hΔ
  refine ⟨(↑(u⁻¹) : E →L[ℝ] E).comp P, ?_⟩
  have hprod : P.comp J = (↑u : E →L[ℝ] E) := hPJ.trans hu.symm
  ext x
  change (↑(u⁻¹) : E →L[ℝ] E) (P (J x)) = x
  have hprod_apply : P (J x) = (↑u : E →L[ℝ] E) x :=
    congrArg (fun f : E →L[ℝ] E => f x) hprod
  rw [hprod_apply]
  have hinv : (↑(u⁻¹) : E →L[ℝ] E) * (↑u : E →L[ℝ] E) = 1 := by simp
  exact congrArg (fun f : E →L[ℝ] E => f x) hinv

/-- Remove one small factor from a decomposition of the identity. This is the
algebraic core of R6 Lemma 5.3, before the shift/tail estimate supplies hsmall. -/
theorem discard_small_factor [CompleteSpace E]
    (J : E →L[ℝ] V) (P : V →L[ℝ] E)
    (K : E →L[ℝ] W) (Q : W →L[ℝ] E)
    (hsplit : P.comp J + Q.comp K = ContinuousLinearMap.id ℝ E)
    (hsmall : ‖Q.comp K‖ < 1) : ContainsComplementedCopy E V := by
  have hmain : P.comp J = ContinuousLinearMap.id ℝ E - Q.comp K := by
    exact eq_sub_iff_add_eq.mpr hsplit
  obtain ⟨R, hR⟩ := repair_left_inverse J P (Q.comp K) hsmall hmain
  exact ⟨J, R, hR⟩

end Factorization
end BanachGeometry
