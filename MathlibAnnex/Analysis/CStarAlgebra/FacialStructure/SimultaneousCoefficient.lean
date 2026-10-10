/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.SimultaneousUnitary
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.RepresentationEquivalence
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.NormAttainment

/-!
# Simultaneous coefficient phases and the l1 norm

One original-algebra contraction realizes all phases, with the phase multiplying
the source (the linear slot). The pinned scalar phase lemma also covers zero
coefficients: its equation is c * alpha = norm alpha. For nonzero alpha this is
precisely the conjugate phase, never the unconjugated alpha / norm alpha.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w t
variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- All unit phases of finitely many inequivalent unit coefficients are
realized by ONE contraction in the original algebra. -/
theorem exists_norm_le_one_forall_matrixCoefficient_eq
    {I : Type t} [Fintype I] {H : I → Type v}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i j, i ≠ j → ¬ (pi i).UnitaryEquivalent (pi j))
    (x y : ∀ i, H i) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (c : I → ℂ) (hc : ∀ i, ‖c i‖ = 1) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ ∀ i, matrixCoefficient (pi i) (x i) (y i) a = c i := by
  obtain ⟨a, ha, happ⟩ := exists_norm_le_one_forall_apply_eq pi hirr hne x
    (fun i => c i • y i) hx (fun i => by simp only [norm_smul, hc i, hy i, one_mul])
  refine ⟨a, ha, fun i => ?_⟩
  rw [matrixCoefficient_apply, happ i, inner_smul_right,
    inner_self_eq_one_of_norm_eq_one (hy i), mul_one]

variable {H : Type v} {K : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The two-representation witness allows different Hilbert universes.
Actual isometric conjugation, not an identification of types, makes a finite family. -/
theorem exists_norm_le_one_matrixCoefficient_eq_and_eq_of_not_unitaryEquivalent
    (pi : NonUnitalCStarRepresentation A H) (sigma : NonUnitalCStarRepresentation A K)
    (hpi : pi.IsIrreducible) (hsigma : sigma.IsIrreducible) (hne : ¬ pi.UnitaryEquivalent sigma)
    (x y : H) (z w : K) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (c d : ℂ) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ matrixCoefficient pi x y a = c ∧ matrixCoefficient sigma z w a = d := by
  let H' := ULift.{w} H
  let K' := ULift.{v} K
  letI : InnerProductSpace ℂ H' :=
    { inner := fun x y => inner ℂ x.down y.down
      norm_sq_eq_re_inner := fun x => norm_sq_eq_re_inner x.down
      conj_inner_symm := fun x y => inner_conj_symm x.down y.down
      add_left := fun x y z => inner_add_left x.down y.down z.down
      smul_left := fun x y c => inner_smul_left x.down y.down c }
  letI : InnerProductSpace ℂ K' :=
    { inner := fun x y => inner ℂ x.down y.down
      norm_sq_eq_re_inner := fun x => norm_sq_eq_re_inner x.down
      conj_inner_symm := fun x y => inner_conj_symm x.down y.down
      add_left := fun x y z => inner_add_left x.down y.down z.down
      smul_left := fun x y c => inner_smul_left x.down y.down c }
  let U : H ≃ₗᵢ[ℂ] H' := (LinearIsometryEquiv.ulift ℂ H).symm
  let V : K ≃ₗᵢ[ℂ] K' := (LinearIsometryEquiv.ulift ℂ K).symm
  let L : Bool → Type (max v w) := fun b => match b with | false => H' | true => K'
  letI (b : Bool) : NormedAddCommGroup (L b) := match b with
    | false => inferInstance
    | true => inferInstance
  letI (b : Bool) : InnerProductSpace ℂ (L b) := match b with
    | false => inferInstance
    | true => inferInstance
  letI (b : Bool) : CompleteSpace (L b) := match b with
    | false => inferInstance
    | true => inferInstance
  let r : ∀ b, NonUnitalCStarRepresentation A (L b) := fun b => match b with
    | false => conj pi U
    | true => conj sigma V
  let p : ∀ b, L b := fun b => match b with | false => U x | true => V z
  let q : ∀ b, L b := fun b => match b with | false => U y | true => V w
  let e : Bool → ℂ := fun b => match b with | false => c | true => d
  have hirr : ∀ b, (r b).IsIrreducible := by
    intro b
    cases b
    · exact isIrreducible_conj pi U hpi
    · exact isIrreducible_conj sigma V hsigma
  have hnot : ¬ (r false).UnitaryEquivalent (r true) :=
    fun h => hne ((unitaryEquivalent_conj_iff pi sigma U V).1 h)
  have hpair : ∀ b k, b ≠ k → ¬ (r b).UnitaryEquivalent (r k) := by
    intro b k hbk
    cases b <;> cases k
    · exact (hbk rfl).elim
    · exact hnot
    · exact fun h => hnot h.symm
    · exact (hbk rfl).elim
  have hp : ∀ b, ‖p b‖ = 1 := by
    intro b
    cases b
    · exact (U.norm_map x).trans hx
    · exact (V.norm_map z).trans hz
  have hq : ∀ b, ‖q b‖ = 1 := by
    intro b
    cases b
    · exact (U.norm_map y).trans hy
    · exact (V.norm_map w).trans hw
  have he : ∀ b, ‖e b‖ = 1 := by
    intro b
    cases b
    · exact hc
    · exact hd
  obtain ⟨a, ha, happ⟩ := exists_norm_le_one_forall_matrixCoefficient_eq r hirr hpair p q hp hq e he
  refine ⟨a, ha, ?_, ?_⟩
  · simpa only [r, p, q, e, matrixCoefficient_conj] using happ false
  · simpa only [r, p, q, e, matrixCoefficient_conj] using happ true

/-- Inequivalent unit coefficients span an isometric l1 pair. Zero scalar
coefficients are included in the pinned phase lemma and in this equality. -/
theorem norm_smul_add_matrixCoefficient_of_not_unitaryEquivalent
    (pi : NonUnitalCStarRepresentation A H) (sigma : NonUnitalCStarRepresentation A K)
    (hpi : pi.IsIrreducible) (hsigma : sigma.IsIrreducible) (hne : ¬ pi.UnitaryEquivalent sigma)
    (x y : H) (z w : K) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (alpha beta : ℂ) :
    ‖alpha • matrixCoefficient pi x y + beta • matrixCoefficient sigma z w‖ =
      ‖alpha‖ + ‖beta‖ := by
  let f := matrixCoefficient pi x y
  let g := matrixCoefficient sigma z w
  have hf : ‖f‖ = 1 := by simp only [f, norm_matrixCoefficient_of_isIrreducible pi hpi, hx, hy, one_mul]
  have hg : ‖g‖ = 1 := by simp only [g, norm_matrixCoefficient_of_isIrreducible sigma hsigma, hz, hw, one_mul]
  apply le_antisymm
  · calc
      ‖alpha • f + beta • g‖ ≤ ‖alpha • f‖ + ‖beta • g‖ := norm_add_le _ _
      _ = ‖alpha‖ + ‖beta‖ := by rw [norm_smul, norm_smul, hf, hg, mul_one, mul_one]
  · obtain ⟨c, hc, halpha⟩ := Complex.exists_norm_eq_mul_self alpha
    obtain ⟨d, hd, hbeta⟩ := Complex.exists_norm_eq_mul_self beta
    obtain ⟨a, ha, hfa, hga⟩ :=
      exists_norm_le_one_matrixCoefficient_eq_and_eq_of_not_unitaryEquivalent
        pi sigma hpi hsigma hne x y z w hx hy hz hw c d hc hd
    have hvalue : (alpha • f + beta • g) a = ((‖alpha‖ + ‖beta‖ : ℝ) : ℂ) := by
      change alpha * f a + beta * g a = _
      rw [hfa, hga, mul_comm alpha c, mul_comm beta d, ← halpha, ← hbeta]
      exact (Complex.ofReal_add _ _).symm
    calc
      ‖alpha‖ + ‖beta‖ = ‖(alpha • f + beta • g) a‖ := by
        rw [hvalue, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      _ ≤ ‖alpha • f + beta • g‖ * ‖a‖ := (alpha • f + beta • g).le_opNorm a
      _ ≤ ‖alpha • f + beta • g‖ := mul_le_of_le_one_right (norm_nonneg _) ha

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
