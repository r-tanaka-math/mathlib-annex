import MathlibAnnex.Analysis.CStarAlgebra.Kadison
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Exact finite-dimensional self-adjoint interpolation

This file upgrades norm-budget Kadison approximation to exact interpolation on a
finite-dimensional subspace.  The proof converts coordinate errors to a restricted
operator-norm error, corrects the self-adjoint residual on the orthogonal projection,
and sums explicitly controlled geometric corrections.  In particular, it never
assumes that independently selected one-shot approximants converge.
-/

set_option autoImplicit false

open scoped InnerProductSpace CStarAlgebra ENNReal lp
open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

namespace MathlibAnnex.Analysis.CStarAlgebra

theorem norm_comp_starProjection_le_sum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    [FiniteDimensional ℂ E] (D : H →L[ℂ] H) :
    ‖D * E.starProjection‖ ≤
      ∑ i : Fin (Module.finrank ℂ E),
        ‖D ((stdOrthonormalBasis ℂ E i : E) : H)‖ := by
  let b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E :=
    stdOrthonormalBasis ℂ E
  rw [show E.starProjection =
      ∑ i, InnerProductSpace.rankOne ℂ ((b i : E) : H) ((b i : E) : H) by
    exact b.starProjection_eq_sum_rankOne]
  rw [Finset.mul_sum]
  calc
    ‖∑ i, D * InnerProductSpace.rankOne ℂ ((b i : E) : H) ((b i : E) : H)‖ ≤
        ∑ i, ‖D * InnerProductSpace.rankOne ℂ ((b i : E) : H) ((b i : E) : H)‖ :=
      norm_sum_le _ _
    _ = ∑ i, ‖D ((b i : E) : H)‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show D * InnerProductSpace.rankOne ℂ ((b i : E) : H) ((b i : E) : H) =
          InnerProductSpace.rankOne ℂ (D ((b i : E) : H)) ((b i : E) : H) by
        exact InnerProductSpace.comp_rankOne _ _ D]
      have hbnorm : ‖((b i : E) : H)‖ = 1 := b.norm_eq_one i
      rw [InnerProductSpace.norm_rankOne, hbnorm, mul_one]

/-- The self-adjoint residual supported on a projection. -/
def projectionResidual
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (R P : H →L[ℂ] H) : H →L[ℂ] H :=
  R * P + P * R - P * R * P

theorem isSelfAdjoint_projectionResidual
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {R P : H →L[ℂ] H}
    (hR : IsSelfAdjoint R) (hP : IsSelfAdjoint P) :
    IsSelfAdjoint (projectionResidual R P) := by
  rw [IsSelfAdjoint]
  simp only [projectionResidual, star_sub, star_add, star_mul,
    hR.star_eq, hP.star_eq]
  noncomm_ring

theorem projectionResidual_mul
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {R P : H →L[ℂ] H} (hP : P * P = P) :
    projectionResidual R P * P = R * P := by
  simp only [projectionResidual, add_mul, sub_mul, mul_assoc, hP]
  abel

theorem norm_projectionResidual_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {R P : H →L[ℂ] H}
    (hR : IsSelfAdjoint R) (hP : IsSelfAdjoint P) (hPnorm : ‖P‖ ≤ 1) :
    ‖projectionResidual R P‖ ≤ 3 * ‖R * P‖ := by
  have hPR : ‖P * R‖ = ‖R * P‖ := by
    calc
      ‖P * R‖ = ‖star (R * P)‖ := by rw [star_mul, hR.star_eq, hP.star_eq]
      _ = ‖R * P‖ := norm_star _
  have hPRP : ‖P * R * P‖ ≤ ‖R * P‖ := by
    calc
      ‖P * R * P‖ = ‖P * (R * P)‖ := by rw [mul_assoc]
      _ ≤ ‖P‖ * ‖R * P‖ := norm_mul_le _ _
      _ ≤ 1 * ‖R * P‖ := mul_le_mul_of_nonneg_right hPnorm (norm_nonneg _)
      _ = ‖R * P‖ := one_mul _
  calc
    ‖projectionResidual R P‖ ≤ ‖R * P + P * R‖ + ‖P * R * P‖ := by
      exact norm_sub_le (R * P + P * R) (P * R * P)
    _ ≤ (‖R * P‖ + ‖P * R‖) + ‖P * R * P‖ := by
      gcongr
      exact norm_add_le (R * P) (P * R)
    _ ≤ (‖R * P‖ + ‖R * P‖) + ‖R * P‖ := by
      rw [hPR]
      gcongr
    _ = 3 * ‖R * P‖ := by ring

theorem exists_selfAdjoint_norm_le_and_norm_sub_mul_starProjection_lt
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection] [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      ‖(pi a - T) * E.starProjection‖ < epsilon := by
  classical
  let b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E :=
    stdOrthonormalBasis ℂ E
  let delta : ℝ := epsilon / ((Module.finrank ℂ E : ℝ) + 1)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  obtain ⟨a, ha, hanorm, happ⟩ :=
    pi.exists_selfAdjoint_atomic_apply_sub_norm_lt_of_irreducible_norm_le
      hpi (fun i => ((b i : E) : H)) T hT hdelta
  refine ⟨a, ha, hanorm, ?_⟩
  have hcoord : ∀ i : Fin (Module.finrank ℂ E),
      ‖(pi a - T) ((b i : E) : H)‖ < delta := by
    intro i
    have hle := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (atomicRepresentation (fun _ : Fin (Module.finrank ℂ E) => pi) a
          (finiteHilbertSum (fun i => ((b i : E) : H))) -
        diagonal (fun _ : Fin (Module.finrank ℂ E) => T) ‖T‖
          (norm_nonneg T) (fun _ => le_rfl)
          (finiteHilbertSum (fun i => ((b i : E) : H)))) i
    have hpoint :
        ‖(pi a - T) ((b i : E) : H)‖ ≤
          ‖atomicRepresentation (fun _ : Fin (Module.finrank ℂ E) => pi) a
              (finiteHilbertSum (fun i => ((b i : E) : H))) -
            diagonal (fun _ : Fin (Module.finrank ℂ E) => T) ‖T‖
              (norm_nonneg T) (fun _ => le_rfl)
              (finiteHilbertSum (fun i => ((b i : E) : H)))‖ := by
      simpa [sub_apply, atomicRepresentation_apply,
        diagonal_apply, finiteHilbertSum_apply] using hle
    exact hpoint.trans_lt happ
  calc
    ‖(pi a - T) * E.starProjection‖ ≤
        ∑ i : Fin (Module.finrank ℂ E),
          ‖(pi a - T) ((b i : E) : H)‖ :=
      norm_comp_starProjection_le_sum E (pi a - T)
    _ ≤ ∑ _i : Fin (Module.finrank ℂ E), delta := by
      exact Finset.sum_le_sum fun i _ => (hcoord i).le
    _ = (Module.finrank ℂ E : ℝ) * delta := by simp
    _ < epsilon := by
      have hlt : (Module.finrank ℂ E : ℝ) <
          (Module.finrank ℂ E : ℝ) + 1 := by linarith
      calc
        (Module.finrank ℂ E : ℝ) * delta <
            ((Module.finrank ℂ E : ℝ) + 1) * delta :=
          mul_lt_mul_of_pos_right hlt hdelta
        _ = epsilon := by
          dsimp [delta]
          field_simp

private structure InterpolationState
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (n : ℕ) where
  value : A
  isSelfAdjoint : IsSelfAdjoint value
  error_lt : ‖(T - pi value) * E.starProjection‖ < ‖T‖ / 6 / 2 ^ n

private theorem exists_initialState
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection] [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hTnorm : 0 < ‖T‖) :
    ∃ s : InterpolationState pi E T 0, ‖s.value‖ ≤ ‖T‖ := by
  obtain ⟨a, ha, hanorm, happ⟩ :=
    exists_selfAdjoint_norm_le_and_norm_sub_mul_starProjection_lt
      pi hpi E T hT (by positivity : 0 < ‖T‖ / 6)
  refine ⟨⟨a, ha, ?_⟩, hanorm⟩
  have hid : (T - pi a) * E.starProjection = -(pi a - T) * E.starProjection := by
    noncomm_ring
  rw [hid, neg_mul, norm_neg]
  simpa only [pow_zero, div_one] using happ

private theorem exists_nextState
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection] [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hTnorm : 0 < ‖T‖)
    (n : ℕ) (s : InterpolationState pi E T n) :
    ∃ t : InterpolationState pi E T (n + 1),
      IsSelfAdjoint (t.value - s.value) ∧
      ‖t.value - s.value‖ ≤ ‖T‖ / 2 / 2 ^ n := by
  let P : H →L[ℂ] H := E.starProjection
  let R : H →L[ℂ] H := T - pi s.value
  let B : H →L[ℂ] H := projectionResidual R P
  have hP : IsSelfAdjoint P := isSelfAdjoint_starProjection E
  have hR : IsSelfAdjoint R := hT.sub (s.isSelfAdjoint.map pi)
  have hB : IsSelfAdjoint B := isSelfAdjoint_projectionResidual hR hP
  have hBP : B * P = R * P := by
    exact projectionResidual_mul E.isIdempotentElem_starProjection
  have hBnorm : ‖B‖ < ‖T‖ / 2 / 2 ^ n := by
    calc
      ‖B‖ ≤ 3 * ‖R * P‖ :=
        norm_projectionResidual_le hR hP E.starProjection_norm_le
      _ < 3 * (‖T‖ / 6 / 2 ^ n) := by
        gcongr
        exact s.error_lt
      _ = ‖T‖ / 2 / 2 ^ n := by ring
  have heps : 0 < ‖T‖ / 6 / 2 ^ (n + 1) := by positivity
  obtain ⟨c, hc, hcnorm, hcapp⟩ :=
    exists_selfAdjoint_norm_le_and_norm_sub_mul_starProjection_lt
      pi hpi E B hB heps
  let tval : A := s.value + c
  have htself : IsSelfAdjoint tval := s.isSelfAdjoint.add hc
  have hterror : ‖(T - pi tval) * P‖ < ‖T‖ / 6 / 2 ^ (n + 1) := by
    have hid : (T - pi tval) * P = -(pi c - B) * P := by
      calc
        (T - pi tval) * P = (R - pi c) * P := by
          simp only [R, tval, map_add]
          noncomm_ring
        _ = B * P - pi c * P := by rw [sub_mul, ← hBP]
        _ = (B - pi c) * P := by rw [sub_mul]
        _ = -(pi c - B) * P := by noncomm_ring
    rw [hid, neg_mul, norm_neg]
    simpa [P] using hcapp
  refine ⟨⟨tval, htself, ?_⟩, ?_, ?_⟩
  · exact hterror
  · simpa [tval] using hc
  · simpa [tval] using hcnorm.trans hBnorm.le

private noncomputable def initialState
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection] [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hTnorm : 0 < ‖T‖) :
    InterpolationState pi E T 0 :=
  Classical.choose (exists_initialState pi hpi E T hT hTnorm)

private theorem initialState_norm_le
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection] [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hTnorm : 0 < ‖T‖) :
    ‖(initialState pi hpi E T hT hTnorm).value‖ ≤ ‖T‖ :=
  (Classical.choose_spec (exists_initialState pi hpi E T hT hTnorm))

private noncomputable def nextState
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection] [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hTnorm : 0 < ‖T‖)
    (n : ℕ) (s : InterpolationState pi E T n) : InterpolationState pi E T (n + 1) :=
  Classical.choose (exists_nextState pi hpi E T hT hTnorm n s)

private theorem isSelfAdjoint_nextState_sub
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection] [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hTnorm : 0 < ‖T‖)
    (n : ℕ) (s : InterpolationState pi E T n) :
    IsSelfAdjoint
      ((nextState pi hpi E T hT hTnorm n s).value - s.value) :=
  (Classical.choose_spec
    (exists_nextState pi hpi E T hT hTnorm n s)).1

private theorem nextState_sub_norm_le
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection] [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hTnorm : 0 < ‖T‖)
    (n : ℕ) (s : InterpolationState pi E T n) :
    ‖(nextState pi hpi E T hT hTnorm n s).value - s.value‖ ≤
      ‖T‖ / 2 / 2 ^ n :=
  (Classical.choose_spec
    (exists_nextState pi hpi E T hT hTnorm n s)).2

theorem exists_selfAdjoint_norm_le_two_mul_and_sub_mul_starProjection_eq_zero
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection] [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 2 * ‖T‖ ∧
      (T - pi a) * E.starProjection = 0 := by
  classical
  by_cases hTzero : ‖T‖ = 0
  · have hT' : T = 0 := norm_eq_zero.mp hTzero
    refine ⟨0, .zero A, ?_, ?_⟩
    · simp [hTzero]
    · simp [hT']
  have hTnorm : 0 < ‖T‖ := lt_of_le_of_ne (norm_nonneg T) (Ne.symm hTzero)
  let s0 : InterpolationState pi E T 0 :=
    initialState pi hpi E T hT hTnorm
  let s : ∀ n : ℕ, InterpolationState pi E T n := fun n =>
    Nat.rec s0 (fun n t => nextState pi hpi E T hT hTnorm n t) n
  let c : ℕ → A := fun n => (s (n + 1)).value - (s n).value
  have hs0norm : ‖(s 0).value‖ ≤ ‖T‖ := by
    simpa [s, s0] using initialState_norm_le pi hpi E T hT hTnorm
  have hcself (n : ℕ) : IsSelfAdjoint (c n) := by
    simpa [c, s] using
      isSelfAdjoint_nextState_sub pi hpi E T hT hTnorm n (s n)
  have hcnorm (n : ℕ) : ‖c n‖ ≤ ‖T‖ / 2 / 2 ^ n := by
    simpa [c, s] using
      nextState_sub_norm_le pi hpi E T hT hTnorm n (s n)
  have hcsum : Summable c :=
    (summable_geometric_two' ‖T‖).of_norm_bounded hcnorm
  have hcnormsum : Summable (fun n => ‖c n‖) :=
    (summable_geometric_two' ‖T‖).of_nonneg_of_le
      (fun n => norm_nonneg (c n)) hcnorm
  have hspartial (n : ℕ) :
      (s n).value = (s 0).value + ∑ i ∈ Finset.range n, c i := by
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          (s (n + 1)).value = (s n).value + c n := by
            simp only [c]
            abel
          _ = (s 0).value + (∑ i ∈ Finset.range n, c i) + c n := by rw [ih]
          _ = (s 0).value + ∑ i ∈ Finset.range (n + 1), c i := by
            rw [Finset.sum_range_succ]
            abel
  let a : A := (s 0).value + ∑' n, c n
  have hsumself : IsSelfAdjoint (∑' n, c n) := by
    rw [IsSelfAdjoint, tsum_star]
    apply tsum_congr
    intro n
    exact (hcself n).star_eq
  have haself : IsSelfAdjoint a := (s 0).isSelfAdjoint.add hsumself
  have hanorm : ‖a‖ ≤ 2 * ‖T‖ := by
    calc
      ‖a‖ ≤ ‖(s 0).value‖ + ‖∑' n, c n‖ := by
        exact norm_add_le _ _
      _ ≤ ‖T‖ + ∑' n, ‖c n‖ :=
        add_le_add hs0norm (norm_tsum_le_tsum_norm hcnormsum)
      _ ≤ ‖T‖ + ∑' n : ℕ, ‖T‖ / 2 / 2 ^ n := by
        exact add_le_add le_rfl
          (Summable.tsum_le_tsum hcnorm hcnormsum (summable_geometric_two' ‖T‖))
      _ = 2 * ‖T‖ := by rw [tsum_geometric_two']; ring
  have hstendsto : Filter.Tendsto (fun n => (s n).value) Filter.atTop (nhds a) := by
    have hsumtendsto := hcsum.hasSum.tendsto_sum_nat
    have hconst : Filter.Tendsto (fun _ : ℕ => (s 0).value) Filter.atTop
        (nhds (s 0).value) := tendsto_const_nhds
    have hadd := hconst.add hsumtendsto
    rw [show (fun n => (s n).value) =
        (fun n => (s 0).value + ∑ i ∈ Finset.range n, c i) by
      funext n
      exact hspartial n]
    simpa only [a] using hadd
  let piL : A →L[ℂ] (H →L[ℂ] H) :=
    pi.toAlgHom.toLinearMap.mkContinuous 1 fun x => by
      change ‖pi x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le pi x
  have hpistendsto :
      Filter.Tendsto (fun n => pi (s n).value) Filter.atTop (nhds (pi a)) := by
    have hcont : Continuous piL := piL.continuous
    change Filter.Tendsto (fun n => piL (s n).value) Filter.atTop (nhds (piL a))
    exact (hcont.tendsto a).comp hstendsto
  have hrestendsto :
      Filter.Tendsto (fun n => (T - pi (s n).value) * E.starProjection)
        Filter.atTop (nhds ((T - pi a) * E.starProjection)) := by
    exact (tendsto_const_nhds.sub hpistendsto).mul tendsto_const_nhds
  have hgeom :
      Filter.Tendsto (fun n : ℕ => ‖T‖ / 6 / 2 ^ n) Filter.atTop (nhds 0) := by
    have hpow : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have hid : (fun n : ℕ => ‖T‖ / 6 / 2 ^ n) =
        (fun n : ℕ => (‖T‖ / 6) * (1 / 2 : ℝ) ^ n) := by
      funext n
      simp only [div_eq_mul_inv, one_mul, inv_pow]
    rw [hid]
    convert tendsto_const_nhds.mul hpow using 1
    simp
  have hresnormzero :
      Filter.Tendsto (fun n => ‖(T - pi (s n).value) * E.starProjection‖)
        Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => norm_nonneg _)
      (fun n => (s n).error_lt.le) hgeom
  have hreszero :
      Filter.Tendsto (fun n => (T - pi (s n).value) * E.starProjection)
        Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hresnormzero
  refine ⟨a, haself, hanorm, ?_⟩
  exact tendsto_nhds_unique hrestendsto hreszero

/-- Coarse norm-controlled exact self-adjoint interpolation on a finite-dimensional
subspace.  The factor `2` is the geometric-correction bound; no convergence of
independently selected one-shot approximants is assumed. -/
theorem exists_selfAdjoint_norm_le_two_mul_and_eq_on
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection] [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 2 * ‖T‖ ∧
      ∀ x : H, x ∈ E → pi a x = T x := by
  obtain ⟨a, ha, hanorm, hexact⟩ :=
    exists_selfAdjoint_norm_le_two_mul_and_sub_mul_starProjection_eq_zero
      pi hpi E T hT
  refine ⟨a, ha, hanorm, fun x hx => ?_⟩
  have happ := congrArg (fun S : H →L[ℂ] H => S x) hexact
  have hproj : E.starProjection x = x := E.starProjection_eq_self_iff.mpr hx
  have hzero : T x - pi a x = 0 := by
    simpa [ContinuousLinearMap.comp_apply, hproj] using happ
  exact (sub_eq_zero.mp hzero).symm

/-- The finite enlargement generated by `E` and its image under `T`. -/
noncomputable def finiteReduction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : Submodule ℂ H) (T : H →L[ℂ] H) : Submodule ℂ H :=
  E ⊔ E.map T.toLinearMap

noncomputable instance instFiniteDimensionalFiniteReduction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) :
    FiniteDimensional ℂ (finiteReduction E T) := by
  dsimp [finiteReduction]
  exact Submodule.finiteDimensional_sup E (E.map T.toLinearMap)

/-- Compression of `T` to the finite enlargement `E + T(E)`, extended by zero
on its orthogonal complement. -/
noncomputable def finiteCompression
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) : H →L[ℂ] H :=
  let F := finiteReduction E T
  F.starProjection * T * F.starProjection

theorem isSelfAdjoint_finiteCompression
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (finiteCompression E T) := by
  let F := finiteReduction E T
  exact hT.conj_starProjection F

theorem finiteCompression_nonneg
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : 0 ≤ T) :
    0 ≤ finiteCompression E T := by
  let F := finiteReduction E T
  let c := CFC.sqrt T
  have hcself : IsSelfAdjoint c := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)
  have hcsq : c * c = T := by
    simpa only [c] using CFC.sqrt_mul_sqrt_self T hT
  rw [show finiteCompression E T = star (c * F.starProjection) *
      (c * F.starProjection) by
    change F.starProjection * T * F.starProjection =
      star (c * F.starProjection) * (c * F.starProjection)
    rw [star_mul, (isSelfAdjoint_starProjection F).star_eq, hcself.star_eq]
    calc
      F.starProjection * T * F.starProjection =
          F.starProjection * (c * c) * F.starProjection :=
        congrArg (fun R : H →L[ℂ] H =>
          F.starProjection * R * F.starProjection) hcsq.symm
      _ = F.starProjection * c * (c * F.starProjection) := by
        simp only [mul_assoc]]
  exact star_mul_self_nonneg _

theorem norm_finiteCompression_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) : ‖finiteCompression E T‖ ≤ ‖T‖ := by
  let F := finiteReduction E T
  calc
    ‖finiteCompression E T‖ ≤ ‖F.starProjection‖ * ‖T‖ * ‖F.starProjection‖ := by
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖T‖ * 1 := by gcongr <;> exact F.starProjection_norm_le
    _ = ‖T‖ := by ring

theorem finiteCompression_apply_of_mem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) {x : H} (hx : x ∈ E) :
    finiteCompression E T x = T x := by
  let F := finiteReduction E T
  have hxF : x ∈ F := (show E ≤ F from le_sup_left) hx
  have hTxF : T x ∈ F := by
    apply (show E.map T.toLinearMap ≤ F from le_sup_right)
    exact ⟨x, hx, rfl⟩
  simp [finiteCompression, F, F.starProjection_eq_self_iff.mpr hxF,
    F.starProjection_eq_self_iff.mpr hTxF]

theorem finiteCompression_supported
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) :
    let F := finiteReduction E T
    F.starProjection * finiteCompression E T = finiteCompression E T ∧
      finiteCompression E T * F.starProjection = finiteCompression E T := by
  let F := finiteReduction E T
  have hP : F.starProjection * F.starProjection = F.starProjection :=
    F.isIdempotentElem_starProjection
  change F.starProjection * (F.starProjection * T * F.starProjection) =
      F.starProjection * T * F.starProjection ∧
    (F.starProjection * T * F.starProjection) * F.starProjection =
      F.starProjection * T * F.starProjection
  constructor
  · calc
      F.starProjection * (F.starProjection * T * F.starProjection) =
          (F.starProjection * F.starProjection) * T * F.starProjection := by
            noncomm_ring
      _ = F.starProjection * T * F.starProjection := by rw [hP]
  · calc
      (F.starProjection * T * F.starProjection) * F.starProjection =
          F.starProjection * T * (F.starProjection * F.starProjection) := by
            noncomm_ring
      _ = F.starProjection * T * F.starProjection := by rw [hP]

/-- The geometric exact interpolation applied to the finite compression on
`E + T(E)`.  The represented witness and the compression agree on the whole
finite enlargement, so that enlargement reduces the represented witness.  This
is the CFC-ready coarse-bound stage of the sharp Kadison argument. -/
theorem exists_selfAdjoint_finiteReduction_norm_le_two_mul
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    let F := finiteReduction E T
    let S := finiteCompression E T
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 2 * ‖T‖ ∧
      pi a * F.starProjection = S ∧ F.starProjection * pi a = S ∧
      ∀ x : H, x ∈ E → pi a x = T x := by
  let F := finiteReduction E T
  let S := finiteCompression E T
  have hSself : IsSelfAdjoint S := isSelfAdjoint_finiteCompression E T hT
  obtain ⟨a, haself, hanormS, hexact⟩ :=
    exists_selfAdjoint_norm_le_two_mul_and_sub_mul_starProjection_eq_zero
      pi hpi F S hSself
  have hSnorm : ‖S‖ ≤ ‖T‖ := norm_finiteCompression_le E T
  have hanorm : ‖a‖ ≤ 2 * ‖T‖ := hanormS.trans (by gcongr)
  have hSsupport := finiteCompression_supported E T
  have hright : pi a * F.starProjection = S := by
    have hsub : S * F.starProjection - pi a * F.starProjection = 0 := by
      simpa only [sub_mul] using hexact
    calc
      pi a * F.starProjection = S * F.starProjection :=
        (sub_eq_zero.mp hsub).symm
      _ = S := hSsupport.2
  have hleft : F.starProjection * pi a = S := by
    calc
      F.starProjection * pi a = star (pi a * F.starProjection) := by
        rw [star_mul, haself.map pi |>.star_eq,
          (isSelfAdjoint_starProjection F).star_eq]
      _ = star S := by rw [hright]
      _ = S := hSself.star_eq
  refine ⟨a, haself, hanorm, hright, hleft, fun x hx => ?_⟩
  have hxF : x ∈ F := (show E ≤ F from le_sup_left) hx
  have happ := congrArg (fun R : H →L[ℂ] H => R x) hright
  have hproj : F.starProjection x = x := F.starProjection_eq_self_iff.mpr hxF
  simpa [hproj, S, finiteCompression_apply_of_mem E T hx] using happ

/-! ## Functional calculus on a reducing projection -/

/-- On the commutant of a star projection, multiplication by that projection
is a non-unital star algebra homomorphism.  This is the small corner map used
to transport clipping through a reducing finite-dimensional summand. -/
noncomputable def centralizerRightMul
    {B : Type*} [CStarAlgebra B] (q : B) (hq : IsStarProjection q) :
    (StarSubalgebra.centralizer ℂ ({q} : Set B)) →⋆ₙₐ[ℂ] B where
  toFun x := (x : B) * q
  map_zero' := by simp
  map_add' x y := by simp [add_mul]
  map_smul' c x := by simp
  map_mul' x y := by
    have hy : q * (y : B) = (y : B) * q := by
      have hy' :=
        (StarSubalgebra.mem_centralizer_iff (R := ℂ)
          (s := ({q} : Set B)) (z := (y : B))).mp y.property q (by simp)
      exact hy'.1
    calc
      ((x : B) * (y : B)) * q = (x : B) * (y : B) * (q * q) := by
        rw [hq.isIdempotentElem.eq]
      _ = (x : B) * ((y : B) * q) * q := by simp only [mul_assoc]
      _ = (x : B) * (q * (y : B)) * q := by rw [hy]
      _ = ((x : B) * q) * ((y : B) * q) := by simp only [mul_assoc]
  map_star' x := by
    have hx : q * star (x : B) = star (x : B) * q := by
      have hx' :=
        (StarSubalgebra.mem_centralizer_iff (R := ℂ)
          (s := ({q} : Set B)) (z := (star x : B))).mp
            (star_mem x.property) q (by simp)
      exact hx'.1
    calc
      star (x : B) * q = q * star (x : B) := hx.symm
      _ = star q * star (x : B) := by rw [hq.isSelfAdjoint.star_eq]
      _ = star ((x : B) * q) := by rw [star_mul]

/-- A continuous real function fixing zero respects equality after a common
reducing star projection.  The proof uses the non-unital corner homomorphism,
so no polynomial-approximation hierarchy is introduced. -/
theorem cfc_mul_eq_of_mul_eq
    {B : Type*} [CStarAlgebra B] {a b q : B}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hq : IsStarProjection q) (haq : Commute a q) (hbq : Commute b q)
    (hab : a * q = b * q) (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : f 0 = 0) :
    cfc f a * q = cfc f b * q := by
  let C : StarSubalgebra ℂ B :=
    StarSubalgebra.centralizer ℂ ({q} : Set B)
  letI : IsClosed (C : Set B) := by
    dsimp only [C]
    rw [StarSubalgebra.coe_centralizer]
    exact Set.isClosed_centralizer _
  have haC : a ∈ C := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    constructor
    · exact haq.eq.symm
    · simpa [hq.isSelfAdjoint.star_eq] using haq.eq.symm
  have hbC : b ∈ C := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    constructor
    · exact hbq.eq.symm
    · simpa [hq.isSelfAdjoint.star_eq] using hbq.eq.symm
  let ac : C := ⟨a, haC⟩
  let bc : C := ⟨b, hbC⟩
  have hacself : IsSelfAdjoint ac := by
    rw [isSelfAdjoint_iff]
    exact Subtype.ext ha.star_eq
  have hbcself : IsSelfAdjoint bc := by
    rw [isSelfAdjoint_iff]
    exact Subtype.ext hb.star_eq
  let ι : C →⋆ₐ[ℂ] B := C.subtype
  let r : C →⋆ₙₐ[ℂ] B := centralizerRightMul q hq
  have hιa : ι (cfcₙ f ac) = cfcₙ f a := by
    simpa [ι, ac] using
      (ι.toNonUnitalStarAlgHom.map_cfcₙ f ac
        (hf := hf.continuousOn) (hf₀ := hf0)
        (hφ := continuous_subtype_val) (ha := hacself) (hφa := ha))
  have hιb : ι (cfcₙ f bc) = cfcₙ f b := by
    simpa [ι, bc] using
      (ι.toNonUnitalStarAlgHom.map_cfcₙ f bc
        (hf := hf.continuousOn) (hf₀ := hf0)
        (hφ := continuous_subtype_val) (ha := hbcself) (hφa := hb))
  have hra := r.map_cfcₙ f ac
    (hf := hf.continuousOn) (hf₀ := hf0) (hφ := by fun_prop)
    (ha := hacself) (hφa := by cfc_tac)
  have hrb := r.map_cfcₙ f bc
    (hf := hf.continuousOn) (hf₀ := hf0) (hφ := by fun_prop)
    (ha := hbcself) (hφa := by cfc_tac)
  rw [show r ac = a * q by rfl] at hra
  rw [show r bc = b * q by rfl] at hrb
  calc
    cfc f a * q = cfcₙ f a * q := by
      rw [cfcₙ_eq_cfc hf.continuousOn hf0]
    _ = r (cfcₙ f ac) := by rw [← hιa]; rfl
    _ = cfcₙ f (a * q) := hra
    _ = cfcₙ f (b * q) := by rw [hab]
    _ = r (cfcₙ f bc) := hrb.symm
    _ = cfcₙ f b * q := by rw [← hιb]; rfl
    _ = cfc f b * q := by rw [cfcₙ_eq_cfc hf.continuousOn hf0]

/-- Sharp norm-controlled exact self-adjoint interpolation on a
finite-dimensional subspace.  The coarse exact witness is first made reducing
on `E + T(E)` and is then clipped by continuous functional calculus. -/
theorem exists_selfAdjoint_norm_le_and_eq_on
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      ∀ x : H, x ∈ E → pi a x = T x := by
  let F := finiteReduction E T
  let S := finiteCompression E T
  let q : H →L[ℂ] H := F.starProjection
  obtain ⟨a, ha, -, hright, hleft, -⟩ :=
    exists_selfAdjoint_finiteReduction_norm_le_two_mul pi hpi E T hT
  have hSself : IsSelfAdjoint S := isSelfAdjoint_finiteCompression E T hT
  have hSnorm : ‖S‖ ≤ ‖T‖ := norm_finiteCompression_le E T
  have hSsupport := finiteCompression_supported E T
  have hinterval : -‖T‖ ≤ ‖T‖ :=
    (neg_nonpos.mpr (norm_nonneg T)).trans (norm_nonneg T)
  let f : ℝ → ℝ := fun x =>
    (Set.projIcc (-‖T‖) ‖T‖ hinterval x : ℝ)
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hf0 : f 0 = 0 := by
    dsimp only [f]
    simp [Set.projIcc_of_mem, norm_nonneg]
  have hfnorm (x : ℝ) : ‖f x‖ ≤ ‖T‖ := by
    have hx := (Set.projIcc (-‖T‖) ‖T‖ hinterval x).property
    change |(Set.projIcc (-‖T‖) ‖T‖ hinterval x : ℝ)| ≤ ‖T‖
    exact abs_le.mpr hx
  have hfix : cfc f S = S := by
    calc
      cfc f S = cfc (fun x : ℝ => x) S := by
        apply cfc_congr
        intro x hx
        have hxnorm : ‖x‖ ≤ ‖S‖ := spectrum.norm_le_norm_of_mem hx
        have hxbound : -‖T‖ ≤ x ∧ x ≤ ‖T‖ := by
          rw [Real.norm_eq_abs, abs_le] at hxnorm
          exact ⟨(neg_le_neg hSnorm).trans hxnorm.1,
            hxnorm.2.trans hSnorm⟩
        dsimp only [f]
        exact congrArg Subtype.val
          (Set.projIcc_of_mem hinterval hxbound)
      _ = S := cfc_id' ℝ S
  have haq : Commute (pi a) q := by
    rw [commute_iff_eq]
    exact hright.trans hleft.symm
  have hSq : Commute S q := by
    rw [commute_iff_eq]
    exact hSsupport.2.trans hSsupport.1.symm
  let b : A := cfc f a
  have hbself : IsSelfAdjoint b := IsSelfAdjoint.cfc
  have hbnorm : ‖b‖ ≤ ‖T‖ := by
    exact norm_cfc_le (norm_nonneg T) fun x _ => hfnorm x
  have hpib : pi b = cfc f (pi a) := by
    exact StarAlgHomClass.map_cfc pi f a
      (hf := hf.continuousOn) (hφ := by fun_prop)
      (ha := ha) (hφa := ha.map pi)
  have hfcq : cfc f (pi a) * q = S := by
    calc
      cfc f (pi a) * q = cfc f S * q :=
        cfc_mul_eq_of_mul_eq (ha.map pi) hSself
          isStarProjection_starProjection haq hSq
          (hright.trans hSsupport.2.symm) f hf hf0
      _ = S := by rw [hfix, hSsupport.2]
  refine ⟨b, hbself, hbnorm, fun x hx => ?_⟩
  have hxF : x ∈ F := (show E ≤ F from le_sup_left) hx
  have hqx : q x = x := F.starProjection_eq_self_iff.mpr hxF
  have happ := congrArg (fun R : H →L[ℂ] H => R x) hfcq
  rw [hpib]
  simpa [ContinuousLinearMap.comp_apply, hqx, S,
    finiteCompression_apply_of_mem E T hx] using happ

/-- Sharp positive exact interpolation on a finite-dimensional subspace.
The self-adjoint exact interpolant on the reducing enlargement is clipped to
the interval `[0, ‖T‖]`; the common reducing corner makes this second clipping
preserve the prescribed vectors exactly. -/
theorem exists_nonneg_norm_le_and_eq_on
    {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : 0 ≤ T) :
    ∃ a : A, 0 ≤ a ∧ ‖a‖ ≤ ‖T‖ ∧
      ∀ x : H, x ∈ E → pi a x = T x := by
  let F := finiteReduction E T
  let S := finiteCompression E T
  let q : H →L[ℂ] H := F.starProjection
  have hTself : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg hT
  have hSself : IsSelfAdjoint S := isSelfAdjoint_finiteCompression E T hTself
  have hSnonneg : 0 ≤ S := finiteCompression_nonneg E T hT
  have hSnorm : ‖S‖ ≤ ‖T‖ := norm_finiteCompression_le E T
  have hSsupport := finiteCompression_supported E T
  obtain ⟨a, ha, -, haexact⟩ :=
    exists_selfAdjoint_norm_le_and_eq_on pi hpi F S hSself
  have hright : pi a * q = S := by
    apply ContinuousLinearMap.ext
    intro x
    change pi a (q x) = S x
    rw [haexact (q x) (F.starProjection_apply_mem x)]
    have happ := congrArg (fun R : H →L[ℂ] H => R x) hSsupport.2
    simpa [ContinuousLinearMap.comp_apply] using happ
  have hleft : q * pi a = S := by
    calc
      q * pi a = star (pi a * q) := by
        rw [star_mul, ha.map pi |>.star_eq,
          (isSelfAdjoint_starProjection F).star_eq]
      _ = star S := by rw [hright]
      _ = S := hSself.star_eq
  have haq : Commute (pi a) q := by
    rw [commute_iff_eq]
    exact hright.trans hleft.symm
  have hSq : Commute S q := by
    rw [commute_iff_eq]
    exact hSsupport.2.trans hSsupport.1.symm
  have hinterval : 0 ≤ ‖T‖ := norm_nonneg T
  let f : ℝ → ℝ := fun x =>
    (Set.projIcc 0 ‖T‖ hinterval x : ℝ)
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hf0 : f 0 = 0 := by
    dsimp only [f]
    simp
  have hfnonneg (x : ℝ) : 0 ≤ f x := by
    exact (Set.projIcc 0 ‖T‖ hinterval x).property.1
  have hfnorm (x : ℝ) : ‖f x‖ ≤ ‖T‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnonneg x)]
    exact (Set.projIcc 0 ‖T‖ hinterval x).property.2
  have hfix : cfc f S = S := by
    calc
      cfc f S = cfc (fun x : ℝ => x) S := by
        apply cfc_congr
        intro x hx
        have hxlower : 0 ≤ x := spectrum_nonneg_of_nonneg hSnonneg hx
        have hxnorm : ‖x‖ ≤ ‖S‖ := spectrum.norm_le_norm_of_mem hx
        have hxupper : x ≤ ‖T‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hxlower] at hxnorm
          exact hxnorm.trans hSnorm
        dsimp only [f]
        exact congrArg Subtype.val
          (Set.projIcc_of_mem hinterval ⟨hxlower, hxupper⟩)
      _ = S := cfc_id' ℝ S
  let b : A := cfc f a
  have hbnonneg : 0 ≤ b := cfc_nonneg fun x _ => hfnonneg x
  have hbnorm : ‖b‖ ≤ ‖T‖ := by
    exact norm_cfc_le (norm_nonneg T) fun x _ => hfnorm x
  have hpib : pi b = cfc f (pi a) := by
    exact StarAlgHomClass.map_cfc pi f a
      (hf := hf.continuousOn) (hφ := by fun_prop)
      (ha := ha) (hφa := ha.map pi)
  have hfcq : cfc f (pi a) * q = S := by
    calc
      cfc f (pi a) * q = cfc f S * q :=
        cfc_mul_eq_of_mul_eq (ha.map pi) hSself
          isStarProjection_starProjection haq hSq
          (hright.trans hSsupport.2.symm) f hf hf0
      _ = S := by rw [hfix, hSsupport.2]
  refine ⟨b, hbnonneg, hbnorm, fun x hx => ?_⟩
  have hxF : x ∈ F := (show E ≤ F from le_sup_left) hx
  have hqx : q x = x := F.starProjection_eq_self_iff.mpr hxF
  have happ := congrArg (fun R : H →L[ℂ] H => R x) hfcq
  rw [hpib]
  simpa [ContinuousLinearMap.comp_apply, hqx, S,
    finiteCompression_apply_of_mem E T hx] using happ

/-- Positive-contraction form of finite-dimensional exact interpolation. -/
theorem exists_positive_contraction_eq_on
    {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) (hT : 0 ≤ T) (hTnorm : ‖T‖ ≤ 1) :
    ∃ a : A, 0 ≤ a ∧ ‖a‖ ≤ 1 ∧
      ∀ x : H, x ∈ E → pi a x = T x := by
  obtain ⟨a, ha, hanorm, haexact⟩ :=
    exists_nonneg_norm_le_and_eq_on pi hpi E T hT
  exact ⟨a, ha, hanorm.trans hTnorm, haexact⟩

/-- Sharp exact finite-dimensional interpolation with the algebra witness
supported in a prescribed projection corner.  Only the requested finite
subspace is required to be mapped into the represented corner. -/
theorem StarAlgHom.exists_cornerSupported_selfAdjoint_norm_le_and_eq_on_of_apply
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    {e : A} (he : IsStarProjection e)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (hE : ∀ x : H, x ∈ E → pi e x = x)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hTE : ∀ x : H, x ∈ E → pi e (T x) = T x) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      e * a = a ∧ a * e = a ∧ ∀ x : H, x ∈ E → pi a x = T x := by
  obtain ⟨b, hbself, hbnorm, hbexact⟩ :=
    exists_selfAdjoint_norm_le_and_eq_on pi hpi E T hT
  let a : A := e * b * e
  have haself : IsSelfAdjoint a := by
    rw [IsSelfAdjoint]
    simp only [a, star_mul, he.isSelfAdjoint.star_eq, hbself.star_eq]
    exact (mul_assoc e b e).symm
  have hanorm : ‖a‖ ≤ ‖T‖ := by
    calc
      ‖a‖ ≤ ‖e‖ * ‖b‖ * ‖e‖ := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ‖T‖ * 1 := by
        gcongr <;> exact he.norm_le
      _ = ‖T‖ := by ring
  have haleft : e * a = a := by
    dsimp [a]
    calc
      e * (e * b * e) = (e * e) * b * e := by noncomm_ring
      _ = e * b * e := by rw [he.isIdempotentElem.eq]
  have haright : a * e = a := by
    dsimp [a]
    calc
      e * b * e * e = e * b * (e * e) := by noncomm_ring
      _ = e * b * e := by rw [he.isIdempotentElem.eq]
  refine ⟨a, haself, hanorm, haleft, haright, fun x hx => ?_⟩
  have hmap : pi a = pi e * pi b * pi e := by simp [a]
  rw [hmap]
  change pi e (pi b (pi e x)) = T x
  rw [hE x hx, hbexact x hx]
  exact hTE x hx

/-- Compatibility wrapper using the former global range hypothesis. -/
theorem StarAlgHom.exists_cornerSupported_selfAdjoint_norm_le_and_eq_on
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    {e : A} (he : IsStarProjection e)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection] [FiniteDimensional ℂ E]
    (hE : ∀ x : H, x ∈ E → pi e x = x)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hTrange : pi e * T = T) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      e * a = a ∧ a * e = a ∧ ∀ x : H, x ∈ E → pi a x = T x := by
  apply pi.exists_cornerSupported_selfAdjoint_norm_le_and_eq_on_of_apply
    hpi he E hE T hT
  intro x _hx
  exact congrArg (fun S : H →L[ℂ] H => S x) hTrange

/-- Positive sharp interpolation supported in an arbitrary projection corner.
The support projection is the corner unit; it is not identified with the
ambient unit. -/
theorem StarAlgHom.exists_cornerSupported_nonneg_norm_le_and_eq_on_of_apply
    {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    {e : A} (he : IsStarProjection e)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (hE : ∀ x : H, x ∈ E → pi e x = x)
    (T : H →L[ℂ] H) (hT : 0 ≤ T)
    (hTE : ∀ x : H, x ∈ E → pi e (T x) = T x) :
    ∃ a : A, 0 ≤ a ∧ ‖a‖ ≤ ‖T‖ ∧
      e * a = a ∧ a * e = a ∧ ∀ x : H, x ∈ E → pi a x = T x := by
  obtain ⟨b, hbnonneg, hbnorm, hbexact⟩ :=
    exists_nonneg_norm_le_and_eq_on pi hpi E T hT
  let a : A := e * b * e
  have hanonneg : 0 ≤ a := by
    simpa only [a, he.isSelfAdjoint.star_eq] using
      (star_right_conjugate_nonneg hbnonneg e)
  have hanorm : ‖a‖ ≤ ‖T‖ := by
    calc
      ‖a‖ ≤ ‖e‖ * ‖b‖ * ‖e‖ := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * ‖T‖ * 1 := by
        gcongr <;> exact he.norm_le
      _ = ‖T‖ := by ring
  have haleft : e * a = a := by
    dsimp [a]
    calc
      e * (e * b * e) = (e * e) * b * e := by noncomm_ring
      _ = e * b * e := by rw [he.isIdempotentElem.eq]
  have haright : a * e = a := by
    dsimp [a]
    calc
      e * b * e * e = e * b * (e * e) := by noncomm_ring
      _ = e * b * e := by rw [he.isIdempotentElem.eq]
  refine ⟨a, hanonneg, hanorm, haleft, haright, fun x hx => ?_⟩
  have hmap : pi a = pi e * pi b * pi e := by simp [a]
  rw [hmap]
  change pi e (pi b (pi e x)) = T x
  rw [hE x hx, hbexact x hx]
  exact hTE x hx

/-- Compatibility wrapper using the former global range hypothesis. -/
theorem StarAlgHom.exists_cornerSupported_nonneg_norm_le_and_eq_on
    {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    {e : A} (he : IsStarProjection e)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection] [FiniteDimensional ℂ E]
    (hE : ∀ x : H, x ∈ E → pi e x = x)
    (T : H →L[ℂ] H) (hT : 0 ≤ T)
    (hTrange : pi e * T = T) :
    ∃ a : A, 0 ≤ a ∧ ‖a‖ ≤ ‖T‖ ∧
      e * a = a ∧ a * e = a ∧ ∀ x : H, x ∈ E → pi a x = T x := by
  apply pi.exists_cornerSupported_nonneg_norm_le_and_eq_on_of_apply
    hpi he E hE T hT
  intro x _hx
  exact congrArg (fun S : H →L[ℂ] H => S x) hTrange

/-- Positive-contraction interpolation supported in an arbitrary projection
corner. -/
theorem StarAlgHom.exists_cornerSupported_positive_contraction_eq_on_of_apply
    {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    {e : A} (he : IsStarProjection e)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (hE : ∀ x : H, x ∈ E → pi e x = x)
    (T : H →L[ℂ] H) (hT : 0 ≤ T) (hTnorm : ‖T‖ ≤ 1)
    (hTE : ∀ x : H, x ∈ E → pi e (T x) = T x) :
    ∃ a : A, 0 ≤ a ∧ ‖a‖ ≤ 1 ∧
      e * a = a ∧ a * e = a ∧ ∀ x : H, x ∈ E → pi a x = T x := by
  obtain ⟨a, ha, hanorm, haleft, haright, haexact⟩ :=
    pi.exists_cornerSupported_nonneg_norm_le_and_eq_on_of_apply
      hpi he E hE T hT hTE
  exact ⟨a, ha, hanorm.trans hTnorm, haleft, haright, haexact⟩

/-- Compatibility wrapper using the former global range hypothesis. -/
theorem StarAlgHom.exists_cornerSupported_positive_contraction_eq_on
    {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    {e : A} (he : IsStarProjection e)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection] [FiniteDimensional ℂ E]
    (hE : ∀ x : H, x ∈ E → pi e x = x)
    (T : H →L[ℂ] H) (hT : 0 ≤ T) (hTnorm : ‖T‖ ≤ 1)
    (hTrange : pi e * T = T) :
    ∃ a : A, 0 ≤ a ∧ ‖a‖ ≤ 1 ∧
      e * a = a ∧ a * e = a ∧ ∀ x : H, x ∈ E → pi a x = T x := by
  apply pi.exists_cornerSupported_positive_contraction_eq_on_of_apply
    hpi he E hE T hT hTnorm
  intro x _hx
  exact congrArg (fun S : H →L[ℂ] H => S x) hTrange

/-- Compatibility form of corner-supported exact interpolation with the old
factor-two estimate.  New callers should use the sharp theorem above. -/
theorem StarAlgHom.exists_cornerSupported_selfAdjoint_norm_le_two_mul_and_eq_on
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    {e : A} (he : IsStarProjection e)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection] [FiniteDimensional ℂ E]
    (hE : ∀ x : H, x ∈ E → pi e x = x)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hTrange : pi e * T = T) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 2 * ‖T‖ ∧
      e * a = a ∧ a * e = a ∧ ∀ x : H, x ∈ E → pi a x = T x := by
  obtain ⟨a, ha, hanorm, haleft, haright, haexact⟩ :=
    pi.exists_cornerSupported_selfAdjoint_norm_le_and_eq_on
      hpi he E hE T hT hTrange
  have hanorm' : ‖a‖ ≤ 2 * ‖T‖ :=
    hanorm.trans (by nlinarith [norm_nonneg T])
  exact ⟨a, ha, hanorm', haleft, haright, haexact⟩

end MathlibAnnex.Analysis.CStarAlgebra
