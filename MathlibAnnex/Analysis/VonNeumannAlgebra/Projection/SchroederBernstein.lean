/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.CentralComparison

/-!
# Schroeder--Bernstein for internal projection equivalence

The sandwich argument starts with `p ∼ r ≤ q ≤ p`. Iterating the internal
witness on the defect `p - q` gives an orthogonal sequence of projections.
The shifts between consecutive projections are summed by the existing
finite-subset strong-net construction. Adding the unchanged complementary
projection gives `p ∼ q`. Mutual subequivalence then reduces to this
sandwich statement.

All witnesses remain in the specified von Neumann algebra. The auxiliary
sequence is constructed from an arbitrary internal witness; there is no
countability or separability hypothesis on the algebra or its Hilbert space.
-/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra

universe u v

/-- The algebraic shift family used by the sandwich proof. -/
private theorem exists_orthogonal_shift_family
    {R : Type v} [NonUnitalRing R] [StarRing R] {p q r : R}
    (hpr : MurrayVonNeumannEquivalent p r) (hq : IsStarProjection q)
    (hrq : r * q = r) (hqp : q * p = q) :
    ∃ P V : ℕ → R,
      (∀ n, IsStarProjection (P n)) ∧ P 0 = p - q ∧
      (∀ n, P n * p = P n) ∧ (∀ n, P (n + 1) * q = P (n + 1)) ∧
      Pairwise (fun i j ↦ P i * P j = 0) ∧
      (∀ n, IsPartialIsometry (V n)) ∧
      (∀ n, star (V n) * V n = P n) ∧
      (∀ n, V n * star (V n) = P (n + 1)) := by
  have hp := hpr.isStarProjection_left
  have hr := hpr.isStarProjection_right
  have hrp : r * p = r := by
    calc
      r * p = (r * q) * p := by rw [hrq]
      _ = r * (q * p) := mul_assoc _ _ _
      _ = r := by rw [hqp, hrq]
  obtain ⟨v, hv, hvi, hvf, hpv, hvp⟩ :=
    hpr.exists_partial_isometry_with_absorption hp hp.isIdempotentElem.eq hrp
  have hqr : q * r = r := by
    simpa only [star_mul, hq.isSelfAdjoint.star_eq, hr.isSelfAdjoint.star_eq]
      using congrArg star hrq
  have hqv : q * v = v := by
    calc
      q * v = q * (r * v) := by rw [← hvf, hv.mul_star_self_mul]
      _ = (q * r) * v := (mul_assoc _ _ _).symm
      _ = v := by rw [hqr, ← hvf, hv.mul_star_self_mul]
  have hpq : p * q = q := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
      using congrArg star hqp
  let d := p - q
  have hd : IsStarProjection d := hq.sub_of_mul_eq_left hp hqp
  have hpd : p * d = d := by
    change p * (p - q) = p - q
    rw [mul_sub, hp.isIdempotentElem.eq, hpq]
  have hdv : d * v = 0 := by
    change (p - q) * v = 0
    rw [sub_mul, hpv, hqv, sub_self]
  let U : ℕ → R := Nat.rec d (fun _ x ↦ v * x)
  have hU : ∀ n, IsPartialIsometry (U n) ∧ star (U n) * U n = d ∧ p * U n = U n := by
    intro n
    induction n with
    | zero =>
      refine ⟨hd.isPartialIsometry, ?_, hpd⟩
      change star d * d = d
      rw [hd.isSelfAdjoint.star_eq, hd.isIdempotentElem.eq]
    | succ n ih =>
      refine ⟨ih.1.mul_of_initial_mul_eq v (by rw [hvi, ih.2.2]), ?_, ?_⟩
      · change star (v * U n) * (v * U n) = d
        calc
          star (v * U n) * (v * U n) =
              star (U n) * (star v * v) * U n := by
            simp only [star_mul, mul_assoc]
          _ = d := by rw [hvi, mul_assoc, ih.2.2, ih.2.1]
      · change p * (v * U n) = v * U n
        rw [← mul_assoc, hpv]
  have hUd (n : ℕ) : U n * d = U n := by
    simpa only [(hU n).2.1] using (hU n).1.mul_initial
  have hdUs (n : ℕ) : d * star (U n) = star (U n) := by
    simpa only [(hU n).2.1] using (hU n).1.initial_mul_star
  let P : ℕ → R := fun n ↦ U n * star (U n)
  have hP (n : ℕ) : IsStarProjection (P n) :=
    (hU n).1.isStarProjection_mul_star_self
  have hPzero : P 0 = d := by
    change d * star d = d
    rw [hd.isSelfAdjoint.star_eq, hd.isIdempotentElem.eq]
  have hPsucc (n : ℕ) : P (n + 1) = v * P n * star v := by
    change (v * U n) * star (v * U n) = v * (U n * star (U n)) * star v
    simp only [star_mul, mul_assoc]
  have hPp (n : ℕ) : P n * p = P n := by
    have hstar : star (U n) * p = star (U n) := by
      simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star (hU n).2.2
    change (U n * star (U n)) * p = U n * star (U n)
    rw [mul_assoc, hstar]
  have hPq (n : ℕ) : P (n + 1) * q = P (n + 1) := by
    have hstar : star v * q = star v := by
      simpa only [star_mul, hq.isSelfAdjoint.star_eq] using congrArg star hqv
    calc
      P (n + 1) * q = (v * P n * star v) * q := by rw [hPsucc]
      _ = v * P n * star v := by rw [mul_assoc, hstar]
      _ = P (n + 1) := (hPsucc n).symm
  have hzero_succ (n : ℕ) : P 0 * P (n + 1) = 0 := by
    rw [hPzero, hPsucc]
    calc
      d * (v * P n * star v) = (d * v) * P n * star v := by
        simp only [mul_assoc]
      _ = 0 := by rw [hdv, zero_mul, zero_mul]
  have horth : Pairwise (fun i j ↦ P i * P j = 0) := by
    intro i
    induction i with
    | zero =>
      intro j hij
      cases j with
      | zero => exact (hij rfl).elim
      | succ j => exact hzero_succ j
    | succ i ih =>
      intro j hij
      cases j with
      | zero =>
        simpa only [star_mul, (hP 0).isSelfAdjoint.star_eq,
          (hP (i + 1)).isSelfAdjoint.star_eq, star_zero]
          using congrArg star (hzero_succ i)
      | succ j =>
        have hij' : i ≠ j := fun h ↦ hij (congrArg Nat.succ h)
        have hprod : P i * P j = 0 := ih hij'
        rw [hPsucc, hPsucc]
        calc
          (v * P i * star v) * (v * P j * star v) =
              v * P i * (star v * v) * P j * star v := by
            simp only [mul_assoc]
          _ = v * (P i * P j) * star v := by
            rw [hvi, mul_assoc v (P i) p, hPp]
            simp only [mul_assoc]
          _ = 0 := by rw [hprod, mul_zero, zero_mul]
  let V : ℕ → R := fun n ↦ U (n + 1) * star (U n)
  have hV (n : ℕ) : IsPartialIsometry (V n) :=
    (hU n).1.star.mul_of_initial_mul_eq (U (n + 1)) (by
      rw [(hU (n + 1)).2.1]
      exact hdUs n)
  have hVi (n : ℕ) : star (V n) * V n = P n := by
    change star (U (n + 1) * star (U n)) *
      (U (n + 1) * star (U n)) = U n * star (U n)
    calc
      star (U (n + 1) * star (U n)) * (U (n + 1) * star (U n)) =
          U n * (star (U (n + 1)) * U (n + 1)) * star (U n) := by
        simp only [star_mul, star_star, mul_assoc]
      _ = U n * star (U n) := by rw [(hU (n + 1)).2.1, hUd]
  have hVf (n : ℕ) : V n * star (V n) = P (n + 1) := by
    change (U (n + 1) * star (U n)) * star (U (n + 1) * star (U n)) =
      U (n + 1) * star (U (n + 1))
    calc
      (U (n + 1) * star (U n)) * star (U (n + 1) * star (U n)) =
          U (n + 1) * (star (U n) * U n) * star (U (n + 1)) := by
        simp only [star_mul, star_star, mul_assoc]
      _ = U (n + 1) * star (U (n + 1)) := by rw [(hU n).2.1, hUd (n + 1)]
  exact ⟨P, V, hP, hPzero, hPp, hPq, horth, hV, hVi, hVf⟩

/-- An internal equivalence to a subprojection produces an orthogonal
sequence of equivalent copies of its defect. This interface exposes the
existing shift construction without repeating its recursive proof. -/
theorem MurrayVonNeumannEquivalent.exists_orthogonal_sequence
    {R : Type v} [NonUnitalRing R] [StarRing R] {p q : R}
    (h : MurrayVonNeumannEquivalent p q) (hqp : q * p = q) :
    ∃ P : ℕ → R,
      (∀ n, IsStarProjection (P n)) ∧ P 0 = p - q ∧
      (∀ n, P n * p = P n) ∧
      Pairwise (fun i j ↦ P i * P j = 0) ∧
      ∀ n, MurrayVonNeumannEquivalent (P n) (P (n + 1)) := by
  obtain ⟨P, V, hP, hPzero, hPp, _, horth, hV, hVi, hVf⟩ :=
    exists_orthogonal_shift_family h h.isStarProjection_right
      h.isStarProjection_right.isIdempotentElem.eq hqp
  exact ⟨P, hP, hPzero, hPp, horth,
    fun n ↦ ⟨hP n, hP (n + 1), V n, hV n, hVi n, hVf n⟩⟩

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- If `p ∼ r ≤ q ≤ p`, then `p ∼ q`. The infinite shift is formed in `M`
from the actual finite-subset net of its internal partial isometries. -/
theorem murrayVonNeumannEquivalent_of_sandwich (M : VonNeumannAlgebra H)
    {p q r : M.toStarSubalgebra} (hpr : MurrayVonNeumannEquivalent p r)
    (hq : IsStarProjection q) (hrq : r * q = r) (hqp : q * p = q) :
    MurrayVonNeumannEquivalent p q := by
  obtain ⟨P, V, hP, hPzero, hPp, hPq, horth, hV, hVi, hVf⟩ :=
    exists_orthogonal_shift_family hpr hq hrq hqp
  have hi : Pairwise (fun i j ↦ star (V i) * V j = 0) := by
    intro i j hij
    apply (hV i).star_mul_eq_zero_of_final_mul_final_eq_zero (hV j)
    rw [hVf, hVf]
    exact horth (fun h ↦ hij (Nat.succ.inj h))
  have hf : Pairwise (fun i j ↦ V i * star (V j) = 0) := by
    intro i j hij
    apply (hV i).mul_star_eq_zero_of_initial_mul_initial_eq_zero (hV j)
    rw [hVi, hVi]
    exact horth hij
  obtain ⟨S, hS, hSi, hSf⟩ :=
    exists_orthogonal_sum_partial_isometry_with_sup M V hV hi hf
  let f := iSupProjection M P hP
  let g := iSupProjection M (fun n ↦ P (n + 1)) (fun n ↦ hP (n + 1))
  have hfin : star S * S = f := by simpa only [hVi] using hSi
  have hfinal : S * star S = g := by simpa only [hVf] using hSf
  have hF : IsStarProjection f := isStarProjection_iSupProjection M P hP
  have hG : IsStarProjection g :=
    isStarProjection_iSupProjection M (fun n ↦ P (n + 1)) (fun n ↦ hP (n + 1))
  have hFG : MurrayVonNeumannEquivalent f g := ⟨hF, hG, S, hS, hfin, hfinal⟩
  have hp := hpr.isStarProjection_left
  have hfp : f ≤ p := iSupProjection_le M P hP hp
    (fun n ↦ ((hP n).le_iff_mul_eq_left hp).2 (hPp n))
  have hgq : g ≤ q :=
    iSupProjection_le M (fun n ↦ P (n + 1)) (fun n ↦ hP (n + 1)) hq
      (fun n ↦ ((hP (n + 1)).le_iff_mul_eq_left hq).2 (hPq n))
  have hgf : g ≤ f :=
    iSupProjection_le M (fun n ↦ P (n + 1)) (fun n ↦ hP (n + 1)) hF
      (fun n ↦ le_iSupProjection M P hP (n + 1))
  have hpg : p * g = g := (hG.le_iff_mul_eq_right hp).1 (hgf.trans hfp)
  have hqg : q * g = g := (hG.le_iff_mul_eq_right hq).1 hgq
  have hzero_g : P 0 * g = 0 := by
    rw [hPzero, sub_mul, hpg, hqg, sub_self]
  have hg_zero : g * P 0 = 0 := by
    simpa only [star_mul, (hP 0).isSelfAdjoint.star_eq,
      hG.isSelfAdjoint.star_eq, star_zero] using congrArg star hzero_g
  have hsum : IsStarProjection (P 0 + g) := (hP 0).add hG hzero_g
  have hzero_le : P 0 ≤ P 0 + g := ((hP 0).le_iff_mul_eq_left hsum).2 (by
    rw [mul_add, (hP 0).isIdempotentElem.eq, hzero_g, add_zero])
  have hg_le : g ≤ P 0 + g := (hG.le_iff_mul_eq_left hsum).2 (by
    rw [mul_add, hg_zero, hG.isIdempotentElem.eq, zero_add])
  have hsplit : f = P 0 + g := by
    apply le_antisymm
    · apply iSupProjection_le M P hP hsum
      intro n
      cases n with
      | zero => exact hzero_le
      | succ n =>
        exact (le_iSupProjection M (fun k ↦ P (k + 1))
          (fun k ↦ hP (k + 1)) n).trans hg_le
    · apply (hsum.le_iff_mul_eq_left hF).2
      rw [add_mul, ((hP 0).le_iff_mul_eq_left hF).1 (le_iSupProjection M P hP 0),
        (hG.le_iff_mul_eq_left hF).1 hgf]
  have hfp' : f * p = f := (hF.le_iff_mul_eq_left hp).1 hfp
  have hpf : p * f = f := (hF.le_iff_mul_eq_right hp).1 hfp
  have hfg : f * g = g := (hG.le_iff_mul_eq_right hF).1 hgf
  have hrest : IsStarProjection (p - f) := hF.sub_of_mul_eq_left hp hfp'
  have hrest_f : (p - f) * f = 0 := by
    rw [sub_mul, hpf, hF.isIdempotentElem.eq, sub_self]
  have hrest_g : (p - f) * g = 0 := by
    rw [sub_mul, hpg, hfg, sub_self]
  have hqsum : (p - f) + g = q := by
    rw [hsplit, hPzero, sub_add_eq_sub_sub, sub_add_cancel, sub_sub_cancel]
  have h := (MurrayVonNeumannEquivalent.refl hrest).add hFG hrest_f hrest_g
  simpa only [sub_add_cancel, hqsum] using h

/-- Schroeder--Bernstein for projections in a von Neumann algebra:
mutual internal subequivalence implies internal equivalence. -/
theorem murrayVonNeumannEquivalent_of_mutual_subequivalent
    (M : VonNeumannAlgebra H) {p q : M.toStarSubalgebra}
    (hpq : MurrayVonNeumannSubequivalent p q)
    (hqp : MurrayVonNeumannSubequivalent q p) : MurrayVonNeumannEquivalent p q := by
  obtain ⟨_, r, hpr, hrq⟩ := hpq
  obtain ⟨_, s, hqs, hsp⟩ := hqp
  obtain ⟨t, hrt, hts⟩ := hqs.subprojection hpr.isStarProjection_right hrq
  have hps : MurrayVonNeumannEquivalent p s :=
    murrayVonNeumannEquivalent_of_sandwich M (hpr.trans hrt)
      hqs.isStarProjection_right hts hsp
  exact hps.trans hqs.symm

/-- An equivalence can equivalently be specified by the two internal
subequivalences. No relation on arbitrary nonprojection elements is added. -/
theorem murrayVonNeumannEquivalent_iff_mutual_subequivalent
    (M : VonNeumannAlgebra H) {p q : M.toStarSubalgebra} :
    MurrayVonNeumannEquivalent p q ↔
      MurrayVonNeumannSubequivalent p q ∧ MurrayVonNeumannSubequivalent q p :=
  ⟨fun h ↦ ⟨h.subequivalent, h.symm.subequivalent⟩,
    fun h ↦ murrayVonNeumannEquivalent_of_mutual_subequivalent M h.1 h.2⟩

end VonNeumannAlgebra
