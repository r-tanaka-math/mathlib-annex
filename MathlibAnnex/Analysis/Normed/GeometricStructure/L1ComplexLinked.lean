/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.Normed.GeometricStructure.L1ComplexPhase
import MathlibAnnex.Topology.ClosureSpace.Components

/-!
# Linked complex ℓ¹ coefficient kernels

The closed-pair direction uses three witnesses in the ratio range, not an
assumption that the range consists of exactly three points. In the two-value
case a third unimodular coefficient sequence is explicitly constructed, and
its actual kernel is proved distinct from both old kernels and in their
hull–kernel closure. All kernels are points of the original face-defined GSS.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set ComplexConjugate
open scoped lp ENNReal

namespace NormedSpace

/-- A coefficient combination becomes an affine function of the relative phase. -/
theorem l1PhaseRatio_smul_add (u v : ℓ^∞(ℕ, ℂ)) (hv : ∀ n, ‖v n‖ = 1)
    (a b : ℂ) (n : ℕ) :
    l1PhaseRatio (a • u + b • v) v n = a * l1PhaseRatio u v n + b := by
  change (a * u n + b * v n) * conj (v n) = a * (u n * conj (v n)) + b
  calc
    (a * u n + b * v n) * conj (v n) =
        a * (u n * conj (v n)) + b * (v n * conj (v n)) := by ring
    _ = a * (u n * conj (v n)) + b := by
      rw [Complex.mul_conj_eq_one_of_norm_eq_one (hv n), mul_one]

/-- Three distinct relative phases force the actual two-point set to be closed. -/
theorem isClosed_pair_l1ComplexKernelPoint_of_three_ratios
    (u v : ℓ^∞(ℕ, ℂ)) (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1)
    (i j k : ℕ) (hij : l1PhaseRatio u v i ≠ l1PhaseRatio u v j)
    (hik : l1PhaseRatio u v i ≠ l1PhaseRatio u v k)
    (hjk : l1PhaseRatio u v j ≠ l1PhaseRatio u v k) :
    (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).IsClosed
      {l1ComplexKernelPoint u hu, l1ComplexKernelPoint v hv} := by
  apply ((geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).isClosed_iff_closure_subset _).2
  intro K hK
  obtain ⟨w, hw, rfl⟩ := exists_l1ComplexKernelPoint_eq K
  rw [geometricStructureClosure_closure] at hK
  change (∀ x : ℓ¹(ℕ, ℂ),
    (∀ J : GeometricStructureSpace ℂ ℓ¹(ℕ, ℂ),
      J ∈ {l1ComplexKernelPoint u hu, l1ComplexKernelPoint v hv} → x ∈ J.val) →
    x ∈ (l1ComplexKernelPoint w hw).val) at hK
  have hker : (lp.coefficientFunctional u).ker ⊓ (lp.coefficientFunctional v).ker ≤
      (lp.coefficientFunctional w).ker := by
    intro x hx
    apply hK x
    intro J hJ
    rcases (show J = l1ComplexKernelPoint u hu ∨ J = l1ComplexKernelPoint v hv by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hJ) with rfl | rfl
    · exact hx.1
    · exact hx.2
  obtain ⟨a, b, hfun⟩ :=
    (ContinuousLinearMap.inf_ker_le_ker_iff_exists_smul_add_smul
      (lp.coefficientFunctional u) (lp.coefficientFunctional v)
      (lp.coefficientFunctional w)).1 hker
  have hseq : w = a • u + b • v := by
    apply lp.coefficientFunctional_injective
    rw [lp.coefficientFunctional_add, lp.coefficientFunctional_smul,
      lp.coefficientFunctional_smul]
    exact hfun
  have hn (n : ℕ) : ‖a * l1PhaseRatio u v n + b‖ = 1 := by
    rw [← l1PhaseRatio_smul_add u v hv a b n, ← hseq]
    exact norm_l1PhaseRatio w v hw hv n
  have hab := Complex.eq_zero_or_eq_zero_of_norm_affine_eq_one_three a b
    (l1PhaseRatio u v i) (l1PhaseRatio u v j) (l1PhaseRatio u v k)
    (norm_l1PhaseRatio u v hu hv i) (norm_l1PhaseRatio u v hu hv j)
    (norm_l1PhaseRatio u v hu hv k) hij hik hjk (hn i) (hn j) (hn k)
  have hwne : lp.coefficientFunctional w ≠ 0 := norm_ne_zero_iff.1 (by
    rw [lp.norm_coefficientFunctional_eq_one_of_forall_norm_eq_one w hw]
    exact one_ne_zero)
  rcases hab with ha | hb
  · have hbne : b ≠ 0 := by
      intro hb
      have hzero : w 0 = 0 := by
        rw [hseq]
        change a * u 0 + b * v 0 = 0
        simp [ha, hb]
      exact (zero_ne_one : (0 : ℝ) ≠ 1) (by simpa only [hzero, norm_zero] using hw 0)
    have hpoint : l1ComplexKernelPoint w hw = l1ComplexKernelPoint v hv := by
      apply Subtype.ext
      change (lp.coefficientFunctional w : ℓ¹(ℕ, ℂ) → ℂ) ⁻¹' {0} =
        (lp.coefficientFunctional v : ℓ¹(ℕ, ℂ) → ℂ) ⁻¹' {0}
      rw [hseq, ha, zero_smul, zero_add]
      exact lp.preimage_zero_coefficientFunctional_smul v hbne
    exact Set.mem_insert_iff.2 (Or.inr (Set.mem_singleton_iff.2 hpoint))
  · have hane : a ≠ 0 := by
      intro ha
      have hzero : w 0 = 0 := by
        rw [hseq]
        change a * u 0 + b * v 0 = 0
        simp [ha, hb]
      exact (zero_ne_one : (0 : ℝ) ≠ 1) (by simpa only [hzero, norm_zero] using hw 0)
    have hpoint : l1ComplexKernelPoint w hw = l1ComplexKernelPoint u hu := by
      apply Subtype.ext
      change (lp.coefficientFunctional w : ℓ¹(ℕ, ℂ) → ℂ) ⁻¹' {0} =
        (lp.coefficientFunctional u : ℓ¹(ℕ, ℂ) → ℂ) ⁻¹' {0}
      rw [hseq, hb, zero_smul, add_zero]
      exact lp.preimage_zero_coefficientFunctional_smul u hane
    exact Set.mem_insert_iff.2 (Or.inl hpoint)

/-- Two attained, distinct relative phases give a third actual kernel in the
closure of the pair. Its distinctness is proved from its two relative phases. -/
theorem exists_l1ComplexKernelPoint_mem_closure_pair_ne
    (u v : ℓ^∞(ℕ, ℂ)) (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1)
    (i j : ℕ) (hij : l1PhaseRatio u v i ≠ l1PhaseRatio u v j)
    (hcover : ∀ n, l1PhaseRatio u v n = l1PhaseRatio u v i ∨
      l1PhaseRatio u v n = l1PhaseRatio u v j) :
    ∃ (w : ℓ^∞(ℕ, ℂ)) (hw : ∀ n, ‖w n‖ = 1),
      l1ComplexKernelPoint w hw ∈ (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).closure
        {l1ComplexKernelPoint u hu, l1ComplexKernelPoint v hv} ∧
      l1ComplexKernelPoint w hw ≠ l1ComplexKernelPoint u hu ∧
      l1ComplexKernelPoint w hw ≠ l1ComplexKernelPoint v hv := by
  let r := l1PhaseRatio u v i
  let s := l1PhaseRatio u v j
  have hs : s ≠ 0 := norm_ne_zero_iff.1 (by
    rw [norm_l1PhaseRatio u v hu hv j]; exact one_ne_zero)
  obtain ⟨t, ht, ht1, hts⟩ := Complex.exists_unit_phase_mul_ne r s hs
  have hrs : r - s ≠ 0 := sub_ne_zero.2 hij
  let a : ℂ := (t - 1) / (r - s)
  let b : ℂ := 1 - a * s
  have har : a * r + b = t := by dsimp only [a, b]; field_simp [hrs] <;> ring
  have has : a * s + b = 1 := by dsimp only [b]; ring
  let w : ℓ^∞(ℕ, ℂ) := a • u + b • v
  have hcoeff (n : ℕ) : w n = (a * l1PhaseRatio u v n + b) * v n := by
    change a * u n + b * v n = (a * l1PhaseRatio u v n + b) * v n
    rw [add_mul, mul_assoc, l1PhaseRatio_mul_right u v hv]
  have hw (n : ℕ) : ‖w n‖ = 1 := by
    rw [hcoeff, norm_mul, hv n, mul_one]
    rcases hcover n with hn | hn
    · rw [hn, har]; exact ht
    · rw [hn, has]; exact norm_one
  have hratio (n : ℕ) : l1PhaseRatio w v n = a * l1PhaseRatio u v n + b :=
    l1PhaseRatio_smul_add u v hv a b n
  have hwi : l1PhaseRatio w v i = t := (hratio i).trans har
  have hwj : l1PhaseRatio w v j = 1 := (hratio j).trans has
  refine ⟨w, hw, ?_, ?_, ?_⟩
  · rw [geometricStructureClosure_closure]
    change ∀ x : ℓ¹(ℕ, ℂ),
      (∀ J : GeometricStructureSpace ℂ ℓ¹(ℕ, ℂ),
        J ∈ {l1ComplexKernelPoint u hu, l1ComplexKernelPoint v hv} → x ∈ J.val) →
      x ∈ (l1ComplexKernelPoint w hw).val
    intro x hx
    have hxu : lp.coefficientFunctional u x = 0 :=
      hx (l1ComplexKernelPoint u hu) (by simp)
    have hxv : lp.coefficientFunctional v x = 0 :=
      hx (l1ComplexKernelPoint v hv) (by simp)
    change lp.coefficientFunctional w x = 0
    dsimp only [w]
    rw [lp.coefficientFunctional_add, lp.coefficientFunctional_smul,
      lp.coefficientFunctional_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hxu, hxv,
      smul_zero, smul_zero, add_zero]
  · intro hwu
    obtain ⟨c, hc⟩ := (l1ComplexKernelPoint_eq_iff_exists_const_ratio w u hw hu).1 hwu
    have hi : c * r = t := by
      rw [← hc i, l1PhaseRatio_mul w u v hu i, hwi]
    have hj : c * s = 1 := by
      rw [← hc j, l1PhaseRatio_mul w u v hu j, hwj]
    apply hts
    calc
      t * s = (c * r) * s := by rw [hi]
      _ = (c * s) * r := by ring
      _ = r := by rw [hj, one_mul]
  · intro hwv
    obtain ⟨c, hc⟩ := (l1ComplexKernelPoint_eq_iff_exists_const_ratio w v hw hv).1 hwv
    exact ht1 (hwi.symm.trans ((hc i).trans ((hc j).symm.trans hwj)))

/-- Linkedness of the actual GSS points is precisely that the relative phase
range has at most two values. Equality of the two kernels covers the one-value case. -/
theorem linked_l1ComplexKernelPoint_iff (u v : ℓ^∞(ℕ, ℂ))
    (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1) :
    (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).Linked
      (l1ComplexKernelPoint u hu) (l1ComplexKernelPoint v hv) ↔
      ∃ r s : ℂ, ∀ n, l1PhaseRatio u v n = r ∨ l1PhaseRatio u v n = s := by
  classical
  constructor
  · intro hlinked
    by_contra htwo
    have hj : ∃ j, l1PhaseRatio u v j ≠ l1PhaseRatio u v 0 := by
      by_contra h
      apply htwo
      refine ⟨l1PhaseRatio u v 0, l1PhaseRatio u v 0, fun n => Or.inl ?_⟩
      by_contra hn
      exact h ⟨n, hn⟩
    obtain ⟨j, hj⟩ := hj
    have hk : ∃ k, l1PhaseRatio u v k ≠ l1PhaseRatio u v 0 ∧
        l1PhaseRatio u v k ≠ l1PhaseRatio u v j := by
      by_contra h
      apply htwo
      refine ⟨l1PhaseRatio u v 0, l1PhaseRatio u v j, fun n => ?_⟩
      by_cases hn : l1PhaseRatio u v n = l1PhaseRatio u v 0
      · exact Or.inl hn
      · right
        by_contra hn'
        exact h ⟨n, hn, hn'⟩
    obtain ⟨k, hk0, hkj⟩ := hk
    rcases hlinked with heq | hclosed
    · obtain ⟨c, hc⟩ := (l1ComplexKernelPoint_eq_iff_exists_const_ratio u v hu hv).1 heq
      exact hj ((hc j).trans (hc 0).symm)
    · exact hclosed (isClosed_pair_l1ComplexKernelPoint_of_three_ratios
        u v hu hv 0 j k hj.symm hk0.symm hkj.symm)
  · rintro ⟨r, s, hcover⟩
    by_cases heq : l1ComplexKernelPoint u hu = l1ComplexKernelPoint v hv
    · exact Or.inl heq
    have hj : ∃ j, l1PhaseRatio u v j ≠ l1PhaseRatio u v 0 := by
      by_contra h
      apply heq
      apply (l1ComplexKernelPoint_eq_iff_exists_const_ratio u v hu hv).2
      refine ⟨l1PhaseRatio u v 0, fun n => ?_⟩
      by_contra hn
      exact h ⟨n, hn⟩
    obtain ⟨j, hj⟩ := hj
    have hc : ∀ n, l1PhaseRatio u v n = l1PhaseRatio u v 0 ∨
        l1PhaseRatio u v n = l1PhaseRatio u v j := by
      intro n
      rcases hcover 0 with h0 | h0 <;> rcases hcover j with hj' | hj'
      · exact (hj (hj'.trans h0.symm)).elim
      · rcases hcover n with hn | hn
        · exact Or.inl (hn.trans h0.symm)
        · exact Or.inr (hn.trans hj'.symm)
      · rcases hcover n with hn | hn
        · exact Or.inr (hn.trans hj'.symm)
        · exact Or.inl (hn.trans h0.symm)
      · exact (hj (hj'.trans h0.symm)).elim
    obtain ⟨w, hw, hcl, hwu, hwv⟩ :=
      exists_l1ComplexKernelPoint_mem_closure_pair_ne u v hu hv 0 j hj.symm hc
    right
    intro hclosed
    have hm := ((geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).isClosed_iff_closure_subset _).1
      hclosed hcl
    rcases (show l1ComplexKernelPoint w hw = l1ComplexKernelPoint u hu ∨
        l1ComplexKernelPoint w hw = l1ComplexKernelPoint v hv by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm) with h | h
    · exact hwu h
    · exact hwv h

end NormedSpace
