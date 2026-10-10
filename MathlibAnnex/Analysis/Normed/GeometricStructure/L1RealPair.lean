/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.Normed.GeometricStructure.L1Kernel
import MathlibAnnex.Analysis.Normed.GeometricStructure.FilterPresentation
import MathlibAnnex.Analysis.Normed.Module.DualKernelPair

/-!
# Closed pairs in the real ℓ¹ geometric structure space

After multiplying each real sign sequence by its first sign, both first
coefficients are one. A differing coordinate then forces both `|a+b|=1` and
`|a-b|=1` for a functional in the span of two such functionals. Over ℝ this
forces one scalar to vanish. The two-kernel factorization is applied to the
individual continuous linear functionals, never to a kernel union as a
submodule. The argument is not applied to complex phases.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set
open scoped lp ENNReal

namespace NormedSpace

/-- For real sign coefficients, a kernel containing the intersection of two
 distinct coefficient kernels is one of those two kernels. -/
theorem preimage_zero_coefficientFunctional_eq_or_eq_of_inter_subset_real
    (u v w : ℓ^∞(ℕ, ℝ)) (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1)
    (hw : ∀ n, ‖w n‖ = 1)
    (hne : (lp.coefficientFunctional u : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} ≠
      (lp.coefficientFunctional v : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0})
    (hinter : ((lp.coefficientFunctional u : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} ∩
      (lp.coefficientFunctional v : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0}) ⊆
        (lp.coefficientFunctional w : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0}) :
    (lp.coefficientFunctional w : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} =
        (lp.coefficientFunctional u : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} ∨
      (lp.coefficientFunctional w : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} =
        (lp.coefficientFunctional v : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} := by
  classical
  have hsign {a : ℝ} (ha : ‖a‖ = 1) : a = 1 ∨ a = -1 := by
    rw [Real.norm_eq_abs] at ha
    rcases le_total 0 a with hp | hm
    · left
      rwa [abs_of_nonneg hp] at ha
    · right
      rw [abs_of_nonpos hm] at ha
      linarith
  have hu0 : u 0 ≠ 0 := norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero)
  have hv0 : v 0 ≠ 0 := norm_ne_zero_iff.1 (by rw [hv]; exact one_ne_zero)
  let u' : ℓ^∞(ℕ, ℝ) := u 0 • u
  let v' : ℓ^∞(ℕ, ℝ) := v 0 • v
  have hu' (n : ℕ) : ‖u' n‖ = 1 := by
    change ‖u 0 * u n‖ = 1
    simp only [norm_mul, hu, mul_one]
  have hv' (n : ℕ) : ‖v' n‖ = 1 := by
    change ‖v 0 * v n‖ = 1
    simp only [norm_mul, hv, mul_one]
  have hu'0 : u' 0 = 1 := by
    change u 0 * u 0 = 1
    rcases hsign (hu 0) with h | h <;> rw [h] <;> norm_num
  have hv'0 : v' 0 = 1 := by
    change v 0 * v 0 = 1
    rcases hsign (hv 0) with h | h <;> rw [h] <;> norm_num
  have hku : (lp.coefficientFunctional u' : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} =
      (lp.coefficientFunctional u : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} :=
    lp.preimage_zero_coefficientFunctional_smul u hu0
  have hkv : (lp.coefficientFunctional v' : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} =
      (lp.coefficientFunctional v : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} :=
    lp.preimage_zero_coefficientFunctional_smul v hv0
  have huv : u' ≠ v' := by
    intro h
    apply hne
    exact hku.symm.trans ((congrArg
      (fun q : ℓ^∞(ℕ, ℝ) => (lp.coefficientFunctional q : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0}) h).trans hkv)
  have hex : ∃ n, u' n ≠ v' n := by
    by_contra hn
    apply huv
    apply Subtype.ext
    funext n
    by_contra h
    exact hn ⟨n, h⟩
  obtain ⟨n, hn⟩ := hex
  have hker : (lp.coefficientFunctional u').ker ⊓ (lp.coefficientFunctional v').ker ≤
      (lp.coefficientFunctional w).ker := by
    intro a ha
    have hau : a ∈ (lp.coefficientFunctional u' : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} := ha.1
    have hav : a ∈ (lp.coefficientFunctional v' : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} := ha.2
    rw [hku] at hau
    rw [hkv] at hav
    exact hinter ⟨hau, hav⟩
  obtain ⟨a, b, hwf⟩ :=
    (ContinuousLinearMap.inf_ker_le_ker_iff_exists_smul_add_smul
      (lp.coefficientFunctional u') (lp.coefficientFunctional v')
      (lp.coefficientFunctional w)).1 hker
  have hvalues (j : ℕ) : w j = a * u' j + b * v' j := by
    have hj := congrArg (fun q : StrongDual ℝ ℓ¹(ℕ, ℝ) => q (lp.single 1 j 1)) hwf
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      lp.coefficientFunctional_single, one_mul, smul_eq_mul] using hj
  have hplus : ‖a + b‖ = 1 := by
    have h := hw 0
    simpa only [hvalues 0, hu'0, hv'0, mul_one] using h
  have hminus : ‖a - b‖ = 1 := by
    rcases hsign (hu' n) with hU | hU <;> rcases hsign (hv' n) with hV | hV
    · exact (hn (hU.trans hV.symm)).elim
    · have h := hw n
      simpa only [hvalues n, hU, hV, mul_one, mul_neg_one, sub_eq_add_neg] using h
    · have h := hw n
      have hneg : -a + b = -(a - b) := by abel
      simpa only [hvalues n, hU, hV, mul_one, mul_neg_one, hneg, norm_neg] using h
    · exact (hn (hU.trans hV.symm)).elim
  have hab : a = 0 ∨ b = 0 := by
    rcases hsign hplus with hp | hp <;> rcases hsign hminus with hm | hm
    · right; linarith
    · left; linarith
    · left; linarith
    · right; linarith
  have hwne : lp.coefficientFunctional w ≠ 0 := by
    apply norm_ne_zero_iff.1
    rw [lp.norm_coefficientFunctional_eq_one_of_forall_norm_eq_one w hw]
    exact one_ne_zero
  rcases hab with ha | hb
  · have hbne : b ≠ 0 := by
      intro hb
      apply hwne
      simpa only [ha, hb, zero_smul, add_zero] using hwf
    right
    calc
      (lp.coefficientFunctional w : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} =
          (lp.coefficientFunctional (b • v') : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} := by
        rw [lp.coefficientFunctional_smul, hwf, ha, zero_smul, zero_add]
      _ = (lp.coefficientFunctional v' : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} :=
        lp.preimage_zero_coefficientFunctional_smul v' hbne
      _ = (lp.coefficientFunctional v : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} := hkv
  · have hane : a ≠ 0 := by
      intro ha
      apply hwne
      simpa only [ha, hb, zero_smul, add_zero] using hwf
    left
    calc
      (lp.coefficientFunctional w : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} =
          (lp.coefficientFunctional (a • u') : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} := by
        rw [lp.coefficientFunctional_smul, hwf, hb, zero_smul, add_zero]
      _ = (lp.coefficientFunctional u' : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} :=
        lp.preimage_zero_coefficientFunctional_smul u' hane
      _ = (lp.coefficientFunctional u : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} := hku

/-- Every two-point subset of the original real ℓ¹ GSS is closed. This is not
 finite-union preservation for arbitrary closed sets. -/
theorem isClosed_pair_geometricStructureClosure_l1_real
    (I J : GeometricStructureSpace ℝ ℓ¹(ℕ, ℝ)) :
    (geometricStructureClosure ℝ ℓ¹(ℕ, ℝ)).IsClosed {I, J} := by
  classical
  by_cases hIJ : I = J
  · subst J
    simpa using isT1_geometricStructureClosure ℝ ℓ¹(ℕ, ℝ) I
  apply ((geometricStructureClosure ℝ ℓ¹(ℕ, ℝ)).isClosed_iff_closure_subset _).2
  intro K hK
  rw [geometricStructureClosure_closure] at hK
  change (∀ a : ℓ¹(ℕ, ℝ),
    (∀ L : GeometricStructureSpace ℝ ℓ¹(ℕ, ℝ),
      L ∈ ({I, J} : Set (GeometricStructureSpace ℝ ℓ¹(ℕ, ℝ))) → a ∈ L.val) →
      a ∈ K.val) at hK
  obtain ⟨u, hu, huI⟩ := (mem_geometricStructureFamily_l1_iff ℝ I.val).1 I.property
  obtain ⟨v, hv, hvJ⟩ := (mem_geometricStructureFamily_l1_iff ℝ J.val).1 J.property
  obtain ⟨w, hw, hwK⟩ := (mem_geometricStructureFamily_l1_iff ℝ K.val).1 K.property
  have hne : (lp.coefficientFunctional u : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} ≠
      (lp.coefficientFunctional v : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} := by
    intro h
    exact hIJ (Subtype.ext (huI.symm.trans (h.trans hvJ)))
  have hinter : ((lp.coefficientFunctional u : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} ∩
      (lp.coefficientFunctional v : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0}) ⊆
        (lp.coefficientFunctional w : ℓ¹(ℕ, ℝ) → ℝ) ⁻¹' {0} := by
    rw [huI, hvJ, hwK]
    intro a ha
    apply hK a
    intro L hL
    rcases (show L = I ∨ L = J by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hL)
      with rfl | rfl
    · exact ha.1
    · exact ha.2
  rcases preimage_zero_coefficientFunctional_eq_or_eq_of_inter_subset_real
      u v w hu hv hw hne hinter with h | h
  · have hKI : K = I := Subtype.ext (hwK.symm.trans (h.trans huI))
    exact Set.mem_insert_iff.2 (Or.inl hKI)
  · have hKJ : K = J := Subtype.ext (hwK.symm.trans (h.trans hvJ))
    exact Set.mem_insert_iff.2 (Or.inr (Set.mem_singleton_iff.2 hKJ))

end NormedSpace
