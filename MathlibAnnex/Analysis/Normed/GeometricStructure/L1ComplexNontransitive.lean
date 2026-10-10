/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.Normed.GeometricStructure.L1ComplexLinked
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# Nontransitivity of Linked on complex ℓ¹

The three nonempty coordinate classes are `{0}`, `{1}`, and their complement
(which contains `2`). The three phase sequences have classwise values
`(1,1,1)`, `(1,1,I)`, and `(1,I,-1)`. Consecutive ratios take two values, but
the outer ratio takes the three distinct values `1`, `-I`, and `-1`.
All three kernels are actual points of the original face-defined GSS.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set ComplexConjugate
open scoped lp ENNReal

namespace NormedSpace

/-- Three explicit bounded unimodular sequences on three nonempty coordinate classes. -/
def l1ThreeClassPhase (k : Fin 3) : ℓ^∞(ℕ, ℂ) :=
  lp.inftyOfNormOne
    (fun n => if k = 0 then 1 else if k = 1 then
      (if n = 0 ∨ n = 1 then 1 else Complex.I) else
      (if n = 0 then 1 else if n = 1 then Complex.I else -1))
    (fun n => by split_ifs <;> simp)

/-- Every coefficient in every one of these three sequences has norm one. -/
theorem norm_l1ThreeClassPhase (k : Fin 3) (n : ℕ) : ‖l1ThreeClassPhase k n‖ = 1 := by
  dsimp [l1ThreeClassPhase, lp.inftyOfNormOne]
  split_ifs <;> simp

/-- An explicit chain of two links whose distinct endpoints are not linked. -/
theorem exists_linked_linked_not_linked_geometricStructureClosure_l1Complex :
    ∃ I J K : GeometricStructureSpace ℂ ℓ¹(ℕ, ℂ),
      I ≠ J ∧ I ≠ K ∧ J ≠ K ∧
      (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).Linked I J ∧
      (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).Linked J K ∧
      ¬ (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).Linked I K := by
  let u := l1ThreeClassPhase 0
  let v := l1ThreeClassPhase 1
  let w := l1ThreeClassPhase 2
  have hu : ∀ n, ‖u n‖ = 1 := norm_l1ThreeClassPhase 0
  have hv : ∀ n, ‖v n‖ = 1 := norm_l1ThreeClassPhase 1
  have hw : ∀ n, ‖w n‖ = 1 := norm_l1ThreeClassPhase 2
  have hne (a b : ℓ^∞(ℕ, ℂ)) (ha : ∀ n, ‖a n‖ = 1) (hb : ∀ n, ‖b n‖ = 1)
      (i j : ℕ) (hij : l1PhaseRatio a b i ≠ l1PhaseRatio a b j) :
      l1ComplexKernelPoint a ha ≠ l1ComplexKernelPoint b hb := by
    intro h
    obtain ⟨r, hr⟩ := (l1ComplexKernelPoint_eq_iff_exists_const_ratio a b ha hb).1 h
    exact hij ((hr i).trans (hr j).symm)
  have huv : (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).Linked
      (l1ComplexKernelPoint u hu) (l1ComplexKernelPoint v hv) := by
    apply (linked_l1ComplexKernelPoint_iff u v hu hv).2
    refine ⟨1, -Complex.I, fun n => ?_⟩
    by_cases hn : n = 0 ∨ n = 1
    · left
      simp [l1PhaseRatio, u, v, l1ThreeClassPhase, hn]
    · right
      simp [l1PhaseRatio, u, v, l1ThreeClassPhase, hn]
  have hvw : (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).Linked
      (l1ComplexKernelPoint v hv) (l1ComplexKernelPoint w hw) := by
    apply (linked_l1ComplexKernelPoint_iff v w hv hw).2
    refine ⟨1, -Complex.I, fun n => ?_⟩
    by_cases h0 : n = 0
    · left
      simp [l1PhaseRatio, v, w, l1ThreeClassPhase, h0]
    · right
      by_cases h1 : n = 1
      · simp [l1PhaseRatio, v, w, l1ThreeClassPhase, h0, h1]
      · simp [l1PhaseRatio, v, w, l1ThreeClassPhase, h0, h1]
  have huvne : l1ComplexKernelPoint u hu ≠ l1ComplexKernelPoint v hv := by
    apply hne u v hu hv 0 2
    simp [l1PhaseRatio, u, v, l1ThreeClassPhase, Complex.ext_iff]
  have hvwne : l1ComplexKernelPoint v hv ≠ l1ComplexKernelPoint w hw := by
    apply hne v w hv hw 0 1
    simp [l1PhaseRatio, v, w, l1ThreeClassPhase, Complex.ext_iff]
  have h01 : l1PhaseRatio u w 0 ≠ l1PhaseRatio u w 1 := by
    simp [l1PhaseRatio, u, w, l1ThreeClassPhase, Complex.ext_iff]
  have h02 : l1PhaseRatio u w 0 ≠ l1PhaseRatio u w 2 := by
    simp [l1PhaseRatio, u, w, l1ThreeClassPhase, Complex.ext_iff] <;> norm_num
  have h12 : l1PhaseRatio u w 1 ≠ l1PhaseRatio u w 2 := by
    simp [l1PhaseRatio, u, w, l1ThreeClassPhase, Complex.ext_iff]
  have huwne := hne u w hu hw 0 1 h01
  have hclosed := isClosed_pair_l1ComplexKernelPoint_of_three_ratios u w hu hw
    0 1 2 h01 h02 h12
  refine ⟨l1ComplexKernelPoint u hu, l1ComplexKernelPoint v hv,
    l1ComplexKernelPoint w hw, huvne, huwne, hvwne, huv, hvw, ?_⟩
  rintro (heq | hnclosed)
  · exact huwne heq
  · exact hnclosed hclosed

/-- Remark 4.12: linkedness itself is not a transitive relation on the actual GSS. -/
theorem not_transitive_linked_geometricStructureClosure_l1Complex :
    ¬ Transitive (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).Linked := by
  intro h
  obtain ⟨I, J, K, _, _, _, hIJ, hJK, hIK⟩ :=
    exists_linked_linked_not_linked_geometricStructureClosure_l1Complex
  exact hIK (h hIJ hJK)

end NormedSpace
