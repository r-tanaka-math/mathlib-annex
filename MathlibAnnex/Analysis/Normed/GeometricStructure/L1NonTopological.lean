/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.L1Kernel
public import MathlibAnnex.Analysis.Normed.GeometricStructure.FilterPresentation
public import MathlibAnnex.Topology.ClosureSpace.Topological
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# A nonclosed triple in the geometric structure space of ℓ¹

The four sign patterns are (1,1,...), (1,-1,-1,...), (-1,1,-1,...),
and (-1,-1,1,1,...). Their actual continuous coefficient functionals
have four distinct kernels. The fourth functional is minus the sum of the
first three. Thus its kernel belongs to the hull-kernel closure of the first
three points without being one of them. This works over both ℝ and ℂ and
concerns the original face-defined GSS. In the real case it is consistent
with the previously proved closedness of every pair.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set
open scoped lp ENNReal

universe u

namespace NormedSpace

variable (𝕜 : Type u) [RCLike 𝕜]

/-- Four bounded unimodular sign patterns, with coordinates indexed from zero. -/
def l1SignCoefficients (i : Fin 4) : ℓ^∞(ℕ, 𝕜) :=
  lp.inftyOfNormOne
    (fun n => if i = 0 then 1 else if i = 1 then (if n = 0 then 1 else -1)
      else if i = 2 then (if n = 1 then 1 else -1)
      else if n = 0 then -1 else if n = 1 then -1 else 1)
    (by intro n; split_ifs <;> simp)

/-- Each coordinate of each of the four patterns has norm one. -/
theorem norm_l1SignCoefficients_apply (i : Fin 4) (n : ℕ) :
    ‖l1SignCoefficients 𝕜 i n‖ = 1 := by
  simp only [l1SignCoefficients, lp.inftyOfNormOne_apply]
  split_ifs <;> simp

/-- The actual GSS point associated to one of the four sign patterns. -/
def l1SignKernelPoint (i : Fin 4) : GeometricStructureSpace 𝕜 ℓ¹(ℕ, 𝕜) :=
  ⟨(lp.coefficientFunctional (l1SignCoefficients 𝕜 i) : ℓ¹(ℕ, 𝕜) → 𝕜) ⁻¹' {0},
    preimage_zero_coefficientFunctional_mem_geometricStructureFamily 𝕜
      (l1SignCoefficients 𝕜 i) (norm_l1SignCoefficients_apply 𝕜 i)⟩

/-- Three two-coordinate test vectors distinguish all four kernel points. -/
theorem l1SignKernelPoint_injective : Function.Injective (l1SignKernelPoint 𝕜) := by
  intro i j hij
  let a : ℓ¹(ℕ, 𝕜) := lp.single 1 0 1 - lp.single 1 1 1
  let b : ℓ¹(ℕ, 𝕜) := lp.single 1 0 1 - lp.single 1 2 1
  let c : ℓ¹(ℕ, 𝕜) := lp.single 1 1 1 - lp.single 1 2 1
  have ha := congrArg (fun I : GeometricStructureSpace 𝕜 ℓ¹(ℕ, 𝕜) => a ∈ I.val) hij
  have hb := congrArg (fun I : GeometricStructureSpace 𝕜 ℓ¹(ℕ, 𝕜) => b ∈ I.val) hij
  have hc := congrArg (fun I : GeometricStructureSpace 𝕜 ℓ¹(ℕ, 𝕜) => c ∈ I.val) hij
  simp only [l1SignKernelPoint, Set.mem_preimage, Set.mem_singleton_iff,
    a, b, c, map_sub, lp.coefficientFunctional_single, l1SignCoefficients,
    lp.inftyOfNormOne_apply, one_mul] at ha hb hc
  fin_cases i
  all_goals fin_cases j
  all_goals norm_num [Fin.ext_iff] at *

/-- The fourth coefficient functional is the negative sum of the first three. -/
theorem coefficientFunctional_l1SignCoefficients_three :
    lp.coefficientFunctional (l1SignCoefficients 𝕜 3) =
      -lp.coefficientFunctional (l1SignCoefficients 𝕜 0) -
        lp.coefficientFunctional (l1SignCoefficients 𝕜 1) -
        lp.coefficientFunctional (l1SignCoefficients 𝕜 2) := by
  have hcoeff : l1SignCoefficients 𝕜 3 =
      -l1SignCoefficients 𝕜 0 - l1SignCoefficients 𝕜 1 - l1SignCoefficients 𝕜 2 := by
    apply Subtype.ext
    funext n
    change l1SignCoefficients 𝕜 3 n =
      -l1SignCoefficients 𝕜 0 n - l1SignCoefficients 𝕜 1 n - l1SignCoefficients 𝕜 2 n
    by_cases hn0 : n = 0 <;> by_cases hn1 : n = 1 <;>
      norm_num [l1SignCoefficients, Fin.ext_iff, hn0, hn1]
  rw [hcoeff, lp.coefficientFunctional_sub, lp.coefficientFunctional_sub,
    lp.coefficientFunctional_neg]

/-- The fourth kernel is in the closure of the first three actual GSS points. -/
theorem l1SignKernelPoint_mem_closure_triple :
    l1SignKernelPoint 𝕜 3 ∈ (geometricStructureClosure 𝕜 ℓ¹(ℕ, 𝕜)).closure
      {l1SignKernelPoint 𝕜 0, l1SignKernelPoint 𝕜 1, l1SignKernelPoint 𝕜 2} := by
  rw [geometricStructureClosure_closure]
  change ∀ a : ℓ¹(ℕ, 𝕜),
    (∀ p : GeometricStructureSpace 𝕜 ℓ¹(ℕ, 𝕜),
      p ∈ {l1SignKernelPoint 𝕜 0, l1SignKernelPoint 𝕜 1, l1SignKernelPoint 𝕜 2} → a ∈ p.val) →
    a ∈ (l1SignKernelPoint 𝕜 3).val
  intro a ha
  have h0 : lp.coefficientFunctional (l1SignCoefficients 𝕜 0) a = 0 :=
    ha (l1SignKernelPoint 𝕜 0) (by simp)
  have h1 : lp.coefficientFunctional (l1SignCoefficients 𝕜 1) a = 0 :=
    ha (l1SignKernelPoint 𝕜 1) (by simp)
  have h2 : lp.coefficientFunctional (l1SignCoefficients 𝕜 2) a = 0 :=
    ha (l1SignKernelPoint 𝕜 2) (by simp)
  change lp.coefficientFunctional (l1SignCoefficients 𝕜 3) a = 0
  have h := congrArg (fun f : StrongDual 𝕜 ℓ¹(ℕ, 𝕜) => f a)
    (coefficientFunctional_l1SignCoefficients_three 𝕜)
  change lp.coefficientFunctional (l1SignCoefficients 𝕜 3) a =
    -lp.coefficientFunctional (l1SignCoefficients 𝕜 0) a -
      lp.coefficientFunctional (l1SignCoefficients 𝕜 1) a -
      lp.coefficientFunctional (l1SignCoefficients 𝕜 2) a at h
  simpa only [h0, h1, h2, neg_zero, sub_zero] using h

/-- This is a genuinely new point, not a repetition in the three-element set. -/
theorem l1SignKernelPoint_notMem_triple :
    l1SignKernelPoint 𝕜 3 ∉
      ({l1SignKernelPoint 𝕜 0, l1SignKernelPoint 𝕜 1, l1SignKernelPoint 𝕜 2} :
        Set (GeometricStructureSpace 𝕜 ℓ¹(ℕ, 𝕜))) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
    (l1SignKernelPoint_injective 𝕜).eq_iff]
  norm_num [Fin.ext_iff]

/-- A specific triple in the ℓ¹ GSS is not closed. -/
theorem not_isClosed_triple_l1SignKernelPoint :
    ¬ (geometricStructureClosure 𝕜 ℓ¹(ℕ, 𝕜)).IsClosed
      {l1SignKernelPoint 𝕜 0, l1SignKernelPoint 𝕜 1, l1SignKernelPoint 𝕜 2} := by
  intro h
  exact l1SignKernelPoint_notMem_triple 𝕜
    (((geometricStructureClosure 𝕜 ℓ¹(ℕ, 𝕜)).isClosed_iff_closure_subset _).1 h
      (l1SignKernelPoint_mem_closure_triple 𝕜))

/-- REF42 Theorem 5.8: the original ℓ¹ GSS is not topologizable, over ℝ or ℂ. -/
theorem not_isTopologizable_geometricStructureClosure_l1 :
    ¬ (geometricStructureClosure 𝕜 ℓ¹(ℕ, 𝕜)).IsTopologizable := by
  intro htop
  apply not_isClosed_triple_l1SignKernelPoint 𝕜
  have hT1 := isT1_geometricStructureClosure 𝕜 ℓ¹(ℕ, 𝕜)
  simpa only [Set.singleton_union] using
    htop.isClosed_union (hT1 (l1SignKernelPoint 𝕜 0))
      (htop.isClosed_union (hT1 (l1SignKernelPoint 𝕜 1)) (hT1 (l1SignKernelPoint 𝕜 2)))

end NormedSpace
