/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.C0DirectSum

/-! # The c₀ ideal of a dependent bounded product
Exact R34 OPERATOR author blocks, separated from primitive-spectrum clients.
R35 repairs the left endpoint; the downstream dependency audit is recorded separately.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Filter Set Topology
open scoped BigOperators CStarAlgebra ENNReal

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u uK

namespace C0DirectSum

universe uι uA

variable {ι : Type uι} (A : ι → Type uA)
variable [∀ i, NonUnitalCStarAlgebra (A i)]

/-- Right multiplication by an arbitrary bounded family preserves vanishing at
infinity. -/
theorem VanishesAtInfinity.mul_right_bounded {x : lp A ∞}
    (hx : VanishesAtInfinity A x) (y : lp A ∞) :
    VanishesAtInfinity A (x * y) := by
  intro ε hε
  let d : ℝ := ‖y‖ + 1
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hfinite := hx (ε / d) (div_pos hε hd)
  refine hfinite.subset ?_
  intro i hi
  change ε / d ≤ ‖x i‖
  apply (div_le_iff₀ hd).2
  calc
    ε ≤ ‖x i * y i‖ := hi
    _ ≤ ‖x i‖ * ‖y i‖ := norm_mul_le _ _
    _ ≤ ‖x i‖ * d := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      dsimp [d]
      exact (lp.norm_apply_le_norm (by simp) y i).trans
        (le_add_of_nonneg_right zero_le_one)

/-- Left multiplication by an arbitrary bounded family preserves vanishing at
infinity. -/
theorem VanishesAtInfinity.mul_left_bounded (x : lp A ∞) {y : lp A ∞}
    (hy : VanishesAtInfinity A y) :
    VanishesAtInfinity A (x * y) := by
  intro ε hε
  let d : ℝ := ‖x‖ + 1
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hfinite := hy (ε / d) (div_pos hε hd)
  refine hfinite.subset ?_
  intro i hi
  change ε / d ≤ ‖y i‖
  apply (div_le_iff₀ hd).2
  calc
    ε ≤ ‖x i * y i‖ := hi
    _ ≤ ‖x i‖ * ‖y i‖ := norm_mul_le _ _
    _ ≤ d * ‖y i‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      dsimp [d]
      exact (lp.norm_apply_le_norm (by simp) x i).trans
        (le_add_of_nonneg_right zero_le_one)
    _ = ‖y i‖ * d := mul_comm _ _

/-- The actual c₀-families form an algebraic two-sided ideal of the dependent
bounded product. -/
def boundedProductIdeal : TwoSidedIdeal (lp A ∞) :=
  TwoSidedIdeal.mk'
    {x | VanishesAtInfinity A x}
    (vanishesAtInfinity_zero A)
    (fun hx hy => hx.add (A := A) hy)
    (fun hx => hx.neg (A := A))
    (fun hy => hy.mul_left_bounded (A := A) _)
    (fun hx => hx.mul_right_bounded (A := A) _)

@[simp]
theorem mem_boundedProductIdeal (x : lp A ∞) :
    x ∈ boundedProductIdeal A ↔ VanishesAtInfinity A x := by
  simp [boundedProductIdeal]

/-- The bounded-product c₀-ideal has exactly the same carrier as the concrete
c₀ star subalgebra. -/
theorem coe_boundedProductIdeal :
    (boundedProductIdeal A : Set (lp A ∞)) = starSubalgebra A := by
  ext x
  change (x ∈ boundedProductIdeal A) ↔ (x ∈ starSubalgebra A)
  rw [mem_boundedProductIdeal, mem_starSubalgebra]

/-- The bounded-product c₀-ideal is norm closed. -/
theorem isClosed_boundedProductIdeal :
    IsClosed (boundedProductIdeal A : Set (lp A ∞)) := by
  rw [coe_boundedProductIdeal]
  exact isClosed_starSubalgebra A

end C0DirectSum

end MathlibAnnex.Analysis.CStarAlgebra
