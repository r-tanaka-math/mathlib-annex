/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Tactic

/-!
# Closed ideals and the canonical unitization

A norm-closed two-sided ideal in a possibly nonunital complex C-star
algebra is first regarded as an actual complex submodule and then embedded in
the scalar-zero summand of the canonical unitization.  The declarations are
reusable independently of primitive separation.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology BoundedContinuousFunction
open scoped CStarAlgebra ComplexOrder BigOperators

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

section UnitizationIdeal

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- A norm-closed ring ideal of a nonunital C-star algebra is stable under
complex scalars.  The proof uses the canonical approximate unit, so no unit
or unrecorded multiplier action is assumed. -/
theorem TwoSidedIdeal.smul_mem_of_isClosed (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) (c : ℂ) {x : A} (hx : x ∈ J) : c • x ∈ J := by
  letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
  let l := _root_.CStarAlgebra.approximateUnit A
  have hl : Filter.IsIncreasingApproximateUnit l :=
    _root_.CStarAlgebra.increasingApproximateUnit A
  letI : NeBot l := hl.neBot
  have ht : Tendsto (fun e : A => c • (e * x)) l (𝓝 (c • x)) :=
    tendsto_const_nhds.smul (hl.tendsto_mul_right x)
  apply hJ.mem_of_tendsto ht
  filter_upwards with e
  rw [← smul_mul_assoc]
  exact J.mul_mem_left (c • e) x hx

/-- The actual complex submodule carried by a norm-closed two-sided ring
ideal of a possibly nonunital C-star algebra. -/
def TwoSidedIdeal.closedComplexSubmodule (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) : Submodule ℂ A where
  carrier := J
  zero_mem' := J.zero_mem
  add_mem' := fun hx hy => J.add_mem hx hy
  smul_mem' := fun c _ hx => TwoSidedIdeal.smul_mem_of_isClosed J hJ c hx

@[simp]
theorem TwoSidedIdeal.mem_closedComplexSubmodule_iff
    (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) (x : A) :
    x ∈ TwoSidedIdeal.closedComplexSubmodule J hJ ↔ x ∈ J := Iff.rfl

/-- The copy of a norm-closed two-sided ideal in the scalar-zero summand of
the canonical unitization. -/
def unitizationIdeal (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    TwoSidedIdeal (Unitization ℂ A) :=
  TwoSidedIdeal.mk'
    {z | z.fst = 0 ∧ z.snd ∈ J}
    (by constructor <;> simp)
    (fun {x y} hx hy => by
      exact ⟨by simp [hx.1, hy.1], by
        simpa only [Unitization.snd_add] using J.add_mem hx.2 hy.2⟩)
    (fun {x} hx => by
      exact ⟨by simp [hx.1], by
        simpa only [Unitization.snd_neg] using J.neg_mem hx.2⟩)
    (fun {x y} hy => by
      refine ⟨by simp [hy.1], ?_⟩
      rw [Unitization.snd_mul, hy.1]
      simp only [zero_smul, add_zero]
      exact J.add_mem
        (TwoSidedIdeal.smul_mem_of_isClosed J hJ x.fst hy.2)
        (J.mul_mem_left _ _ hy.2))
    (fun {x y} hx => by
      refine ⟨by simp [hx.1], ?_⟩
      rw [Unitization.snd_mul, hx.1]
      simp only [zero_smul, zero_add]
      exact J.add_mem
        (TwoSidedIdeal.smul_mem_of_isClosed J hJ y.fst hx.2)
        (J.mul_mem_right _ _ hx.2))

@[simp]
theorem mem_unitizationIdeal_iff (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) (z : Unitization ℂ A) :
    z ∈ unitizationIdeal J hJ ↔ z.fst = 0 ∧ z.snd ∈ J := by
  simp only [unitizationIdeal, TwoSidedIdeal.mem_mk', Set.mem_setOf_eq]

@[simp]
theorem inr_mem_unitizationIdeal_iff (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) (a : A) :
    Unitization.inr a ∈ unitizationIdeal J hJ ↔ a ∈ J := by
  simp only [mem_unitizationIdeal_iff, Unitization.fst_inr, Unitization.snd_inr, true_and]

/-- Membership in the scalar-zero unitization ideal gives the literal `inr`
form needed by the chosen Hahn--Banach extension. -/
theorem eq_inr_snd_of_mem_unitizationIdeal (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) {z : Unitization ℂ A}
    (hz : z ∈ unitizationIdeal J hJ) : z = Unitization.inr z.snd := by
  apply Unitization.ext
  · have hz0 := ((mem_unitizationIdeal_iff J hJ z).1 hz).1
    simpa only [Unitization.fst_inr] using hz0
  · simp

/-- Closedness is inherited from the original ideal and the two continuous
coordinate maps of the genuine unitization norm. -/
theorem isClosed_unitizationIdeal (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) :
    IsClosed (unitizationIdeal J hJ : Set (Unitization ℂ A)) := by
  rw [show (unitizationIdeal J hJ : Set (Unitization ℂ A)) =
      {z | z.fst = 0} ∩ (fun z : Unitization ℂ A => z.snd) ⁻¹' (J : Set A) by
    ext z
    change (z ∈ unitizationIdeal J hJ) ↔ z.fst = 0 ∧ z.snd ∈ J
    exact mem_unitizationIdeal_iff J hJ z]
  exact (isClosed_eq Unitization.continuous_fst continuous_const).inter
    (hJ.preimage Unitization.continuous_snd)

end UnitizationIdeal

end MathlibAnnex.Analysis.CStarAlgebra
