import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Order.AtTopBotIxx
import Mathlib.Topology.Path

/-!
# Locally finite concatenation of paths

This file glues a bi-infinite chain of ordinary unit-interval paths into a
continuous map on `ℝ`.  The construction is purely topological; negative-time
constant segments can be used to obtain a path on `[0, ∞)` with a specified
value at zero.
-/

set_option autoImplicit false

noncomputable section

open Filter Set TopologicalSpace

namespace MathlibAnnex.Path

variable {X : Type*} [TopologicalSpace X]

/-- The value of the locally finite concatenation at time `t`.  The path with
index `floor t` is evaluated at the fractional part of `t`. -/
def infiniteConcat (x : ℤ → X) (p : ∀ n, Path (x n) (x (n + 1))) (t : ℝ) : X :=
  p ⌊t⌋ ⟨Int.fract t, unitInterval.fract_mem t⟩

/-- The affine reparametrization of the `n`th path on `[n,n+1]`. -/
def intervalPath (x : ℤ → X) (p : ∀ n, Path (x n) (x (n + 1))) (n : ℤ) :
    Set.Icc (n : ℝ) (n + 1 : ℝ) → X := fun t =>
  p n ⟨(t : ℝ) - n, by
    constructor
    · exact sub_nonneg.mpr t.property.1
    · linarith [t.property.2]⟩

theorem continuous_intervalPath (x : ℤ → X)
    (p : ∀ n, Path (x n) (x (n + 1))) (n : ℤ) :
    Continuous (intervalPath x p n) := by
  apply (p n).continuous.comp
  exact (continuous_subtype_val.sub continuous_const).subtype_mk _

theorem infiniteConcat_eq_intervalPath (x : ℤ → X)
    (p : ∀ n, Path (x n) (x (n + 1))) (n : ℤ)
    (t : Set.Icc (n : ℝ) (n + 1 : ℝ)) :
    infiniteConcat x p t = intervalPath x p n t := by
  by_cases ht : (t : ℝ) < n + 1
  · have hfloor : ⌊(t : ℝ)⌋ = n := Int.floor_eq_iff.mpr ⟨t.property.1, ht⟩
    have hfract : Int.fract (t : ℝ) = (t : ℝ) - n := by
      rw [Int.fract, hfloor]
    unfold infiniteConcat intervalPath
    rw [hfloor]
    congr 1
    apply Subtype.ext
    exact hfract
  · have ht' : (t : ℝ) = n + 1 := le_antisymm t.property.2 (not_lt.mp ht)
    have hfloor : ⌊(t : ℝ)⌋ = n + 1 := by
      rw [ht']
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num
    have hfract : Int.fract (t : ℝ) = 0 := by
      rw [Int.fract, hfloor, ht']
      norm_num
    rw [infiniteConcat, intervalPath, hfloor]
    rw [show (⟨Int.fract (t : ℝ), unitInterval.fract_mem (t : ℝ)⟩ : unitInterval) = 0 by
      apply Subtype.ext
      exact hfract]
    rw [(p (n + 1)).source]
    have harg :
        (⟨(t : ℝ) - (n : ℝ), by
          constructor
          · exact sub_nonneg.mpr t.property.1
          · linarith [t.property.2]⟩ : unitInterval) = 1 := by
      apply Subtype.ext
      change (t : ℝ) - (n : ℝ) = 1
      linarith [ht']
    rw [harg, (p n).target]

theorem continuousOn_infiniteConcat_interval (x : ℤ → X)
    (p : ∀ n, Path (x n) (x (n + 1))) (n : ℤ) :
    ContinuousOn (infiniteConcat x p) (Set.Icc (n : ℝ) (n + 1 : ℝ)) := by
  rw [continuousOn_iff_continuous_restrict]
  have h := continuous_intervalPath x p n
  apply h.congr
  intro t
  exact (infiniteConcat_eq_intervalPath x p n t).symm

theorem continuous_infiniteConcat (x : ℤ → X)
    (p : ∀ n, Path (x n) (x (n + 1))) :
    Continuous (infiniteConcat x p) := by
  have hlocal : LocallyFinite
      (fun n : ℤ => Set.Icc (n : ℝ) (n + 1 : ℝ)) := by
    apply locallyFinite_Icc_of_tendsto
    · exact tendsto_intCast_atTop_atTop
    · exact tendsto_atBot_add_const_right _ 1
        ((tendsto_intCast_atBot_iff).2 tendsto_id)
  apply hlocal.continuous
  · ext t
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨⌊t⌋, Int.floor_le t, (Int.lt_floor_add_one t).le⟩
  · intro n
    exact isClosed_Icc
  · exact continuousOn_infiniteConcat_interval x p

end MathlibAnnex.Path
