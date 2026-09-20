import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Compactness.Compact

/-!
# One simultaneous annihilator from compact finite approximate witnesses

Finite witnesses may change with the finite set and positive tolerance.
Compactness chooses ONE point annihilating every test, while every closed
constraint already built into K is preserved. No sequence or separability
assumption is used. C04 source candidate, unbuilt.
-/
set_option autoImplicit false
noncomputable section
open Set Topology

namespace MathlibAnnex.CompactAnnihilator
universe u v
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {I : Type v}

private theorem exists_common_positive_radius (s : Finset I) (r : I → ℝ)
    (hr : ∀ i, 0 < r i) : ∃ delta : ℝ, 0 < delta ∧ ∀ i ∈ s, delta ≤ r i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨delta, hd, hs⟩ := ih
      refine ⟨min delta (r i), lt_min hd (hr i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hs j hj)

/-- This proves the infinite simultaneous selection, rather than assuming
one global limiting point or a mean as an input. -/
theorem exists_mem_annihilating (K : Set (WeakDual ℂ X)) (hK : IsCompact K)
    (test : I → X)
    (hfinite : ∀ s : Finset I, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ omega ∈ K, ∀ i ∈ s, ‖omega (test i)‖ < epsilon) :
    ∃ omega ∈ K, ∀ i, omega (test i) = 0 := by
  classical
  let J := I × {r : ℝ // 0 < r}
  let C : J → Set (WeakDual ℂ X) := fun j => {w | ‖w (test j.1)‖ ≤ j.2.val}
  have hclosed (j : J) : IsClosed (C j) :=
    isClosed_le (WeakDual.eval_continuous (test j.1)).norm continuous_const
  have hne : (K ∩ ⋂ j : J, C j).Nonempty := by
    apply hK.inter_iInter_nonempty C hclosed
    intro s
    obtain ⟨delta, hd, hsmall⟩ := exists_common_positive_radius s
      (fun j : J => j.2.val) (fun j => j.2.property)
    obtain ⟨w, hw, ht⟩ := hfinite (s.image Prod.fst) delta hd
    refine ⟨w, hw, ?_⟩
    simp only [mem_iInter]
    intro j hj
    exact (le_of_lt (ht j.1 (Finset.mem_image.mpr ⟨j, hj, rfl⟩))).trans (hsmall j hj)
  obtain ⟨w, hw, hall⟩ := hne
  refine ⟨w, hw, fun i => ?_⟩
  apply norm_eq_zero.mp
  by_contra h
  have hpos : 0 < ‖w (test i)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
  have hc := (mem_iInter.mp hall) (i, ⟨‖w (test i)‖ / 2, half_pos hpos⟩)
  change ‖w (test i)‖ ≤ ‖w (test i)‖ / 2 at hc
  linarith

end MathlibAnnex.CompactAnnihilator
