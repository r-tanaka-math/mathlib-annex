import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Linarith

/-!
# Centers of bounded reflection-invariant sets

Mathlib is the canonical provider of the Mazur--Ulam theorem. This module adds
one general center-transport result for bounded point-reflection-invariant
subsets. It does not provide another Mazur--Ulam endpoint.
-/

open Metric Set AffineIsometryEquiv Bornology

namespace MathlibAnnex.IsometryEquiv

noncomputable section

variable {V P W Q : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [MetricSpace Q] [NormedAddTorsor W Q]

private def restrictedPointReflection (s : Set P) (c : P)
    (h : MapsTo (pointReflection ℝ c) s s) : s ≃ᵢ s where
  toFun x := ⟨pointReflection ℝ c x, h x.property⟩
  invFun x := ⟨pointReflection ℝ c x, h x.property⟩
  left_inv x := by
    apply Subtype.ext
    exact pointReflection_involutive c (x : P)
  right_inv x := by
    apply Subtype.ext
    exact pointReflection_involutive c (x : P)
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    change dist (pointReflection ℝ c (x : P)) (pointReflection ℝ c (y : P)) =
      dist (x : P) (y : P)
    exact (pointReflection ℝ c).isometry.dist_eq _ _

private theorem apply_center_eq_of_isBounded_of_mapsTo_pointReflection
    {s : Set P} {c : P} (hc : c ∈ s) (hs : IsBounded s)
    (hreflect : MapsTo (pointReflection ℝ c) s s) (e : s ≃ᵢ s) :
    e ⟨c, hc⟩ = ⟨c, hc⟩ := by
  let c₀ : s := ⟨c, hc⟩
  let R : s ≃ᵢ s := restrictedPointReflection s c hreflect
  have h_bdd : BddAbove (range fun e : s ≃ᵢ s => dist (e c₀) c₀) := by
    rcases (Metric.isBounded_iff.mp hs) with ⟨C, hC⟩
    refine ⟨C, forall_mem_range.2 ?_⟩
    intro g
    exact hC (g c₀).property c₀.property
  let T : (s ≃ᵢ s) → (s ≃ᵢ s) := fun g => ((g.trans R).trans g.symm).trans R
  have hT_dist : ∀ g : s ≃ᵢ s, dist (T g c₀) c₀ = 2 * dist (g c₀) c₀ := by
    intro g
    change dist (R (g.symm (R (g c₀)))) c₀ = 2 * dist (g c₀) c₀
    calc
      dist (R (g.symm (R (g c₀)))) c₀ = dist (g.symm (R (g c₀))) c₀ := by
        rw [Subtype.dist_eq, Subtype.dist_eq]
        exact dist_pointReflection_fixed c (g.symm (R (g c₀)) : P)
      _ = dist (g (g.symm (R (g c₀)))) (g c₀) :=
        (g.dist_eq (g.symm (R (g c₀))) c₀).symm
      _ = dist (R (g c₀)) (g c₀) := by rw [g.apply_symm_apply]
      _ = 2 * dist (g c₀) c₀ := by
        dsimp [R, restrictedPointReflection]
        rw [Subtype.dist_eq, Subtype.dist_eq]
        simpa [dist_comm] using dist_pointReflection_self_real c (g c₀ : P)
  let C := ⨆ g : s ≃ᵢ s, dist (g c₀) c₀
  have hhalve : C ≤ C / 2 := by
    apply ciSup_le
    intro g
    rw [le_div_iff₀' (zero_lt_two' ℝ), ← hT_dist]
    exact le_ciSup h_bdd (T g)
  have hC_nonpos : C ≤ 0 := by linarith
  apply dist_le_zero.mp
  exact (le_ciSup h_bdd e).trans hC_nonpos

/-- An isometry equivalence between point-reflection-invariant subsets sends
the center of a bounded source subset to the center of the target subset. -/
theorem map_center_of_mapsTo_pointReflection
    {s : Set P} {t : Set Q} {c : P} {d : Q} (f : s ≃ᵢ t)
    (hc : c ∈ s) (hd : d ∈ t) (hs : IsBounded s)
    (hsreflect : MapsTo (pointReflection ℝ c) s s)
    (htreflect : MapsTo (pointReflection ℝ d) t t) :
    f ⟨c, hc⟩ = ⟨d, hd⟩ := by
  let R : t ≃ᵢ t := restrictedPointReflection t d htreflect
  let g : s ≃ᵢ s := (f.trans R).trans f.symm
  have hg := apply_center_eq_of_isBounded_of_mapsTo_pointReflection hc hs hsreflect g
  have hRf : R (f ⟨c, hc⟩) = f ⟨c, hc⟩ := by
    simpa [g] using congrArg f hg
  apply Subtype.ext
  have hfixed : pointReflection ℝ d ((f ⟨c, hc⟩ : t) : Q) =
      ((f ⟨c, hc⟩ : t) : Q) := by
    exact congrArg Subtype.val hRf
  exact pointReflection_fixed_iff.mp hfixed

end

end MathlibAnnex.IsometryEquiv
