import MathlibAnnex.Analysis.Normed.Affine.IsometryExtension.Convex
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Ball extension corollaries

The closed-ball theorem first transports the center using the bounded
point-reflection theorem, then applies the convex ambient-interior corollary.
-/

open Metric Set AffineIsometryEquiv Bornology

namespace MathlibAnnex

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace IsometryEquiv

/-- A surjective isometry between positive-radius open balls extends to a
unique ambient real affine isometry equivalence. -/
theorem existsUnique_affineExtension_ball
    {c : E} {d : F} {r R : ℝ} (f : ball c r ≃ᵢ ball d R)
    (hr : 0 < r) (hR : 0 < R) :
    ∃! A : E ≃ᵃⁱ[ℝ] F,
      ∀ x : ball c r, A (x : E) = ((f x : ball d R) : F) := by
  have _htc : IsConnected (ball d R) := isConnected_ball hR
  exact MathlibAnnex.IsometryEquiv.existsUnique_affineExtension
    f isOpen_ball (isConnected_ball hr) isOpen_ball

private theorem mapsTo_pointReflection_closedBall (c : E) (r : ℝ) :
    MapsTo (pointReflection ℝ c) (closedBall c r) (closedBall c r) := by
  intro x hx
  rw [mem_closedBall, dist_pointReflection_fixed]
  exact hx

/-- A surjective isometry between closed balls of the same positive radius
extends to a unique ambient real affine isometry equivalence. -/
theorem existsUnique_affineExtension_closedBall
    {c : E} {d : F} {r : ℝ} (f : closedBall c r ≃ᵢ closedBall d r)
    (hr : 0 < r) :
    ∃! A : E ≃ᵃⁱ[ℝ] F,
      ∀ x : closedBall c r,
        A (x : E) = ((f x : closedBall d r) : F) := by
  let cc : closedBall c r := ⟨c, mem_closedBall_self hr.le⟩
  let dd : closedBall d r := ⟨d, mem_closedBall_self hr.le⟩
  have hcenter : f cc = dd :=
    MathlibAnnex.IsometryEquiv.map_center_of_mapsTo_pointReflection
      f cc.property dd.property isBounded_closedBall
      (mapsTo_pointReflection_closedBall c r)
      (mapsTo_pointReflection_closedBall d r)
  have hcenter_val : ((f cc : closedBall d r) : F) = d :=
    congrArg Subtype.val hcenter
  have hfi : ∀ x : closedBall c r,
      (x : E) ∈ interior (closedBall c r) ↔
        ((f x : closedBall d r) : F) ∈ interior (closedBall d r) := by
    intro x
    rw [interior_closedBall c hr.ne', interior_closedBall d hr.ne',
      mem_ball, mem_ball]
    have hdist : dist ((f x : closedBall d r) : F) d = dist (x : E) c := by
      calc
        dist ((f x : closedBall d r) : F) d =
            dist ((f x : closedBall d r) : F)
              ((f cc : closedBall d r) : F) := by rw [hcenter_val]
        _ = dist (f x) (f cc) := rfl
        _ = dist x cc := f.dist_eq x cc
        _ = dist (x : E) c := rfl
    rw [hdist]
  have hsint : (interior (closedBall c r)).Nonempty := by
    rw [interior_closedBall c hr.ne']
    exact nonempty_ball.mpr hr
  exact
    MathlibAnnex.IsometryEquiv.existsUnique_affineExtension_of_convex
      f (convex_closedBall c r) hsint hfi

end IsometryEquiv

end

end MathlibAnnex
