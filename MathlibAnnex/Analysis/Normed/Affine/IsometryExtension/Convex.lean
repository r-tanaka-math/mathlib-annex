import MathlibAnnex.Analysis.Normed.Affine.IsometryExtension.OpenConnected
import Mathlib.Analysis.Convex.Topology

/-!
# Convex-set extension corollary

The theorem in this module applies the open-connected extension theorem to
ambient interiors, then extends the agreement to the whole convex sets by
continuity and density.
-/

open Metric Set

namespace MathlibAnnex

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace IsometryEquiv

private def interiorRestriction
    {s : Set E} {t : Set F} (f : s ≃ᵢ t)
    (hfi : ∀ x : s, (x : E) ∈ interior s ↔ ((f x : t) : F) ∈ interior t) :
    interior s ≃ᵢ interior t where
  toFun x :=
    ⟨((f ⟨x, interior_subset x.property⟩ : t) : F),
      (hfi ⟨x, interior_subset x.property⟩).mp x.property⟩
  invFun y := by
    let yt : t := ⟨y, interior_subset y.property⟩
    let xs : s := f.symm yt
    refine ⟨(xs : E), ?_⟩
    apply (hfi xs).mpr
    rw [show f xs = yt from f.apply_symm_apply yt]
    exact y.property
  left_inv x := by
    apply Subtype.ext
    change ((f.symm (f ⟨x, interior_subset x.property⟩) : s) : E) = (x : E)
    exact congrArg Subtype.val (f.symm_apply_apply ⟨x, interior_subset x.property⟩)
  right_inv y := by
    apply Subtype.ext
    change ((f (f.symm ⟨y, interior_subset y.property⟩) : t) : F) = (y : F)
    exact congrArg Subtype.val (f.apply_symm_apply ⟨y, interior_subset y.property⟩)
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    change dist (f ⟨x, interior_subset x.property⟩)
      (f ⟨y, interior_subset y.property⟩) = dist x y
    rw [f.dist_eq, Subtype.dist_eq, Subtype.dist_eq]

/-- An isometry equivalence from a convex set with nonempty ambient interior
extends uniquely if it preserves membership in the ambient interiors.
The target set is not separately assumed convex. -/
theorem existsUnique_affineExtension_of_convex
    {s : Set E} {t : Set F} (f : s ≃ᵢ t)
    (hs : Convex ℝ s) (hsint : (interior s).Nonempty)
    (hfi : ∀ x : s,
      (x : E) ∈ interior s ↔ ((f x : t) : F) ∈ interior t) :
    ∃! A : E ≃ᵃⁱ[ℝ] F,
      ∀ x : s, A (x : E) = ((f x : t) : F) := by
  let fi : interior s ≃ᵢ interior t := interiorRestriction f hfi
  rcases MathlibAnnex.IsometryEquiv.existsUnique_affineExtension
      fi isOpen_interior ((hs.interior).isConnected hsint) isOpen_interior with
    ⟨A, hAi, hAuniq⟩
  let u : Set s := {x | (x : E) ∈ interior s}
  have hu_image : Subtype.val '' u = interior s := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, interior_subset hz⟩, hz, rfl⟩
  have hu_dense : Dense u := by
    rw [Subtype.dense_iff, hu_image,
      hs.closure_interior_eq_closure_of_nonempty_interior hsint]
    exact subset_closure
  have hAall : ∀ x : s, A (x : E) = ((f x : t) : F) := by
    have hcontA : Continuous (fun x : s ↦ A (x : E)) :=
      A.continuous.comp continuous_subtype_val
    have hcontf : Continuous (fun x : s ↦ ((f x : t) : F)) :=
      continuous_subtype_val.comp f.continuous
    have heq : u.EqOn (fun x : s ↦ A (x : E))
        (fun x : s ↦ ((f x : t) : F)) := by
      intro x hx
      let xi : interior s := ⟨(x : E), hx⟩
      have h := hAi xi
      exact h
    exact fun x ↦ congrFun (Continuous.ext_on hu_dense hcontA hcontf heq) x
  refine ⟨A, hAall, ?_⟩
  intro B hB
  apply hAuniq
  intro x
  let xs : s := ⟨(x : E), interior_subset x.property⟩
  have h := hB xs
  exact h

end IsometryEquiv

end

end MathlibAnnex
