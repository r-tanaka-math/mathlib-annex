import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedBidualProduct

/-!
# The bidual involution and the adjoint of the actual represented extension

The involution is written as an explicit map on the project's Banach
bidual.  Its evaluation formula, isometry and involutivity are proved.
Together with `extension_arensProduct`, the representation respects both
operations.  No global `CStarAlgebra A**` instance, central support projection,
or normal section is asserted or installed by this file.

Controller checkpoint C01.  Source not yet compiled.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProduct

namespace MathlibAnnex.RepresentedBidual

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The involution of a source functional, complex-linear in the source
argument and conjugate-linear in the functional. -/
def dualStar (f : StrongDual ℂ A) : StrongDual ℂ A :=
  LinearMap.mkContinuous
    { toFun := fun a => star (f (star a))
      map_add' := by intro a b; simp only [star_add, map_add]
      map_smul' := by
        intro c a
        simp only [star_smul, map_smul, star_star]
        rfl }
    ‖f‖ (by
      intro a
      change ‖star (f (star a))‖ ≤ ‖f‖ * ‖a‖
      rw [norm_star]
      simpa only [norm_star] using f.le_opNorm (star a))

@[simp]
theorem dualStar_apply (f : StrongDual ℂ A) (a : A) :
    dualStar f a = star (f (star a)) := rfl

@[simp]
theorem dualStar_add (f g : StrongDual ℂ A) : dualStar (f + g) = dualStar f + dualStar g := by
  ext a
  simp only [dualStar_apply, ContinuousLinearMap.add_apply, star_add]

@[simp]
theorem dualStar_smul (c : ℂ) (f : StrongDual ℂ A) :
    dualStar (c • f) = star c • dualStar f := by
  ext a
  simp only [dualStar_apply, ContinuousLinearMap.smul_apply, star_smul]

@[simp]
theorem dualStar_dualStar (f : StrongDual ℂ A) : dualStar (dualStar f) = f := by
  ext a
  simp only [dualStar_apply, star_star]

theorem norm_dualStar_le (f : StrongDual ℂ A) : ‖dualStar f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro a
  simp only [dualStar_apply, norm_star]
  simpa only [norm_star] using f.le_opNorm (star a)

@[simp]
theorem norm_dualStar (f : StrongDual ℂ A) : ‖dualStar f‖ = ‖f‖ := by
  apply le_antisymm (norm_dualStar_le f)
  simpa only [dualStar_dualStar] using norm_dualStar_le (dualStar f)

/-- Explicit involution on the strong Banach bidual. -/
def bidualStar (F : StrongDual ℂ (StrongDual ℂ A)) : StrongDual ℂ (StrongDual ℂ A) :=
  LinearMap.mkContinuous
    { toFun := fun f => star (F (dualStar f))
      map_add' := by intro f g; simp only [dualStar_add, map_add, star_add]
      map_smul' := by
        intro c f
        simp only [dualStar_smul, map_smul, star_smul, star_star]
        rfl }
    ‖F‖ (by
      intro f
      change ‖star (F (dualStar f))‖ ≤ ‖F‖ * ‖f‖
      rw [norm_star]
      simpa only [norm_dualStar] using F.le_opNorm (dualStar f))

@[simp]
theorem bidualStar_apply (F : StrongDual ℂ (StrongDual ℂ A)) (f : StrongDual ℂ A) :
    bidualStar F f = star (F (dualStar f)) := rfl

@[simp]
theorem bidualStar_add (F G : StrongDual ℂ (StrongDual ℂ A)) :
    bidualStar (F + G) = bidualStar F + bidualStar G := by
  ext f
  simp only [bidualStar_apply, ContinuousLinearMap.add_apply, star_add]

@[simp]
theorem bidualStar_smul (c : ℂ) (F : StrongDual ℂ (StrongDual ℂ A)) :
    bidualStar (c • F) = star c • bidualStar F := by
  ext f
  simp only [bidualStar_apply, ContinuousLinearMap.smul_apply, star_smul]

@[simp]
theorem bidualStar_bidualStar (F : StrongDual ℂ (StrongDual ℂ A)) :
    bidualStar (bidualStar F) = F := by
  ext f
  simp only [bidualStar_apply, dualStar_dualStar, star_star]

theorem norm_bidualStar_le (F : StrongDual ℂ (StrongDual ℂ A)) :
    ‖bidualStar F‖ ≤ ‖F‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
  intro f
  simp only [bidualStar_apply, norm_star]
  simpa only [norm_dualStar] using F.le_opNorm (dualStar f)

@[simp]
theorem norm_bidualStar (F : StrongDual ℂ (StrongDual ℂ A)) :
    ‖bidualStar F‖ = ‖F‖ := by
  apply le_antisymm (norm_bidualStar_le F)
  simpa only [bidualStar_bidualStar] using norm_bidualStar_le (bidualStar F)

@[simp]
theorem bidualStar_canonical (a : A) :
    bidualStar (NormedSpace.inclusionInDoubleDual ℂ A a) =
      NormedSpace.inclusionInDoubleDual ℂ A (star a) := by
  ext f
  change star (dualStar f a) = f (star a)
  simp only [dualStar_apply, star_star]

/-- Swapping the two vectors gives the involuted matrix coefficient. -/
theorem dualStar_coefficient_inner (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (xi eta : H) :
    dualStar (coefficient rho xi (innerSL ℂ eta)) =
      coefficient rho eta (innerSL ℂ xi) := by
  ext a
  change star (inner ℂ eta (rho (star a) xi)) = inner ℂ xi (rho a eta)
  rw [map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact inner_conj_symm _ _

/-- The representation respects the explicit bidual involution. -/
theorem extension_bidualStar (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    extension rho (bidualStar F) = star (extension rho F) := by
  apply ContinuousLinearMap.ext
  intro xi
  apply ext_inner_left ℂ
  intro eta
  calc
    inner ℂ eta (extension rho (bidualStar F) xi) =
        bidualStar F (coefficient rho xi (innerSL ℂ eta)) :=
      coefficient_extension rho (bidualStar F) xi (innerSL ℂ eta)
    _ = star (F (coefficient rho eta (innerSL ℂ xi))) := by
      rw [bidualStar_apply, dualStar_coefficient_inner]
    _ = star (inner ℂ xi (extension rho F eta)) := by
      rw [← coefficient_extension]
      rfl
    _ = inner ℂ (extension rho F eta) xi := inner_conj_symm _ _
    _ = inner ℂ eta (star (extension rho F) xi) := by
      rw [ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]

/-- The kernel is invariant under the involution as well as both product
actions.  This still does not manufacture a central support projection. -/
theorem extension_kernel_star (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (F : StrongDual ℂ (StrongDual ℂ A)) (hF : extension rho F = 0) :
    extension rho (bidualStar F) = 0 := by
  rw [extension_bidualStar, hF, star_zero]

/-- The two star-square orientations have their correct represented images. -/
theorem extension_starSquares (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    extension rho (arensProduct (bidualStar F) F) =
      star (extension rho F) * extension rho F ∧
    extension rho (arensProduct F (bidualStar F)) =
      extension rho F * star (extension rho F) := by
  simp only [extension_arensProduct, extension_bidualStar, and_self]

end MathlibAnnex.RepresentedBidual
