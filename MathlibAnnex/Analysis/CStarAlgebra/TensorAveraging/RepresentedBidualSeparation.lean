import MathlibAnnex.Analysis.CStarAlgebra.Representation.FunctionalCoefficient
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedBidualStar

/-!
# The actual represented family separates and norms the Banach bidual

The family is indexed by nonzero source functionals, not by a proper class of
Hilbert spaces.  Its GNS spaces were constructed in FunctionalCoefficient. Every
member is contractive. Exact coefficient recovery proves the converse norm
bound. This is not a faithfulness assumption or an equivalence of arbitrary
renormings. The original Banach-bidual norm is retained exactly. C03, unbuilt.
-/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace

namespace MathlibAnnex.RepresentedBidual
namespace FunctionalFamily

universe u
variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

abbrev NonzeroFunctional (A : Type u) [CStarAlgebra A] := {f : StrongDual ℂ A // f ≠ 0}
abbrev GNSHilbertSpace (f : NonzeroFunctional A) := FunctionalCoefficient.GNSHilbertSpace f.val f.property

def rep (f : NonzeroFunctional A) : A →⋆ₐ[ℂ] (GNSHilbertSpace f →L[ℂ] GNSHilbertSpace f) :=
  FunctionalCoefficient.representation f.val f.property

def image (f : NonzeroFunctional A) :
    StrongDual ℂ (StrongDual ℂ A) →L[ℂ] (GNSHilbertSpace f →L[ℂ] GNSHilbertSpace f) :=
  extension (rep f).toNonUnitalStarAlgHom

/-- This is an equality of actual continuous source functionals. -/
theorem source_coefficient (f : NonzeroFunctional A) :
    f.val = (‖f.val‖ : ℂ) • coefficient (rep f).toNonUnitalStarAlgHom
      (FunctionalCoefficient.rightVector f.val f.property)
      (innerSL ℂ (FunctionalCoefficient.leftVector f.val f.property)) := by
  ext a
  exact FunctionalCoefficient.recover f.val f.property a

/-- Evaluate arbitrary F at an arbitrary nonzero functional using its one
constructed Hilbert representation. -/
theorem evaluation (F : StrongDual ℂ (StrongDual ℂ A)) (f : NonzeroFunctional A) :
    F f.val = (‖f.val‖ : ℂ) *
      inner ℂ (FunctionalCoefficient.leftVector f.val f.property)
        (image f F (FunctionalCoefficient.rightVector f.val f.property)) := by
  calc
    F f.val = F ((‖f.val‖ : ℂ) • coefficient (rep f).toNonUnitalStarAlgHom
      (FunctionalCoefficient.rightVector f.val f.property)
      (innerSL ℂ (FunctionalCoefficient.leftVector f.val f.property))) :=
        congrArg F (source_coefficient f)
    _ = _ := by rw [map_smul, smul_eq_mul, ← coefficient_extension]; rfl

theorem evaluation_norm_le (F : StrongDual ℂ (StrongDual ℂ A)) (f : NonzeroFunctional A) :
    ‖F f.val‖ ≤ ‖f.val‖ * ‖image f F‖ := by
  rw [evaluation, norm_mul]
  have hscalar : ‖(‖f.val‖ : ℂ)‖ = ‖f.val‖ := by simp
  rw [hscalar]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖inner ℂ (FunctionalCoefficient.leftVector f.val f.property)
      (image f F (FunctionalCoefficient.rightVector f.val f.property))‖ ≤
      ‖FunctionalCoefficient.leftVector f.val f.property‖ *
        ‖image f F (FunctionalCoefficient.rightVector f.val f.property)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖FunctionalCoefficient.leftVector f.val f.property‖ *
        (‖image f F‖ * ‖FunctionalCoefficient.rightVector f.val f.property‖) :=
      mul_le_mul_of_nonneg_left ((image f F).le_opNorm _) (norm_nonneg _)
    _ ≤ 1 * (‖image f F‖ * 1) := by
      gcongr
      · exact FunctionalCoefficient.norm_leftVector_le _ _
      · exact FunctionalCoefficient.norm_rightVector_le _ _
    _ = ‖image f F‖ := by ring

/-- Norm recovery uses every source functional and includes f=0 explicitly. -/
theorem norm_le_of_images_le (F : StrongDual ℂ (StrongDual ℂ A))
    {r : ℝ} (hr : 0 ≤ r) (h : ∀ f : NonzeroFunctional A, ‖image f F‖ ≤ r) : ‖F‖ ≤ r := by
  apply ContinuousLinearMap.opNorm_le_bound _ hr
  intro f
  by_cases hf : f = 0
  · simp [hf]
  · let k : NonzeroFunctional A := ⟨f, hf⟩
    calc
      ‖F f‖ ≤ ‖f‖ * ‖image k F‖ := evaluation_norm_le F k
      _ ≤ ‖f‖ * r := mul_le_mul_of_nonneg_left (h k) (norm_nonneg f)
      _ = r * ‖f‖ := mul_comm _ _

theorem norm_le_iff (F : StrongDual ℂ (StrongDual ℂ A)) {r : ℝ} (hr : 0 ≤ r) :
    ‖F‖ ≤ r ↔ ∀ f : NonzeroFunctional A, ‖image f F‖ ≤ r := by
  constructor
  · intro h f
    exact (norm_extension_apply_le (rep f).toNonUnitalStarAlgHom F).trans h
  · exact norm_le_of_images_le F hr

/-- No norm, weak-star, or C*-structure beyond the raw bidual is assumed. -/
theorem ext (F G : StrongDual ℂ (StrongDual ℂ A))
    (h : ∀ f : NonzeroFunctional A, image f F = image f G) : F = G := by
  apply ContinuousLinearMap.ext
  intro f
  by_cases hf : f = 0
  · simp [hf]
  · let k : NonzeroFunctional A := ⟨f, hf⟩
    change F k.val = G k.val
    rw [evaluation F k, evaluation G k, h k]

@[simp] theorem image_product (f : NonzeroFunctional A) (F G : StrongDual ℂ (StrongDual ℂ A)) :
    image f (arensProduct F G) = image f F * image f G :=
  extension_arensProduct (rep f).toNonUnitalStarAlgHom F G

@[simp] theorem image_star (f : NonzeroFunctional A) (F : StrongDual ℂ (StrongDual ℂ A)) :
    image f (bidualStar F) = star (image f F) :=
  extension_bidualStar (rep f).toNonUnitalStarAlgHom F

@[simp] theorem image_canonical_one (f : NonzeroFunctional A) :
    image f (NormedSpace.inclusionInDoubleDual ℂ A 1) = 1 := by
  rw [image, extension_canonical]
  exact map_one (rep f)

/-- The exact lower C*-norm bound follows from operator squares and norm
recovery; it does not assume a C*-identity on the raw bidual. -/
theorem norm_square_le (F : StrongDual ℂ (StrongDual ℂ A)) :
    ‖F‖ * ‖F‖ ≤ ‖arensProduct (bidualStar F) F‖ := by
  let r := Real.sqrt ‖arensProduct (bidualStar F) F‖
  have hF : ‖F‖ ≤ r := by
    apply norm_le_of_images_le F (Real.sqrt_nonneg _)
    intro f
    have hs : ‖image f F‖ ^ 2 ≤ ‖arensProduct (bidualStar F) F‖ := by
      calc
        ‖image f F‖ ^ 2 = ‖star (image f F) * image f F‖ := by
          simpa [pow_two] using (CStarRing.norm_star_mul_self (x := image f F)).symm
        _ = ‖image f (arensProduct (bidualStar F) F)‖ := by rw [image_product, image_star]
        _ ≤ ‖arensProduct (bidualStar F) F‖ :=
          norm_extension_apply_le (rep f).toNonUnitalStarAlgHom _
    have hsq := Real.sq_sqrt (norm_nonneg (arensProduct (bidualStar F) F))
    have hr := Real.sqrt_nonneg ‖arensProduct (bidualStar F) F‖
    change ‖image f F‖ ≤ Real.sqrt ‖arensProduct (bidualStar F) F‖
    nlinarith [norm_nonneg (image f F)]
  have hsq := Real.sq_sqrt (norm_nonneg (arensProduct (bidualStar F) F))
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  dsimp [r] at hF hr
  nlinarith [norm_nonneg F]

end FunctionalFamily
end MathlibAnnex.RepresentedBidual
