import Mathlib.Analysis.CStarAlgebra.Unitization
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Arens
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.BidualCStarLaws

/-!
# Arens regularity of multiplication for non-unital C*-algebras

The product is the existing `MathlibAnnex.RepresentedBidual.arensProduct`
on the literal strong double dual. Its construction, boundedness,
associativity and compatibility with the canonical inclusion are imported.

The new point here is that the first and second scalar Arens extensions of
`(a,b) ↦ f (a * b)` agree without a unit or a separability assumption. We
extend `f` to the unitization using its continuous linear second-coordinate
projection, apply the established unital C*-laws, and restrict both variables
along the canonical inclusion. The extension need not preserve the norm:
only its continuity and its restriction to the original algebra are used.

No new carrier, norm or multiplication instance is introduced.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Topology
open MathlibAnnex.BidualBilinear MathlibAnnex.RepresentedBidual
open MathlibAnnex.WeakCompact

namespace MathlibAnnex.Analysis.CStarAlgebra.Bidual

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {B : Type v} [NonUnitalCStarAlgebra B]

/-- A bounded multiplicative map induces a multiplicative map between the
literal biduals, for the existing first-Arens product. -/
theorem bidualMap_arensProduct (T : A →L[ℂ] B)
    (hT : ∀ a b : A, T (a * b) = T a * T b)
    (F G : StrongDual ℂ (StrongDual ℂ A)) :
    bidualMap T (arensProduct F G) =
      arensProduct (bidualMap T F) (bidualMap T G) := by
  ext f
  change arensProduct F G (f.comp T) =
    arensProduct (bidualMap T F) (bidualMap T G) f
  have hform : multiplicationForm (f.comp T) =
      precompRight ((multiplicationForm f).comp T) T := by
    ext a b
    change f (T (a * b)) = f (T a * T b)
    rw [hT a b]
  rw [arensProduct_eq_firstArens, arensProduct_eq_firstArens, hform,
    firstArens_precomp_apply]

private theorem firstArens_multiplicationForm_eq_secondArens_of_unital
    {U : Type v} [CStarAlgebra U] (f : StrongDual ℂ U) :
    firstArens (multiplicationForm f) = secondArens (multiplicationForm f) := by
  apply (isWeaklyCompact_iff_firstArens_eq_secondArens (multiplicationForm f)).mp
  apply (isWeaklyCompact_iff_exists_extension (multiplicationForm f)).mpr
  refine ⟨firstArens (multiplicationForm f),
    ⟨continuousFirst_firstArens (multiplicationForm f), ?_⟩,
    firstArens_canonical (multiplicationForm f), norm_firstArens (multiplicationForm f)⟩
  intro F
  exact (WeakDual.eval_continuous f).comp
    (MathlibAnnex.RepresentedBidual.continuous_arensProduct_right F)

/-- Multiplication in a possibly non-unital C*-algebra is Arens regular,
expressed through the existing scalar-valued Arens constructions. -/
theorem firstArens_multiplicationForm_eq_secondArens (f : StrongDual ℂ A) :
    firstArens (multiplicationForm f) = secondArens (multiplicationForm f) := by
  let i : A →L[ℂ] Unitization ℂ A :=
    { toLinearMap := Unitization.inrHom ℂ ℂ A
      cont := Unitization.continuous_inr }
  let p : Unitization ℂ A →L[ℂ] A :=
    { toLinearMap := Unitization.sndHom ℂ ℂ A
      cont := Unitization.continuous_snd }
  let g : StrongDual ℂ (Unitization ℂ A) := f.comp p
  have hg : firstArens (multiplicationForm g) = secondArens (multiplicationForm g) :=
    firstArens_multiplicationForm_eq_secondArens_of_unital g
  have hform : precompRight ((multiplicationForm g).comp i) i =
      multiplicationForm f := by
    ext a b
    change f (((a : Unitization ℂ A) * (b : Unitization ℂ A)).snd) = f (a * b)
    simp only [Unitization.snd_mul, Unitization.fst_inr, Unitization.snd_inr,
      zero_smul, zero_add]
  apply BidualForm.ext
  intro F G
  rw [← hform, firstArens_precomp_apply, secondArens_precomp_apply, hg]

/-- The multiplication form has a weakly compact associated operator. This
is the scalar Gantmacher criterion, applied after proving Arens regularity. -/
theorem isWeaklyCompact_multiplicationForm (f : StrongDual ℂ A) :
    IsWeaklyCompact (multiplicationForm f) :=
  (isWeaklyCompact_iff_firstArens_eq_secondArens (multiplicationForm f)).mpr
    (firstArens_multiplicationForm_eq_secondArens f)

/-- Evaluation of the actual bidual product also agrees with the second
Arens extension. The original product and its original norm are retained. -/
theorem arensProduct_eq_secondArens (F G : StrongDual ℂ (StrongDual ℂ A))
    (f : StrongDual ℂ A) :
    arensProduct F G f = BidualForm.eval (secondArens (multiplicationForm f)) F G := by
  rw [arensProduct_eq_firstArens, firstArens_multiplicationForm_eq_secondArens]

/-- Separate weak-star continuity in the second variable for the literal
bidual of a possibly non-unital C*-algebra. -/
theorem continuous_arensProduct_right (F : StrongDual ℂ (StrongDual ℂ A)) :
    Continuous (fun G : WeakDual ℂ (StrongDual ℂ A) =>
      StrongDual.toWeakDual (arensProduct F (WeakDual.toStrongDual G))) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  change Continuous (fun G : WeakDual ℂ (StrongDual ℂ A) =>
    arensProduct F (WeakDual.toStrongDual G) f)
  simpa only [arensProduct_eq_secondArens] using
    continuousSecond_secondArens (multiplicationForm f) F

/-- Both scalar Arens extensions are separately weak-star continuous. -/
theorem separatelyWeakStarContinuous_multiplicationForm (f : StrongDual ℂ A) :
    SeparatelyWeakStarContinuous (firstArens (multiplicationForm f)) ∧
      SeparatelyWeakStarContinuous (secondArens (multiplicationForm f)) := by
  have h : SeparatelyWeakStarContinuous (firstArens (multiplicationForm f)) :=
    separatelyWeakStarContinuous_firstArens (multiplicationForm f)
      (isWeaklyCompact_multiplicationForm f)
  exact ⟨h, by simpa only [← firstArens_multiplicationForm_eq_secondArens f] using h⟩

end MathlibAnnex.Analysis.CStarAlgebra.Bidual
