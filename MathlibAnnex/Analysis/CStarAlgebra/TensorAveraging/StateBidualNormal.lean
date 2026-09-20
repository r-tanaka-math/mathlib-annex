import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedBidualStar
import MathlibAnnex.Analysis.CStarAlgebra.State.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Positive normal state extensions on the explicit Banach bidual

Evaluation at a state is weak-star continuous.  Its positivity for the
actual first-Arens star squares is proved using that state's genuine GNS
representation and the represented bidual map constructed in C01.
No general bilinear Arens regularity theorem or new global C*-bidual
instance is assumed.

The strong-star gauge conclusion uses the specified GNS operators.  It
must not be silently transferred to a different irreducible representation:
that step needs the still-missing central support/corner argument.
Controller source C01, uncompiled.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped InnerProduct ComplexOrder

namespace MathlibAnnex.RepresentedBidual
open MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private noncomputable instance : Norm (StrongDual ℂ (StrongDual ℂ A) →L[ℂ] ℂ) :=
  ContinuousLinearMap.hasOpNorm (E := StrongDual ℂ (StrongDual ℂ A)) (F := ℂ)
    (σ₁₂ := RingHom.id ℂ)

/-- The canonical extension is the actual bidual evaluation map. -/
def stateExtension (phi : A →L[ℂ] ℂ) : StrongDual ℂ (StrongDual ℂ A) →L[ℂ] ℂ :=
  NormedSpace.inclusionInDoubleDual ℂ (StrongDual ℂ A) phi

@[simp] theorem stateExtension_apply (phi : A →L[ℂ] ℂ)
    (F : StrongDual ℂ (StrongDual ℂ A)) : stateExtension phi F = F phi := rfl

@[simp] theorem stateExtension_canonical (phi : A →L[ℂ] ℂ) (a : A) :
    stateExtension phi (NormedSpace.inclusionInDoubleDual ℂ A a) = phi a := rfl

theorem stateExtension_weakStarContinuous (phi : A →L[ℂ] ℂ) :
    Continuous (fun F : WeakDual ℂ (StrongDual ℂ A) => stateExtension phi (WeakDual.toStrongDual F)) :=
  WeakDual.eval_continuous phi

@[simp] theorem norm_stateExtension (phi : A →L[ℂ] ℂ) : ‖stateExtension phi‖ = ‖phi‖ :=
  (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℂ) (E := StrongDual ℂ A)).norm_map phi

/-- The state is the coefficient of its own GNS representation, with the
same cyclic vector in both positions. -/
theorem state_gns_coefficient (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) :
    coefficient (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.toNonUnitalStarAlgHom
      (stateGNSVector phi hphi) (innerSL ℂ (stateGNSVector phi hphi)) = phi := by
  ext a
  exact inner_gnsStarAlgHom_stateGNSVector phi hphi a

/-- A useful concrete notation for the GNS image, not a hypothetical normal
extension supplied as an argument. -/
def stateOperator (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    (positiveLinearMapOfMemStateSpace phi hphi).GNS →L[ℂ]
      (positiveLinearMapOfMemStateSpace phi hphi).GNS :=
  extension (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.toNonUnitalStarAlgHom F

theorem stateExtension_eq_inner (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    stateExtension phi F = inner ℂ (stateGNSVector phi hphi)
      (stateOperator phi hphi F (stateGNSVector phi hphi)) := by
  change F phi = _
  calc
    F phi = F (coefficient
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.toNonUnitalStarAlgHom
        (stateGNSVector phi hphi) (innerSL ℂ (stateGNSVector phi hphi))) :=
      congrArg F (state_gns_coefficient phi hphi).symm
    _ = _ := by
      simpa only [stateOperator, innerSL_apply_apply] using (coefficient_extension
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.toNonUnitalStarAlgHom
        F (stateGNSVector phi hphi) (innerSL ℂ (stateGNSVector phi hphi))).symm

/-- Both arguments use one and the same GNS representation. -/
theorem stateExtension_star_product (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (F G : StrongDual ℂ (StrongDual ℂ A)) :
    stateExtension phi (arensProduct (bidualStar F) G) =
      inner ℂ (stateOperator phi hphi F (stateGNSVector phi hphi))
        (stateOperator phi hphi G (stateGNSVector phi hphi)) := by
  rw [stateExtension_eq_inner phi hphi]
  simp only [stateOperator, extension_arensProduct, extension_bidualStar,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

/-- Positivity for first-Arens star squares is proved, not included as an
extra hypothesis on the functional. -/
theorem stateExtension_star_square (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    stateExtension phi (arensProduct (bidualStar F) F) =
      (‖stateOperator phi hphi F (stateGNSVector phi hphi)‖ ^ 2 : ℂ) := by
  rw [stateExtension_star_product phi hphi F F, inner_self_eq_norm_sq_to_K]
  rfl

theorem stateExtension_star_square_nonneg (phi : A →L[ℂ] ℂ)
    (hphi : phi ∈ stateSpace A) (F : StrongDual ℂ (StrongDual ℂ A)) :
    0 ≤ stateExtension phi (arensProduct (bidualStar F) F) := by
  rw [stateExtension_star_square phi hphi F]
  exact_mod_cast sq_nonneg ‖stateOperator phi hphi F (stateGNSVector phi hphi)‖

/-- The reverse square has the adjoint-vector gauge, not the same forward
gauge reused without proof. -/
theorem stateExtension_reverse_square (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    stateExtension phi (arensProduct F (bidualStar F)) =
      (‖star (stateOperator phi hphi F) (stateGNSVector phi hphi)‖ ^ 2 : ℂ) := by
  have h := stateExtension_star_square phi hphi (bidualStar F)
  simpa only [bidualStar_bidualStar, stateOperator, extension_bidualStar] using h

/-- The canonical normal state's Cauchy--Schwarz bound. -/
theorem norm_stateExtension_star_product_le (phi : A →L[ℂ] ℂ)
    (hphi : phi ∈ stateSpace A) (F G : StrongDual ℂ (StrongDual ℂ A)) :
    ‖stateExtension phi (arensProduct (bidualStar F) G)‖ ≤
      ‖stateOperator phi hphi F (stateGNSVector phi hphi)‖ *
      ‖stateOperator phi hphi G (stateGNSVector phi hphi)‖ := by
  rw [stateExtension_star_product]
  exact norm_inner_le_norm _ _

/-- Exact gauge continuity along any net whose specified GNS-vector images
converge.  This is not an identification with another concrete topology. -/
theorem tendsto_stateExtension_star_square {ι : Type*} (l : Filter ι)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (F : ι → StrongDual ℂ (StrongDual ℂ A))
    (hF : Tendsto (fun i => stateOperator phi hphi (F i) (stateGNSVector phi hphi))
      l (𝓝 0)) :
    Tendsto (fun i => stateExtension phi (arensProduct (bidualStar (F i)) (F i))) l (𝓝 0) := by
  have hnorm : Tendsto (fun i => ‖stateOperator phi hphi (F i) (stateGNSVector phi hphi)‖)
      l (𝓝 0) := by simpa only [norm_zero] using hF.norm
  have hsq := hnorm.pow 2
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, stateExtension_star_square phi hphi,
    zero_pow (by decide : (2 : ℕ) ≠ 0), Complex.ofReal_zero,
    Complex.ofReal_pow] using hcomplex

end MathlibAnnex.RepresentedBidual
