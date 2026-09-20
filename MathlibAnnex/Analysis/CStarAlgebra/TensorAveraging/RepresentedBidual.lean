import MathlibAnnex.Analysis.InnerProductSpace.BidualRecovery
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.VectorForms
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

/-!
# The actual operator-valued extension of a representation to the Banach bidual

For a representation `rho : A -> B(H)`, apply Hilbert bidual recovery to
`a |-> rho(a) xi`, for each vector `xi`.  Currying makes these extensions a
single bounded-linear map `A** -> B(H)`.  Its coefficient formula determines
it without a choice of a von Neumann envelope or a section `B(H) -> A**`.

This file constructs the quotient-direction map.  It does not identify a
central corner or assert that arbitrary Hahn--Banach lifts form a linear
section.  In particular, the map here must not be substituted for `j` in
`BidualPullback`: the arrow there points in the opposite direction.

Controller source checkpoint C01.  Not compiled in this chat.
-/

set_option autoImplicit false
noncomputable section

open Topology
open scoped InnerProduct

namespace MathlibAnnex.RepresentedBidual

open MathlibAnnex.HilbertBidual

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The bounded linear map underlying a nonunital star representation. -/
def sourceMap (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : A →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := rho
      map_add' := map_add rho
      map_smul' := map_smul rho }
    1 (fun a => by
      change ‖rho a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le rho a)

@[simp]
theorem sourceMap_apply (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    sourceMap rho a = rho a := rfl

/-- The vector map is chosen canonically, with vector dependence linear. -/
def vectorMap (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (xi : H) : A →L[ℂ] H :=
  (sourceMap rho).flip xi

@[simp]
theorem vectorMap_apply (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (xi : H) (a : A) :
    vectorMap rho xi a = rho a xi := rfl

theorem norm_vectorMap_le (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (xi : H) :
    ‖vectorMap rho xi‖ ≤ ‖xi‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg xi)
  intro a
  change ‖rho a xi‖ ≤ ‖xi‖ * ‖a‖
  calc
    ‖rho a xi‖ ≤ ‖rho a‖ * ‖xi‖ := (rho a).le_opNorm xi
    _ ≤ ‖a‖ * ‖xi‖ := mul_le_mul_of_nonneg_right
      (NonUnitalStarAlgHom.norm_apply_le rho a) (norm_nonneg xi)
    _ = ‖xi‖ * ‖a‖ := mul_comm _ _

/-- Coefficient functionals on the source; arbitrary continuous linear
functionals on `H` are allowed, not only diagonal vector states. -/
def coefficient (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (xi : H) (g : StrongDual ℂ H) : StrongDual ℂ A :=
  g.comp (vectorMap rho xi)

@[simp]
theorem coefficient_apply (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (xi : H) (g : StrongDual ℂ H) (a : A) :
    coefficient rho xi g a = g (rho a xi) := rfl

/-- The representation's actual extension, with no unproved envelope or
extension map as an extra argument. -/
def extension (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    StrongDual ℂ (StrongDual ℂ A) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := fun F =>
        LinearMap.mkContinuous
          { toFun := fun xi => extend (vectorMap rho xi) F
            map_add' := by
              intro xi eta
              change extensionMap (vectorMap rho (xi + eta)) F =
                extensionMap (vectorMap rho xi) F + extensionMap (vectorMap rho eta) F
              simp only [vectorMap, map_add, ContinuousLinearMap.add_apply]
            map_smul' := by
              intro c xi
              change extensionMap (vectorMap rho (c • xi)) F =
                c • extensionMap (vectorMap rho xi) F
              simp only [vectorMap, map_smul, ContinuousLinearMap.smul_apply] }
          ‖F‖ (by
            intro xi
            change ‖extend (vectorMap rho xi) F‖ ≤ ‖F‖ * ‖xi‖
            calc
              ‖extend (vectorMap rho xi) F‖ ≤ ‖vectorMap rho xi‖ * ‖F‖ :=
                norm_extend_apply_le _ _
              _ ≤ ‖xi‖ * ‖F‖ := mul_le_mul_of_nonneg_right
                (norm_vectorMap_le rho xi) (norm_nonneg F)
              _ = ‖F‖ * ‖xi‖ := mul_comm _ _)
      map_add' := by
        intro F G
        apply ContinuousLinearMap.ext
        intro xi
        exact map_add (extend (vectorMap rho xi)) F G
      map_smul' := by
        intro c F
        apply ContinuousLinearMap.ext
        intro xi
        exact map_smul (extend (vectorMap rho xi)) c F }
    1 (by
      intro F
      simp only [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
      intro xi
      change ‖extend (vectorMap rho xi) F‖ ≤ ‖F‖ * ‖xi‖
      calc
        ‖extend (vectorMap rho xi) F‖ ≤ ‖vectorMap rho xi‖ * ‖F‖ :=
          norm_extend_apply_le _ _
        _ ≤ ‖xi‖ * ‖F‖ := mul_le_mul_of_nonneg_right
          (norm_vectorMap_le rho xi) (norm_nonneg F)
        _ = ‖F‖ * ‖xi‖ := mul_comm _ _)

@[simp]
theorem extension_apply (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (F : StrongDual ℂ (StrongDual ℂ A)) (xi : H) :
    extension rho F xi = extend (vectorMap rho xi) F := rfl

/-- This coefficient identity determines both currying variables and is the
normality statement needed by the represented topology. -/
@[simp]
theorem coefficient_extension (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (F : StrongDual ℂ (StrongDual ℂ A)) (xi : H) (g : StrongDual ℂ H) :
    g (extension rho F xi) = F (coefficient rho xi g) := by
  exact dual_extend (vectorMap rho xi) F g

@[simp]
theorem extension_canonical (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    extension rho (NormedSpace.inclusionInDoubleDual ℂ A a) = rho a := by
  apply ContinuousLinearMap.ext
  intro xi
  exact extend_canonical (vectorMap rho xi) a

/-- The operator extension is contractive, for all representations and not
only irreducible or faithful ones. -/
theorem norm_extension_apply_le (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (F : StrongDual ℂ (StrongDual ℂ A)) : ‖extension rho F‖ ≤ ‖F‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
  intro xi
  calc
    ‖extension rho F xi‖ ≤ ‖vectorMap rho xi‖ * ‖F‖ :=
      norm_extend_apply_le _ _
    _ ≤ ‖xi‖ * ‖F‖ := mul_le_mul_of_nonneg_right
      (norm_vectorMap_le rho xi) (norm_nonneg F)
    _ = ‖F‖ * ‖xi‖ := mul_comm _ _

private noncomputable instance extensionOperatorNorm :
    Norm (StrongDual ℂ (StrongDual ℂ A) →L[ℂ] (H →L[ℂ] H)) where
  norm f := sInf { c : ℝ | 0 ≤ c ∧ ∀ F, ‖f F‖ ≤ c * ‖F‖ }

theorem norm_extension_le_one (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    ‖extension rho‖ ≤ 1 := by
  change sInf { c : ℝ | 0 ≤ c ∧ ∀ F, ‖extension rho F‖ ≤ c * ‖F‖ } ≤ 1
  apply csInf_le
  · exact ⟨0, fun c hc => hc.1⟩
  · exact ⟨zero_le_one, fun F => by
      simpa only [one_mul] using norm_extension_apply_le rho F⟩

/-- Coefficientwise weak-star continuity is proved by an actual fixed
source functional. -/
theorem coefficient_extension_weakStarContinuous
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (xi : H) (g : StrongDual ℂ H) :
    Continuous (fun F : WeakDual ℂ (StrongDual ℂ A) =>
      g (extension rho (WeakDual.toStrongDual F) xi)) := by
  simpa only [coefficient_extension, WeakDual.toStrongDual_apply] using
    (WeakDual.eval_continuous (coefficient rho xi g))

/-- The correct topological extension is weak-star to WOT, not weak-star to
operator norm. -/
theorem extension_weakStar_wotContinuous
    (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    Continuous (fun F : WeakDual ℂ (StrongDual ℂ A) =>
      ContinuousLinearMapWOT.ofCLM (extension rho (WeakDual.toStrongDual F))) := by
  apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
  intro xi g
  exact coefficient_extension_weakStarContinuous rho xi g

/-- Agreement on all represented coefficients characterizes an operator.
No arbitrary projective-tensor functional is replaced by these tests. -/
theorem extension_eq_iff (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (F : StrongDual ℂ (StrongDual ℂ A)) (T : H →L[ℂ] H) :
    extension rho F = T ↔
      ∀ xi : H, ∀ g : StrongDual ℂ H, F (coefficient rho xi g) = g (T xi) := by
  constructor
  · intro h xi g
    rw [← coefficient_extension, h]
  · intro h
    apply ContinuousLinearMap.ext
    intro xi
    apply eq_of_dual_eq
    intro g
    rw [coefficient_extension]
    exact h xi g

/-- A zero extension is exactly annihilation of the represented coefficient
space, without an unproved central-projection description of that kernel. -/
theorem extension_eq_zero_iff (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    extension rho F = 0 ↔
      ∀ xi : H, ∀ g : StrongDual ℂ H, F (coefficient rho xi g) = 0 := by
  simpa only [ContinuousLinearMap.zero_apply, map_zero] using
    extension_eq_iff rho F 0

/-- The same operator extension has a canonical formulation on the existing
`BidualModel`; no parallel bidual topology or multiplication is installed. -/
def extensionModel (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    MathlibAnnex.BidualBilinear.BidualModel ℂ A →L[ℂ] (H →L[ℂ] H) :=
  (extension rho).comp
    (MathlibAnnex.BidualBilinear.bidualModelEquiv ℂ A).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem extensionModel_up (rho : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    extensionModel rho (ULift.up F) = extension rho F := rfl

end MathlibAnnex.RepresentedBidual
