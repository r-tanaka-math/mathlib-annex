import MathlibAnnex.Analysis.Normed.Operator.WeakCompact
import Mathlib.Analysis.Complex.Basic

/-!
# Recovering Hilbert-space vectors from the Banach bidual

The canonical embedding of a complete Hilbert space is onto.  This file
bundles its inverse and extends every operator into a Hilbert space to the
bidual of its domain.  No weak compactness hypothesis is added to that
operator: the required reflexivity is proved by the existing Hilbert-space
provider.  The extension varies bounded-linearly with the original operator.

Controller source checkpoint C01.  Proof bodies written; not compiled here.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 10
noncomputable section

open MathlibAnnex.WeakCompact

namespace MathlibAnnex.HilbertBidual

universe uX uH uK

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- The canonical map, made an equivalence using actual Hilbert reflexivity. -/
def canonicalEquiv (H : Type uH) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    H ≃ₗᵢ[ℂ] StrongDual ℂ (StrongDual ℂ H) :=
  LinearIsometryEquiv.ofSurjective
    (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℂ) (E := H))
    (isReflexive_innerProductSpace (𝕜 := ℂ) (H := H))

@[simp]
theorem canonicalEquiv_apply (x : H) :
    canonicalEquiv H x = NormedSpace.inclusionInDoubleDual ℂ H x := rfl

/-- The inverse is linear and isometric, not a separately chosen vector for
individual coefficient equations. -/
def recover : StrongDual ℂ (StrongDual ℂ H) →L[ℂ] H :=
  (canonicalEquiv H).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem canonical_recover (F : StrongDual ℂ (StrongDual ℂ H)) :
    NormedSpace.inclusionInDoubleDual ℂ H (recover F) = F :=
  (canonicalEquiv H).apply_symm_apply F

@[simp]
theorem recover_canonical (x : H) :
    recover (NormedSpace.inclusionInDoubleDual ℂ H x) = x :=
  (canonicalEquiv H).symm_apply_apply x

@[simp]
theorem dual_recover (F : StrongDual ℂ (StrongDual ℂ H))
    (g : StrongDual ℂ H) : g (recover F) = F g :=
  congrArg (fun z : StrongDual ℂ (StrongDual ℂ H) => z g)
    (canonical_recover F)

@[simp]
theorem norm_recover (F : StrongDual ℂ (StrongDual ℂ H)) :
    ‖recover F‖ = ‖F‖ := (canonicalEquiv H).symm.norm_map F

/-- Continuous linear functionals separate vectors, including in the zero
Hilbert space. -/
theorem eq_of_dual_eq {x y : H}
    (h : ∀ g : StrongDual ℂ H, g x = g y) : x = y := by
  apply (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℂ) (E := H)).injective
  apply ContinuousLinearMap.ext
  exact h

/-- The norm estimate for the ordinary bidual operator, proved from its
coefficient formula. -/
theorem norm_bidualMap_le (T : X →L[ℂ] H) : ‖bidualMap T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro F
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg T) (norm_nonneg F))
  intro g
  change ‖F (g.comp T)‖ ≤ ‖T‖ * ‖F‖ * ‖g‖
  calc
    ‖F (g.comp T)‖ ≤ ‖F‖ * ‖g.comp T‖ := F.le_opNorm _
    _ ≤ ‖F‖ * (‖g‖ * ‖T‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le g T)
        (norm_nonneg F)
    _ = ‖T‖ * ‖F‖ * ‖g‖ := by ring

/-- The actual bidual extension of a Hilbert-valued bounded operator. -/
def extend (T : X →L[ℂ] H) : StrongDual ℂ (StrongDual ℂ X) →L[ℂ] H :=
  recover.comp (bidualMap T)

@[simp]
theorem dual_extend (T : X →L[ℂ] H)
    (F : StrongDual ℂ (StrongDual ℂ X)) (g : StrongDual ℂ H) :
    g (extend T F) = F (g.comp T) := by
  exact dual_recover (bidualMap T F) g

@[simp]
theorem extend_canonical (T : X →L[ℂ] H) (x : X) :
    extend T (NormedSpace.inclusionInDoubleDual ℂ X x) = T x := by
  apply eq_of_dual_eq
  intro g
  rw [dual_extend]
  rfl

theorem norm_extend_apply_le (T : X →L[ℂ] H)
    (F : StrongDual ℂ (StrongDual ℂ X)) :
    ‖extend T F‖ ≤ ‖T‖ * ‖F‖ := by
  change ‖recover (bidualMap T F)‖ ≤ _
  rw [norm_recover]
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg T) (norm_nonneg F))
  intro g
  change ‖F (g.comp T)‖ ≤ ‖T‖ * ‖F‖ * ‖g‖
  calc
    ‖F (g.comp T)‖ ≤ ‖F‖ * ‖g.comp T‖ := F.le_opNorm _
    _ ≤ ‖F‖ * (‖g‖ * ‖T‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le g T)
        (norm_nonneg F)
    _ = ‖T‖ * ‖F‖ * ‖g‖ := by ring

theorem norm_extend_le (T : X →L[ℂ] H) : ‖extend T‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    (norm_extend_apply_le T)

@[simp]
theorem extend_add (T S : X →L[ℂ] H) : extend (T + S) = extend T + extend S := by
  apply ContinuousLinearMap.ext
  intro F
  apply eq_of_dual_eq
  intro g
  have hcomp : g.comp (T + S) = g.comp T + g.comp S := by
    ext x
    simp
  simp only [ContinuousLinearMap.add_apply, map_add, dual_extend, hcomp]

@[simp]
theorem extend_smul (c : ℂ) (T : X →L[ℂ] H) :
    extend (c • T) = c • extend T := by
  apply ContinuousLinearMap.ext
  intro F
  apply eq_of_dual_eq
  intro g
  have hcomp : g.comp (c • T) = c • g.comp T := by
    ext x
    simp
  simp only [ContinuousLinearMap.smul_apply, map_smul, dual_extend, hcomp]

/-- A single continuous linear extension operation on all Hilbert-valued
operators; this is what allows the represented extension to depend linearly
on the input vector. -/
def extensionMap : (X →L[ℂ] H) →L[ℂ]
    (StrongDual ℂ (StrongDual ℂ X) →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := extend
      map_add' := extend_add
      map_smul' := extend_smul }
    1 (fun T => by
      change ‖extend T‖ ≤ 1 * ‖T‖
      simpa only [one_mul] using norm_extend_le T)

@[simp]
theorem extensionMap_apply (T : X →L[ℂ] H) : extensionMap T = extend T := rfl

/-- Extension commutes with postcomposition by a bounded operator between
Hilbert spaces.  This is proved from the coefficient formula, not imposed. -/
theorem extend_postcomp (S : H →L[ℂ] K) (T : X →L[ℂ] H) :
    extend (S.comp T) = S.comp (extend T) := by
  apply ContinuousLinearMap.ext
  intro F
  apply eq_of_dual_eq
  intro g
  rw [dual_extend]
  change F (g.comp (S.comp T)) = (g.comp S) (extend T F)
  rw [dual_extend]
  rfl

/-- Full norm preservation follows by restriction to the canonical copy. -/
theorem norm_extend (T : X →L[ℂ] H) : ‖extend T‖ = ‖T‖ := by
  apply le_antisymm (norm_extend_le T)
  apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg (extend T))
  intro x
  rw [← extend_canonical T x]
  have hc : ‖NormedSpace.inclusionInDoubleDual ℂ X x‖ = ‖x‖ := by
    change ‖(NormedSpace.inclusionInDoubleDualLi (𝕜 := ℂ) (E := X)) x‖ = ‖x‖
    exact (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℂ) (E := X)).norm_map x
  calc
    ‖extend T (NormedSpace.inclusionInDoubleDual ℂ X x)‖ ≤
        ‖extend T‖ * ‖NormedSpace.inclusionInDoubleDual ℂ X x‖ :=
      (ContinuousLinearMap.isLeast_opNorm (extend T)).1.2 _
    _ = ‖extend T‖ * ‖x‖ := by rw [hc]

end MathlibAnnex.HilbertBidual
