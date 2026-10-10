/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.SurjectiveDual
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Extreme points of a C-star quotient annihilator

The isometry onto the whole annihilator first identifies its SUBTYPE ball
and its extreme points. The ambient extreme-pullback theorem then proves
that this subspace ball has no new extreme points. Both the subtype and
ambient-set formulations are recorded. Nontriviality belongs to the target,
not to the preceding norm-isometry construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.whnf.reducibleClassField false
noncomputable section
open Set Metric
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B]
variable (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q)

private def annihilatorContinuousMap {C D : Type*}
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    (q : C →⋆ₙₐ[ℂ] D) : C →L[ℂ] D :=
  LinearMap.mkContinuous
    { toFun := q, map_add' := map_add q, map_smul' := map_smul q }
    1 (fun a => by
      change ‖q a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le q a)

/-- Convex extreme points are transported to the actual annihilator SUBTYPE. -/
theorem surjectiveDualLinearIsometryEquiv_mem_extremePoints_iff (rho : StrongDual ℂ B) :
    surjectiveDualLinearIsometryEquiv q hq rho ∈
        (closedBall (0 : (annihilatorContinuousMap q).ker.strongDualAnnihilator) 1).extremePoints ℝ ↔
      rho ∈ (closedBall (0 : StrongDual ℂ B) 1).extremePoints ℝ := by
  let e := surjectiveDualLinearIsometryEquiv q hq
  have hball (f : StrongDual ℂ B) : e f ∈ closedBall 0 1 ↔ f ∈ closedBall 0 1 := by
    simp only [mem_closedBall_zero_iff (a := e f),
      mem_closedBall_zero_iff (a := f), e.norm_map]
  have hmap (s t : ℝ) (f g : StrongDual ℂ B) :
      e (s • f + t • g) = s • e f + t • e g := by
    apply Subtype.ext
    ext a
    rfl
  change e rho ∈ _ ↔ rho ∈ _
  simp only [mem_extremePoints_iff_left]
  constructor
  · rintro ⟨hrho, hext⟩
    refine ⟨(hball rho).1 hrho, ?_⟩
    intro f hf g hg hseg
    obtain ⟨s, t, hs, ht, hst, hfg⟩ := hseg
    exact e.injective (hext (e f) ((hball f).2 hf) (e g) ((hball g).2 hg)
      ⟨s, t, hs, ht, hst, (hmap s t f g).symm.trans (congrArg e hfg)⟩)
  · rintro ⟨hrho, hext⟩
    refine ⟨(hball rho).2 hrho, ?_⟩
    intro F hF G hG hseg
    obtain ⟨f, rfl⟩ := e.surjective F
    obtain ⟨g, rfl⟩ := e.surjective G
    obtain ⟨s, t, hs, ht, hst, hfg⟩ := hseg
    have hlin : s • f + t • g = rho :=
      e.injective ((hmap s t f g).trans hfg)
    exact congrArg e (hext f ((hball f).1 hF) g ((hball g).1 hG)
      ⟨s, t, hs, ht, hst, hlin⟩)

/-- The SUBTYPE ball has the same norm as its ambient image, for every real radius. -/
theorem image_closedBall_annihilator_val (r : ℝ) :
    (Subtype.val : (annihilatorContinuousMap q).ker.strongDualAnnihilator → StrongDual ℂ A) ''
        closedBall 0 r =
      closedBall 0 r ∩
        ((annihilatorContinuousMap q).ker.strongDualAnnihilator : Set (StrongDual ℂ A)) := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(mem_closedBall_zero_iff (a := g.val)).mpr
      ((mem_closedBall_zero_iff (a := g)).mp hg), g.property⟩
  · rintro ⟨hf, hg⟩
    exact ⟨⟨f, hg⟩, (mem_closedBall_zero_iff
      (a := (⟨f, hg⟩ : (annihilatorContinuousMap q).ker.strongDualAnnihilator))).mpr
        ((mem_closedBall_zero_iff (a := f)).mp hf), rfl⟩

variable [Nontrivial B]

include hq in
/-- Literal subspace-ball extremality is equivalent to AMBIENT-ball extremality. -/
theorem mem_extremePoints_annihilator_closedBall_iff
    (g : (annihilatorContinuousMap q).ker.strongDualAnnihilator) :
    g ∈ (closedBall (0 : (annihilatorContinuousMap q).ker.strongDualAnnihilator) 1).extremePoints ℝ ↔
      g.val ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ := by
  obtain ⟨rho, rfl⟩ := (surjectiveDualLinearIsometryEquiv q hq).surjective g
  exact (surjectiveDualLinearIsometryEquiv_mem_extremePoints_iff q hq rho).trans
    (comp_mem_extremePoints_dual_closedBall_iff_of_surjective q hq rho).symm

include hq in
/-- The image of the subtype's extreme points, not merely one-sided preservation. -/
theorem image_extremePoints_annihilator_closedBall :
    (Subtype.val : (annihilatorContinuousMap q).ker.strongDualAnnihilator → StrongDual ℂ A) ''
        (closedBall 0 1).extremePoints ℝ =
      (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ ∩
        ((annihilatorContinuousMap q).ker.strongDualAnnihilator : Set (StrongDual ℂ A)) := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(mem_extremePoints_annihilator_closedBall_iff q hq g).1 hg, g.property⟩
  · rintro ⟨hf, hg⟩
    exact ⟨⟨f, hg⟩, (mem_extremePoints_annihilator_closedBall_iff q hq ⟨f, hg⟩).2 hf, rfl⟩

include hq in
/-- The pullback image can now legitimately be replaced by the FULL annihilator. -/
theorem image_extremePoints_dual_closedBall_eq_inter_annihilator :
    (fun f : StrongDual ℂ B => f.comp (annihilatorContinuousMap q)) ''
        (closedBall (0 : StrongDual ℂ B) 1).extremePoints ℝ =
      (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ ∩
        ((annihilatorContinuousMap q).ker.strongDualAnnihilator : Set (StrongDual ℂ A)) := by
  have himage : (fun f : StrongDual ℂ B => f.comp (annihilatorContinuousMap q)) ''
      (closedBall (0 : StrongDual ℂ B) 1).extremePoints ℝ =
      (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ ∩
        Set.range (fun f : StrongDual ℂ B => f.comp (annihilatorContinuousMap q)) :=
    image_extremePoints_dual_closedBall_of_surjective q hq
  have hrange : Set.range (fun f : StrongDual ℂ B => f.comp (annihilatorContinuousMap q)) =
      ((annihilatorContinuousMap q).ker.strongDualAnnihilator : Set (StrongDual ℂ A)) :=
    range_comp_eq_strongDualAnnihilator_of_surjective q hq
  rw [hrange] at himage
  exact himage

include hq in
/-- Ambient-set version of the annihilator-ball identity. This is not inferred
by silently confusing subtype extreme points with ambient extreme points. -/
theorem extremePoints_closedBall_inter_annihilator :
    (closedBall (0 : StrongDual ℂ A) 1 ∩
      ((annihilatorContinuousMap q).ker.strongDualAnnihilator : Set (StrongDual ℂ A))).extremePoints ℝ =
    (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ ∩
      ((annihilatorContinuousMap q).ker.strongDualAnnihilator : Set (StrongDual ℂ A)) := by
  ext f
  constructor
  · intro hf
    rw [mem_extremePoints_iff_left] at hf
    let g : (annihilatorContinuousMap q).ker.strongDualAnnihilator := ⟨f, hf.1.2⟩
    have hg : g ∈ (closedBall (0 : (annihilatorContinuousMap q).ker.strongDualAnnihilator) 1).extremePoints ℝ := by
      rw [mem_extremePoints_iff_left]
      refine ⟨(mem_closedBall_zero_iff (a := g)).mpr
        ((mem_closedBall_zero_iff (a := f)).mp hf.1.1), ?_⟩
      intro v hv w hw hseg
      obtain ⟨s, t, hs, ht, hst, hvw⟩ := hseg
      apply Subtype.ext
      apply hf.2 v.val ⟨(mem_closedBall_zero_iff (a := v.val)).mpr
        ((mem_closedBall_zero_iff (a := v)).mp hv), v.property⟩
        w.val ⟨(mem_closedBall_zero_iff (a := w.val)).mpr
          ((mem_closedBall_zero_iff (a := w)).mp hw), w.property⟩
      exact ⟨s, t, hs, ht, hst, congrArg Subtype.val hvw⟩
    exact ⟨(mem_extremePoints_annihilator_closedBall_iff q hq g).1 hg, hf.1.2⟩
  · rintro ⟨hf, hfa⟩
    rw [mem_extremePoints_iff_left] at hf ⊢
    refine ⟨⟨hf.1, hfa⟩, ?_⟩
    intro v hv w hw hseg
    exact hf.2 v hv.1 w hw.1 hseg

/-- The original kernel of a possibly nonsurjective homomorphism, not merely
the syntactically different kernel of its range restriction. -/
theorem extremePoints_closedBall_inter_ker_annihilator
    (hneq : ∃ a : A, q a ≠ 0) :
    (closedBall (0 : StrongDual ℂ A) 1 ∩
      ((annihilatorContinuousMap q).ker.strongDualAnnihilator : Set (StrongDual ℂ A))).extremePoints ℝ =
    (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ ∩
      ((annihilatorContinuousMap q).ker.strongDualAnnihilator : Set (StrongDual ℂ A)) := by
  letI : NonUnitalCStarAlgebra (NonUnitalStarAlgHom.range q) := HomKernelQuotient.imageCStarAlgebra q
  letI : PartialOrder (NonUnitalStarAlgHom.range q) := _root_.CStarAlgebra.spectralOrder (NonUnitalStarAlgHom.range q)
  letI : StarOrderedRing (NonUnitalStarAlgHom.range q) := _root_.CStarAlgebra.spectralOrderedRing (NonUnitalStarAlgHom.range q)
  letI : Nontrivial (NonUnitalStarAlgHom.range q) := by
    obtain ⟨a, ha⟩ := hneq
    refine ⟨⟨(NonUnitalStarAlgHom.rangeRestrict q) a, 0, ?_⟩⟩
    intro h
    exact ha (congrArg Subtype.val h)
  have hsurj : Function.Surjective (NonUnitalStarAlgHom.rangeRestrict q) := by
    intro b
    obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range q).1 b.property
    exact ⟨a, Subtype.ext ha⟩
  have hker : (annihilatorContinuousMap (NonUnitalStarAlgHom.rangeRestrict q)).ker = (annihilatorContinuousMap q).ker := by
    ext a
    change (NonUnitalStarAlgHom.rangeRestrict q) a = 0 ↔ q a = 0
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  simpa only [hker] using extremePoints_closedBall_inter_annihilator (NonUnitalStarAlgHom.rangeRestrict q) hsurj

/-- The subtype version for the ORIGINAL image kernel, with both inclusions. -/
theorem image_extremePoints_ker_annihilator_closedBall
    (hneq : ∃ a : A, q a ≠ 0) :
    (Subtype.val : (annihilatorContinuousMap q).ker.strongDualAnnihilator → StrongDual ℂ A) ''
        (closedBall 0 1).extremePoints ℝ =
      (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ ∩
        ((annihilatorContinuousMap q).ker.strongDualAnnihilator : Set (StrongDual ℂ A)) := by
  letI : NonUnitalCStarAlgebra (NonUnitalStarAlgHom.range q) := HomKernelQuotient.imageCStarAlgebra q
  letI : PartialOrder (NonUnitalStarAlgHom.range q) := _root_.CStarAlgebra.spectralOrder (NonUnitalStarAlgHom.range q)
  letI : StarOrderedRing (NonUnitalStarAlgHom.range q) := _root_.CStarAlgebra.spectralOrderedRing (NonUnitalStarAlgHom.range q)
  letI : Nontrivial (NonUnitalStarAlgHom.range q) := by
    obtain ⟨a, ha⟩ := hneq
    refine ⟨⟨(NonUnitalStarAlgHom.rangeRestrict q) a, 0, ?_⟩⟩
    intro h
    exact ha (congrArg Subtype.val h)
  have hsurj : Function.Surjective (NonUnitalStarAlgHom.rangeRestrict q) := by
    intro b
    obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range q).1 b.property
    exact ⟨a, Subtype.ext ha⟩
  have hker : (annihilatorContinuousMap (NonUnitalStarAlgHom.rangeRestrict q)).ker = (annihilatorContinuousMap q).ker := by
    ext a
    change (NonUnitalStarAlgHom.rangeRestrict q) a = 0 ↔ q a = 0
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have htransport := image_extremePoints_annihilator_closedBall (NonUnitalStarAlgHom.rangeRestrict q) hsurj
  rw [hker] at htransport
  exact htransport

end MathlibAnnex.Analysis.CStarAlgebra
