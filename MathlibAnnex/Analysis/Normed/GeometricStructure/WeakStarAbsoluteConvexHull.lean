/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.WeakStarCommonAbsoluteSupport
public import MathlibAnnex.Analysis.Convex.Milman
public import MathlibAnnex.Analysis.Normed.GeometricStructure.MaximalFilter

/-!
# Extreme points of the weak-star closed convex hull of common supports

Milman's converse is supplied by the pinned Annex module
`MathlibAnnex.Analysis.Convex.Milman`; it is not supplied merely by importing
Krein-Milman. No second copy of that existing module is created here.

The closed convex hull below is taken in `WeakDual`, over the real scalars.
First Milman's converse places its extreme points in the common-support set.
The extreme-subset property then gives extremality in the full dual ball.
The converse inclusion is algebraic, so an equality is also obtained.

These statements generalize the independent extreme-point conclusion of
JMAA 514 (2022), Lemma 4.2: nonemptiness of the primal indexing set suffices;
maximality, completeness and nontriviality are not required. Nonemptiness of
the support set for an order filter was established in the preceding module.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Set Metric

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The actual weak-star closed convex hull stays in the dual unit ball. -/
theorem closure_convexHull_weakStarCommonAbsoluteNormingFunctionals_subset_closedBall
    {U : Set E} (hne : U.Nonempty) :
    closure (convexHull ℝ (weakStarCommonAbsoluteNormingFunctionals 𝕜 U)) ⊆
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1 := by
  apply closure_minimal _ (WeakDual.isClosed_closedBall (0 : StrongDual 𝕜 E) 1)
  apply convexHull_min (weakStarCommonAbsoluteNormingFunctionals_subset_closedBall 𝕜 hne)
  intro f hf g hg a b ha hb hab
  change a • f.toStrongDual + b • g.toStrongDual ∈ closedBall (0 : StrongDual 𝕜 E) 1
  exact (convex_closedBall (0 : StrongDual 𝕜 E) 1) hf hg ha hb hab

theorem isCompact_closure_convexHull_weakStarCommonAbsoluteNormingFunctionals
    {U : Set E} (hne : U.Nonempty) :
    IsCompact (closure (convexHull ℝ (weakStarCommonAbsoluteNormingFunctionals 𝕜 U))) := by
  letI : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 E) 1).of_isClosed_subset
    isClosed_closure
    (closure_convexHull_weakStarCommonAbsoluteNormingFunctionals_subset_closedBall 𝕜 hne)

/-- The independent Milman/extreme-point conclusion, including extremality in
both the weak-star closed convex hull and the entire dual ball. -/
theorem extremePoints_closure_convexHull_weakStarCommonAbsoluteNormingFunctionals_subset
    {U : Set E} (hne : U.Nonempty) :
    (closure (convexHull ℝ (weakStarCommonAbsoluteNormingFunctionals 𝕜 U))).extremePoints ℝ ⊆
      weakStarCommonAbsoluteNormingFunctionals 𝕜 U ∩
        (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1).extremePoints ℝ := by
  letI : LocallyConvexSpace ℝ (WeakDual 𝕜 E) :=
    WeakBilin.locallyConvexSpace (B := topDualPairing 𝕜 E)
  let A : Set (WeakDual 𝕜 E) := weakStarCommonAbsoluteNormingFunctionals 𝕜 U
  let C : Set (WeakDual 𝕜 E) := closure (convexHull ℝ A)
  have hAC : A ⊆ C := (subset_convexHull ℝ A).trans subset_closure
  have hCc : IsCompact C :=
    isCompact_closure_convexHull_weakStarCommonAbsoluteNormingFunctionals 𝕜 hne
  have hCv : Convex ℝ C := (convex_convexHull ℝ A).closure
  intro f hf
  have hfAclosure : f ∈ closure A :=
    mem_closure_of_mem_extremePoints_of_mem_closure_convexHull
      (E := WeakDual 𝕜 E) (C := C) (S := A) (x := f) hCc hCv hAC hf hf.1
  have hfA : f ∈ A := by
    have hAclosed : IsClosed A := isClosed_weakStarCommonAbsoluteNormingFunctionals 𝕜 U
    exact hAclosed.closure_eq ▸ hfAclosure
  have hfAext : f ∈ A.extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset
      (𝕜 := ℝ) (A := C) (B := A) hAC ⟨hfA, hf⟩
  have hAext := isExtreme_weakStarCommonAbsoluteNormingFunctionals 𝕜 hne
  exact ⟨hfA, hAext.extremePoints_subset_extremePoints hfAext⟩

/-- The reverse inclusion needs no topological argument: an extreme point of
the ball which belongs to the common set stays extreme in the smaller hull. -/
theorem extremePoints_closure_convexHull_weakStarCommonAbsoluteNormingFunctionals_eq_inter
    {U : Set E} (hne : U.Nonempty) :
    (closure (convexHull ℝ (weakStarCommonAbsoluteNormingFunctionals 𝕜 U))).extremePoints ℝ =
      weakStarCommonAbsoluteNormingFunctionals 𝕜 U ∩
        (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1).extremePoints ℝ := by
  apply Subset.antisymm
    (extremePoints_closure_convexHull_weakStarCommonAbsoluteNormingFunctionals_subset 𝕜 hne)
  rintro f ⟨hfA, hfB⟩
  exact inter_extremePoints_subset_extremePoints_of_subset
    (closure_convexHull_weakStarCommonAbsoluteNormingFunctionals_subset_closedBall 𝕜 hne)
    ⟨subset_closure (subset_convexHull ℝ _ hfA), hfB⟩

/-- The support-hull has an extreme point for an actual order filter.
This is separate from, and does not replace, the extreme-point inclusion. -/
theorem IsBirkhoffJamesFilter.nonempty_extremePoints_closure_convexHull_weakStarCommonAbsoluteNormingFunctionals
    {U : Set E} (hU : IsBirkhoffJamesFilter 𝕜 U) :
    ((closure (convexHull ℝ (weakStarCommonAbsoluteNormingFunctionals 𝕜 U))).extremePoints ℝ).Nonempty := by
  letI : LocallyConvexSpace ℝ (WeakDual 𝕜 E) :=
    WeakBilin.locallyConvexSpace (B := topDualPairing 𝕜 E)
  apply (isCompact_closure_convexHull_weakStarCommonAbsoluteNormingFunctionals 𝕜
    (hU.nonempty 𝕜)).extremePoints_nonempty
  exact (hU.nonempty_weakStarCommonAbsoluteNormingFunctionals 𝕜).mono
    ((subset_convexHull ℝ _).trans subset_closure)

end NormedSpace

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V] [Nontrivial V]

/-- For a maximal filter in a nontrivial normed space, the contractive
common-support carrier is exactly the norm-one carrier used in REF42.
This identification is not extended to the zero space. -/
theorem IsMaximalBirkhoffJamesFilter.weakStarCommonAbsoluteNormingFunctionals_eq_setOf_norm_eq_one
    {U : Set V} (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) :
    weakStarCommonAbsoluteNormingFunctionals 𝕜 U =
      {f : WeakDual 𝕜 V | ‖f.toStrongDual‖ = 1 ∧ ∀ x ∈ U, ‖f x‖ = ‖x‖} := by
  ext f
  constructor
  · intro hf
    have h := (mem_weakStarCommonAbsoluteNormingFunctionals 𝕜).mp hf
    exact ⟨hU.norm_eq_one 𝕜 h, fun x hx => (h x hx).2⟩
  · rintro ⟨hfnorm, hf⟩
    exact (mem_weakStarCommonAbsoluteNormingFunctionals 𝕜).mpr
      (fun x hx => ⟨hfnorm.le, hf x hx⟩)

end NormedSpace
