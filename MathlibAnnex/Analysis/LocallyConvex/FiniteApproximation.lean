import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Finite approximation from a weak-star bidual point

This file isolates the convexity argument behind simultaneous finite
approximation.  It deliberately does not assume separability or replace weak
closure by sequential closure.
-/

set_option autoImplicit false

open Topology

namespace MathlibAnnex.FiniteApproximation

universe uK uX uZ

noncomputable section

variable {𝕜 : Type uK} [RCLike 𝕜]
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
variable {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedSpace ℝ Z] [IsScalarTower ℝ 𝕜 Z]

/-- Pullback of continuous functionals along a continuous linear map. -/
def dualMap (T : X →L[𝕜] Z) : StrongDual 𝕜 Z →L[𝕜] StrongDual 𝕜 X :=
  (ContinuousLinearMap.compL 𝕜 X Z 𝕜).flip T

@[simp]
theorem dualMap_apply (T : X →L[𝕜] Z) (g : StrongDual 𝕜 Z) :
    dualMap T g = g.comp T := rfl

/-- The bidual map, equipped with the weak-star topologies on both sides. -/
def weakStarMap (T : X →L[𝕜] Z) :
    WeakDual 𝕜 (StrongDual 𝕜 X) →L[𝕜]
      WeakDual 𝕜 (StrongDual 𝕜 Z) where
  toLinearMap :=
    ((ContinuousLinearMap.compL 𝕜 (StrongDual 𝕜 Z) (StrongDual 𝕜 X) 𝕜).flip
      (dualMap T)).toLinearMap
  cont := WeakDual.continuous_of_continuous_eval fun g ↦
    WeakDual.eval_continuous (dualMap T g)

@[simp]
theorem weakStarMap_apply (T : X →L[𝕜] Z)
    (omega : WeakDual 𝕜 (StrongDual 𝕜 X)) (g : StrongDual 𝕜 Z) :
    weakStarMap T omega g = omega (g.comp T) := rfl

/-- The canonical copy of a set in the weak-star bidual. -/
def canonicalImage (D : Set X) : Set (WeakDual 𝕜 (StrongDual 𝕜 X)) :=
  NormedSpace.inclusionInDoubleDualWeak 𝕜 X '' (toWeakSpace 𝕜 X '' D)

/-- A bidual functional is in the weak-star closure of the canonical image of `D`. -/
def InWeakStarClosure (omega : StrongDual 𝕜 (StrongDual 𝕜 X))
    (D : Set X) : Prop :=
  StrongDual.toWeakDual omega ∈ closure (canonicalImage D)

/-- A point of `D`, viewed in the bidual, belongs to the weak-star closure
of the canonical image of `D`. -/
theorem inWeakStarClosure_of_mem {D : Set X} {x : X} (hx : x ∈ D) :
    InWeakStarClosure (NormedSpace.inclusionInDoubleDual 𝕜 X x) D := by
  apply subset_closure
  exact ⟨toWeakSpace 𝕜 X x, ⟨x, hx, rfl⟩, rfl⟩

/-- Push a weak-star closure hypothesis through one continuous linear map and
recover norm closure when the original set is real-convex. -/
theorem image_mem_closure {D : Set X} (hD : Convex ℝ D)
    {omega : StrongDual 𝕜 (StrongDual 𝕜 X)} (homega : InWeakStarClosure omega D)
    (T : X →L[𝕜] Z) (z : Z)
    (hT : ∀ g : StrongDual 𝕜 Z, omega (g.comp T) = g z) :
    z ∈ closure (T '' D) := by
  let jZ := NormedSpace.inclusionInDoubleDualWeak 𝕜 Z
  let sZ : Set (WeakSpace 𝕜 Z) := toWeakSpace 𝕜 Z '' (T '' D)
  have hmaps : Set.MapsTo (weakStarMap T) (canonicalImage D) (jZ '' sZ) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨toWeakSpace 𝕜 Z (T x), ⟨_, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    apply WeakDual.toStrongDual.injective
    apply ContinuousLinearMap.ext
    intro g
    rfl
  have hpush0 := mem_closure_image (weakStarMap T).continuous.continuousAt homega
  have hpush : weakStarMap T (StrongDual.toWeakDual omega) ∈ closure (jZ '' sZ) :=
    closure_mono hmaps.image_subset hpush0
  have hpush_eq : weakStarMap T (StrongDual.toWeakDual omega) =
      jZ (toWeakSpace 𝕜 Z z) := by
    apply WeakDual.toStrongDual.injective
    apply ContinuousLinearMap.ext
    intro g
    exact hT g
  have hzweak : toWeakSpace 𝕜 Z z ∈ closure sZ := by
    rw [(NormedSpace.isEmbedding_inclusionInDoubleDualWeak 𝕜 Z).closure_eq_preimage_closure_image sZ]
    simpa [hpush_eq] using hpush
  have hconv : Convex ℝ (T '' D) := by
    change Convex ℝ ((T.restrictScalars ℝ) '' D)
    exact hD.linear_image (T.restrictScalars ℝ).toLinearMap
  have hzimage : toWeakSpace 𝕜 Z z ∈ toWeakSpace 𝕜 Z '' closure (T '' D) := by
    rw [hconv.toWeakSpace_closure 𝕜]
    exact hzweak
  rcases hzimage with ⟨z', hz', hz'eq⟩
  have : z' = z := (toWeakSpace 𝕜 Z).injective hz'eq
  simpa [this] using hz'

/-- Norm approximation consequence of `image_mem_closure`. -/
theorem exists_norm_sub_lt {D : Set X} (hD : Convex ℝ D)
    {omega : StrongDual 𝕜 (StrongDual 𝕜 X)} (homega : InWeakStarClosure omega D)
    (T : X →L[𝕜] Z) (z : Z)
    (hT : ∀ g : StrongDual 𝕜 Z, omega (g.comp T) = g z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d ∈ D, ‖T d - z‖ < ε := by
  obtain ⟨w, ⟨d, hd, rfl⟩, hw⟩ :=
    Metric.mem_closure_iff.mp (image_mem_closure hD homega T z hT) ε hε
  exact ⟨d, hd, by simpa [dist_eq_norm, norm_sub_rev] using hw⟩

/-- Simultaneously meet a norm constraint and a moment constraint with the
same point of the convex set.  The hypothesis is a single weak-star moment
identity for the product map; it does not select separate convex
combinations for the two coordinates. -/
theorem exists_norm_and_moment_lt
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
      [NormedSpace ℝ W] [IsScalarTower ℝ 𝕜 W]
    {D : Set X} (hD : Convex ℝ D)
    {omega : StrongDual 𝕜 (StrongDual 𝕜 X)} (homega : InWeakStarClosure omega D)
    (T : X →L[𝕜] Z) (M : X →L[𝕜] W) (z : Z) (w : W)
    (hTM : ∀ g : StrongDual 𝕜 (Z × W),
      omega (g.comp (T.prod M)) = g (z, w))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d ∈ D, ‖T d - z‖ < ε ∧ ‖M d - w‖ < ε := by
  obtain ⟨d, hd, hprod⟩ := exists_norm_sub_lt hD homega (T.prod M) (z, w) hTM hε
  refine ⟨d, hd, ?_, ?_⟩
  · apply lt_of_le_of_lt _ hprod
    change ‖T d - z‖ ≤ max ‖T d - z‖ ‖M d - w‖
    exact le_max_left _ _
  · apply lt_of_le_of_lt _ hprod
    change ‖M d - w‖ ≤ max ‖T d - z‖ ‖M d - w‖
    exact le_max_right _ _

/-- Finite homogeneous families of norm and scalar-moment conditions can be
met simultaneously by one point of `D`.  Empty index types are allowed. -/
theorem exists_finite_norm_and_moment_lt
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {D : Set X} (hD : Convex ℝ D)
    {omega : StrongDual 𝕜 (StrongDual 𝕜 X)} (homega : InWeakStarClosure omega D)
    (T : X →L[𝕜] (ι → Z)) (M : X →L[𝕜] (κ → 𝕜))
    (z : ι → Z) (w : κ → 𝕜)
    (hTM : ∀ g : StrongDual 𝕜 ((ι → Z) × (κ → 𝕜)),
      omega (g.comp (T.prod M)) = g (z, w))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d ∈ D, (∀ i, ‖T d i - z i‖ < ε) ∧ (∀ j, ‖M d j - w j‖ < ε) := by
  obtain ⟨d, hd, hT, hM⟩ :=
    exists_norm_and_moment_lt hD homega T M z w hTM hε
  refine ⟨d, hd, fun i ↦ ?_, fun j ↦ ?_⟩
  · exact (norm_le_pi_norm (T d - z) i).trans_lt (by simpa using hT)
  · exact (norm_le_pi_norm (M d - w) j).trans_lt (by simpa using hM)

/-- Componentwise bidual identities imply the single product-map identity
needed for simultaneous approximation.  This is the finite heterogeneous
assembly step: no separate point of `D` is selected for any component. -/
theorem exists_finite_norm_and_moment_lt_of_components
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {D : Set X} (hD : Convex ℝ D)
    {omega : StrongDual 𝕜 (StrongDual 𝕜 X)} (homega : InWeakStarClosure omega D)
    (T : X →L[𝕜] (ι → Z)) (M : X →L[𝕜] (κ → 𝕜))
    (z : ι → Z) (w : κ → 𝕜)
    (hT : ∀ (i : ι) (g : StrongDual 𝕜 Z),
      omega (g.comp ((ContinuousLinearMap.proj i).comp T)) = g (z i))
    (hM : ∀ (j : κ) (g : StrongDual 𝕜 𝕜),
      omega (g.comp ((ContinuousLinearMap.proj j).comp M)) = g (w j))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d ∈ D, (∀ i, ‖T d i - z i‖ < ε) ∧
      (∀ j, ‖M d j - w j‖ < ε) := by
  classical
  apply exists_finite_norm_and_moment_lt hD homega T M z w _ hε
  intro g
  let inT : (ι → Z) →L[𝕜] (ι → Z) × (κ → 𝕜) :=
    ContinuousLinearMap.inl 𝕜 (ι → Z) (κ → 𝕜)
  let inM : (κ → 𝕜) →L[𝕜] (ι → Z) × (κ → 𝕜) :=
    ContinuousLinearMap.inr 𝕜 (ι → Z) (κ → 𝕜)
  have hdecomp : g.comp (T.prod M) =
      (∑ i, (g.comp (inT.comp
          (ContinuousLinearMap.single 𝕜 (fun _ : ι ↦ Z) i))).comp
        ((ContinuousLinearMap.proj i).comp T)) +
      ∑ j, (g.comp (inM.comp
          (ContinuousLinearMap.single 𝕜 (fun _ : κ ↦ 𝕜) j))).comp
        ((ContinuousLinearMap.proj j).comp M) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply]
    have hsumT :
        (∑ i, g (inT (ContinuousLinearMap.single 𝕜 (fun _ : ι ↦ Z) i (T x i)))) =
          g (inT (T x)) := by
      simpa only [ContinuousLinearMap.comp_apply] using
        ContinuousLinearMap.sum_comp_single 𝕜 (fun _ : ι ↦ Z) (g.comp inT) (T x)
    have hsumM :
        (∑ j, g (inM (ContinuousLinearMap.single 𝕜 (fun _ : κ ↦ 𝕜) j (M x j)))) =
          g (inM (M x)) := by
      simpa only [ContinuousLinearMap.comp_apply] using
        ContinuousLinearMap.sum_comp_single 𝕜 (fun _ : κ ↦ 𝕜) (g.comp inM) (M x)
    simp only [ContinuousLinearMap.proj_apply]
    rw [hsumT, hsumM]
    simpa [inT, inM] using map_add g (T x, 0) (0, M x)
  rw [hdecomp, map_add, map_sum, map_sum]
  simp_rw [hT, hM]
  have hsumT :
      (∑ i, (g.comp (inT.comp
        (ContinuousLinearMap.single 𝕜 (fun _ : ι ↦ Z) i))) (z i)) =
        g (inT z) := ContinuousLinearMap.sum_comp_single
          𝕜 (fun _ : ι ↦ Z) (g.comp inT) z
  have hsumM :
      (∑ j, (g.comp (inM.comp
        (ContinuousLinearMap.single 𝕜 (fun _ : κ ↦ 𝕜) j))) (w j)) =
        g (inM w) := ContinuousLinearMap.sum_comp_single
          𝕜 (fun _ : κ ↦ 𝕜) (g.comp inM) w
  rw [hsumT, hsumM]
  simpa [inT, inM] using (map_add g (z, 0) (0, w)).symm

end

end MathlibAnnex.FiniteApproximation
