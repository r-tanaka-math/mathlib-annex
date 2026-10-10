/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.AtomicCommutant
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.NormAttainment

/-!
# Simultaneous one-vector density in inequivalent representations

A finite family of pairwise inequivalent nonzero irreducible representations
has dense simultaneous orbit at any tuple with nonzero coordinates. The
algebra elements belong to the original, possibly nonunital, algebra.

The closure of that orbit is a reducing subspace. Its orthogonal projection
has scalar diagonal blocks by bounded Schur theory. A norm-one element fixing
one prescribed nonzero coordinate forces the corresponding scalar to be one.
Thus the projection is the identity. No irreducibility of the sum is used.

This is an unbounded-norm approximation theorem for one vector in each
representation. It does not assert self-adjoint interpolation, a norm budget,
or the full weak-operator closure theorem with arbitrary finite vector tests.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra ENNReal lp

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

open MathlibAnnex.Analysis.InnerProductSpace

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]

private def simultaneousContinuousMap
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (pi : NonUnitalCStarRepresentation A G) : A →L[ℂ] (G →L[ℂ] G) :=
  LinearMap.mkContinuous
    { toFun := pi, map_add' := map_add pi, map_smul' := map_smul pi }
    1 (fun a => by
      change ‖pi a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le pi a)

/-- Normalizing a nonzero vector removes the unit-vector premise from the
previously constructed original-algebra fixed-vector theorem. -/
theorem exists_norm_eq_one_apply_eq_self_of_ne_zero
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    {x : H} (hx : x ≠ 0) : ∃ a : A, ‖a‖ = 1 ∧ pi a x = x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnc : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  let r : ℂ := (‖x‖ : ℂ)⁻¹
  have hr : r ≠ 0 := inv_ne_zero hnc
  have hunit : ‖r • x‖ = 1 := by
    simp only [r, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ hn]
  obtain ⟨a, ha, hax⟩ := exists_norm_eq_one_and_apply_eq_of_isIrreducible
    pi hpi (r • x) (r • x) hunit hunit
  refine ⟨a, ha, ?_⟩
  have hscaled : r • (pi a x - x) = 0 := by
    rw [smul_sub]
    apply sub_eq_zero.mpr
    simpa only [map_smul] using hax
  exact sub_eq_zero.mp ((smul_eq_zero.mp hscaled).resolve_left hr)

variable {I : Type v} {H : I → Type w}
variable [Fintype I] [DecidableEq I]
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- Dense simultaneous original-algebra orbit, without a norm bound on the
approximating elements. The empty index type is allowed. -/
theorem denseRange_atomicOrbit_of_pairwise_not_unitaryEquivalent
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i j, i ≠ j → ¬ (pi i).UnitaryEquivalent (pi j))
    (x : HilbertSum H) (hx : ∀ i, x i ≠ 0) :
    DenseRange (fun a : A =>
      atomicRepresentation (fun i => (pi i).unitization) (Unitization.inr a) x) := by
  classical
  let rho := atomicRepresentation (fun i => (pi i).unitization)
  let sigma : NonUnitalCStarRepresentation A (HilbertSum H) :=
    rho.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  let L : A →L[ℂ] HilbertSum H :=
    (ContinuousLinearMap.apply ℂ (HilbertSum H) x).comp
      (simultaneousContinuousMap sigma)
  let M : Submodule ℂ (HilbertSum H) := (LinearMap.range L.toLinearMap).topologicalClosure
  letI : IsClosed (M : Set (HilbertSum H)) :=
    (LinearMap.range L.toLinearMap).isClosed_topologicalClosure
  letI : CompleteSpace M := inferInstance
  letI : M.HasOrthogonalProjection := inferInstance
  have hinvA (a : A) (y : HilbertSum H) (hy : y ∈ M) : sigma a y ∈ M := by
    change y ∈ closure (LinearMap.range L.toLinearMap) at hy
    change sigma a y ∈ closure (LinearMap.range L.toLinearMap)
    apply (show Set.MapsTo (sigma a) (LinearMap.range L.toLinearMap)
        (LinearMap.range L.toLinearMap) from ?_).closure (sigma a).continuous hy
    rintro _ ⟨b, rfl⟩
    refine ⟨a * b, ?_⟩
    change sigma (a * b) x = sigma a (sigma b x)
    exact congrArg (fun T : HilbertSum H →L[ℂ] HilbertSum H => T x) (map_mul sigma a b)
  have hinv (z : Unitization ℂ A) (y : HilbertSum H) (hy : y ∈ M) : rho z y ∈ M := by
    induction z using Unitization.ind with
    | inl_add_inr c a =>
      have hinl : rho (Unitization.inl c) y = c • y := by
        change rho (algebraMap ℂ (Unitization ℂ A) c) y = c • y
        simpa only [StarAlgHom.coe_toAlgHom, ContinuousLinearMap.algebraMap_apply] using
          congrArg (fun T : HilbertSum H →L[ℂ] HilbertSum H => T y) (rho.commutes c)
      rw [map_add, ContinuousLinearMap.add_apply, hinl]
      exact M.add_mem (M.smul_mem c hy) (hinvA a y hy)
  have hred : _root_.StarAlgHom.IsReducing rho M := by
    intro z
    constructor
    · intro y hy
      exact hinv z y hy
    · intro y hy
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
      exact hinv (star z) y hy
  let P : HilbertSum H →L[ℂ] HilbertSum H := M.starProjection
  have hPcomm : _root_.StarAlgHom.InCommutant rho P := by
    intro z
    change P.comp (rho z) = (rho z).comp P
    exact Submodule.Reduces.starProjection_commute (hred z)
  obtain ⟨c, _, hPc⟩ :=
    exists_forall_apply_eq_smul_of_atomic_inCommutant pi hirr hne P hPcomm
  have hPorbit (a : A) : P (L a) = L a := by
    apply M.starProjection_eq_self_iff.mpr
    exact (LinearMap.range L.toLinearMap).le_topologicalClosure
      (LinearMap.mem_range_self L.toLinearMap a)
  have hc (i : I) : c i = 1 := by
    obtain ⟨a, _, hax⟩ := exists_norm_eq_one_apply_eq_self_of_ne_zero (pi i) (hirr i) (hx i)
    have hcoord : (L a) i = x i := by
      change (pi i).unitization (Unitization.inr a) (x i) = x i
      simpa only [unitization_inr] using hax
    have h := congrArg (fun y : HilbertSum H => y i) (hPorbit a)
    rw [hPc, hcoord] at h
    exact smul_left_injective ℂ (hx i) (h.trans (one_smul ℂ (x i)).symm)
  have hPone : P = 1 := by
    apply ContinuousLinearMap.ext
    intro y
    apply lp.ext
    funext i
    change P y i = y i
    rw [hPc, hc, one_smul]
  have hMtop : M = ⊤ := by
    rw [← M.range_starProjection, show M.starProjection = 1 from hPone]
    exact LinearMap.range_eq_top.mpr fun y => ⟨y, rfl⟩
  change Dense (Set.range L)
  rw [show Set.range L = (LinearMap.range L.toLinearMap : Set (HilbertSum H)) by
    ext y
    rfl]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hMtop

/-- One original-algebra element approximates a target vector in every
inequivalent fiber. No quantitative algebra-norm bound is asserted. -/
theorem exists_forall_apply_sub_norm_lt_of_pairwise_not_unitaryEquivalent
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i j, i ≠ j → ¬ (pi i).UnitaryEquivalent (pi j))
    (x y : HilbertSum H) (hx : ∀ i, x i ≠ 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ a : A, ∀ i, ‖pi i a (x i) - y i‖ < epsilon := by
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.mp
    (denseRange_atomicOrbit_of_pairwise_not_unitaryEquivalent pi hirr hne x hx)
    y epsilon hepsilon
  have herr : ‖atomicRepresentation (fun i => (pi i).unitization)
      (Unitization.inr a) x - y‖ < epsilon := by
    simpa only [dist_eq_norm, norm_sub_rev] using ha
  refine ⟨a, fun i => ?_⟩
  have hcoord := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (atomicRepresentation (fun i => (pi i).unitization) (Unitization.inr a) x - y) i
  change ‖atomicRepresentation (fun i => (pi i).unitization)
    (Unitization.inr a) x i - y i‖ ≤ _ at hcoord
  exact (show ‖pi i a (x i) - y i‖ ≤
    ‖atomicRepresentation (fun i => (pi i).unitization) (Unitization.inr a) x - y‖ from by
      simpa only [atomicRepresentation_apply, unitization_inr] using hcoord).trans_lt herr

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
