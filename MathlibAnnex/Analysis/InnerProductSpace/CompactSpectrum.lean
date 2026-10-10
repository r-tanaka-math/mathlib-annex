/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Topology.DiscreteSubset

/-! # Compact self-adjoint spectral lemmas
The selected and prescribed isolation statements share the same
orthogonal-complement argument. Eigenspace membership is converted explicitly
to an action equation before transport between a subspace and the ambient
space. No finite-dimensional or nontrivial ambient-space hypothesis is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Set Metric Module Module.End
open scoped CStarAlgebra ComplexConjugate Topology

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- A nonzero compact self-adjoint operator has a nonzero eigenvalue. -/
theorem exists_nonzero_eigenvalue_of_isCompactOperator_of_isSelfAdjoint
    (T : H →L[ℂ] H) (hTcompact : IsCompactOperator T)
    (hTself : T.IsSymmetric) (hT0 : T ≠ 0) :
    ∃ μ : ℂ, μ ≠ 0 ∧ HasEigenvalue (T : Module.End ℂ H) μ := by
  by_contra h
  push_neg at h
  have hz : T = 0 :=
    (ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero
      (T := T) hTcompact hTself).1
      (fun μ hμ => by
        by_contra hμ0
        exact h μ hμ0 hμ)
  exact hT0 hz

/-- The orthogonal-complement restriction has no copy of the selected
eigenvalue. -/
theorem not_hasEigenvalue_restrict_orthogonalComplement_eigenspace
    (T : H →L[ℂ] H) (hTself : T.IsSymmetric) {μ : ℂ}
    (hμ : HasEigenvalue (T : Module.End ℂ H) μ) :
    let E := Module.End.eigenspace T.toLinearMap μ
    let R : Eᗮ →L[ℂ] Eᗮ :=
      T.restrict (hTself.invariant_orthogonalComplement_eigenspace μ)
    ¬ HasEigenvalue (R : Module.End ℂ Eᗮ) μ := by
  dsimp
  intro hR
  obtain ⟨y, hy, hy0⟩ := hR.exists_hasEigenvector
  have hyE : (y : H) ∈ Module.End.eigenspace T.toLinearMap μ := by
    rw [Module.End.mem_eigenspace_iff]
    have hyAction := Module.End.mem_eigenspace_iff.mp hy
    exact congrArg Subtype.val hyAction
  have hyperp : (y : H) ∈ (Module.End.eigenspace T.toLinearMap μ)ᗮ := y.property
  have hzero : (y : H) = 0 := by
    exact inner_self_eq_zero.mp (hyperp (y : H) hyE)
  exact hy0 (Subtype.ext hzero)

/-- A selected nonzero eigenvalue of a compact self-adjoint operator is
isolated from the remaining spectrum by a positive metric radius. -/
theorem exists_isolated_nonzero_eigenvalue
    (T : H →L[ℂ] H) (hTcompact : IsCompactOperator T)
    (hTself : T.IsSymmetric) (hT0 : T ≠ 0) :
    ∃ (μ : ℂ) (r : ℝ),
      μ ≠ 0 ∧ 0 < r ∧ r < ‖μ‖ ∧
      HasEigenvalue (T : Module.End ℂ H) μ ∧
      ∀ z ∈ spectrum ℂ T, z ≠ μ → r ≤ dist z μ := by
  obtain ⟨μ, hμ0, hμ⟩ :=
    T.exists_nonzero_eigenvalue_of_isCompactOperator_of_isSelfAdjoint
      hTcompact hTself hT0
  let E := Module.End.eigenspace T.toLinearMap μ
  let R : Eᗮ →L[ℂ] Eᗮ :=
    T.restrict (hTself.invariant_orthogonalComplement_eigenspace μ)
  have hRcompact : IsCompactOperator R :=
    hTcompact.restrict' (hTself.invariant_orthogonalComplement_eigenspace μ)
  have hRno : ¬ HasEigenvalue (R : Module.End ℂ Eᗮ) μ :=
    T.not_hasEigenvalue_restrict_orthogonalComplement_eigenspace hTself hμ
  have hμres : μ ∈ resolventSet ℂ R :=
    (hRcompact.hasEigenvalue_or_mem_resolventSet hμ0).resolve_left hRno
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.1 (spectrum.isOpen_resolventSet R) μ hμres
  let r : ℝ := min (δ / 2) (‖μ‖ / 2)
  have hr : 0 < r := by
    exact lt_min (half_pos hδ) (half_pos (norm_pos_iff.mpr hμ0))
  have hrμ : r < ‖μ‖ :=
    (min_le_right _ _).trans_lt (half_lt_self (norm_pos_iff.mpr hμ0))
  refine ⟨μ, r, hμ0, hr, hrμ, hμ, ?_⟩
  intro z hzspec hzμ
  by_cases hz0 : z = 0
  · subst z
    simpa [dist_zero_left] using hrμ.le
  have hzEig : HasEigenvalue (T : Module.End ℂ H) z :=
    (hTcompact.hasEigenvalue_iff_mem_spectrum hz0).2 hzspec
  by_contra! hzr
  have hzδhalf : dist z μ < δ / 2 :=
    lt_of_lt_of_le hzr (show r ≤ δ / 2 from min_le_left _ _)
  have hzδ : dist z μ < δ := hzδhalf.trans (half_lt_self hδ)
  obtain ⟨x, hx, hx0⟩ := hzEig.exists_hasEigenvector
  have hxperp : x ∈ Eᗮ := by
    intro y hy
    exact hTself.orthogonalFamily_eigenspaces hzμ.symm
      ⟨y, hy⟩ ⟨x, hx⟩
  have hzR : HasEigenvalue (R : Module.End ℂ Eᗮ) z := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
      (x := (⟨x, hxperp⟩ : Eᗮ))
    refine ⟨?_, ?_⟩
    · apply Module.End.mem_eigenspace_iff.mpr
      apply Subtype.ext
      exact Module.End.mem_eigenspace_iff.mp hx
    · exact fun h => hx0 (congrArg Subtype.val h)
  have hzRspec : z ∈ spectrum ℂ R :=
    (hRcompact.hasEigenvalue_iff_mem_spectrum hz0).1 hzR
  have hzRres : z ∈ resolventSet ℂ R := hball (by simpa [mem_ball] using hzδ)
  exact hzRspec hzRres

/-- A prescribed nonzero eigenvalue of a compact self-adjoint operator is
isolated from the rest of its spectrum.  This is the pointwise form of the
existing selected-eigenvalue lemma and is needed to isolate all spectral
points outside a fixed neighbourhood of zero simultaneously. -/
theorem exists_isolated_spectrum_radius_of_hasEigenvalue
    (T : H →L[ℂ] H) (hTcompact : IsCompactOperator T)
    (hTself : T.IsSymmetric) {μ : ℂ} (hμ0 : μ ≠ 0)
    (hμ : HasEigenvalue (T : Module.End ℂ H) μ) :
    ∃ r : ℝ, 0 < r ∧ r < ‖μ‖ ∧
      ∀ z ∈ spectrum ℂ T, z ≠ μ → r ≤ dist z μ := by
  let E := Module.End.eigenspace T.toLinearMap μ
  let R : Eᗮ →L[ℂ] Eᗮ :=
    T.restrict (hTself.invariant_orthogonalComplement_eigenspace μ)
  have hRcompact : IsCompactOperator R :=
    hTcompact.restrict' (hTself.invariant_orthogonalComplement_eigenspace μ)
  have hRno : ¬ HasEigenvalue (R : Module.End ℂ Eᗮ) μ :=
    T.not_hasEigenvalue_restrict_orthogonalComplement_eigenspace hTself hμ
  have hμres : μ ∈ resolventSet ℂ R :=
    (hRcompact.hasEigenvalue_or_mem_resolventSet hμ0).resolve_left hRno
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.1 (spectrum.isOpen_resolventSet R) μ hμres
  let r : ℝ := min (δ / 2) (‖μ‖ / 2)
  have hr : 0 < r :=
    lt_min (half_pos hδ) (half_pos (norm_pos_iff.mpr hμ0))
  have hrμ : r < ‖μ‖ :=
    (min_le_right _ _).trans_lt (half_lt_self (norm_pos_iff.mpr hμ0))
  refine ⟨r, hr, hrμ, ?_⟩
  intro z hzspec hzμ
  by_cases hz0 : z = 0
  · subst z
    simpa [dist_zero_left] using hrμ.le
  have hzEig : HasEigenvalue (T : Module.End ℂ H) z :=
    (hTcompact.hasEigenvalue_iff_mem_spectrum hz0).2 hzspec
  by_contra! hzr
  have hzδhalf : dist z μ < δ / 2 :=
    lt_of_lt_of_le hzr (show r ≤ δ / 2 from min_le_left _ _)
  have hzδ : dist z μ < δ := hzδhalf.trans (half_lt_self hδ)
  obtain ⟨x, hx, hx0⟩ := hzEig.exists_hasEigenvector
  have hxperp : x ∈ Eᗮ := by
    intro y hy
    exact hTself.orthogonalFamily_eigenspaces hzμ.symm
      ⟨y, hy⟩ ⟨x, hx⟩
  have hzR : HasEigenvalue (R : Module.End ℂ Eᗮ) z := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
      (x := (⟨x, hxperp⟩ : Eᗮ))
    refine ⟨?_, ?_⟩
    · apply Module.End.mem_eigenspace_iff.mpr
      apply Subtype.ext
      exact Module.End.mem_eigenspace_iff.mp hx
    · exact fun h => hx0 (congrArg Subtype.val h)
  have hzRspec : z ∈ spectrum ℂ R :=
    (hRcompact.hasEigenvalue_iff_mem_spectrum hz0).1 hzR
  have hzRres : z ∈ resolventSet ℂ R :=
    hball (by simpa [mem_ball] using hzδ)
  exact hzRspec hzRres

/-- The nonzero spectrum of a compact self-adjoint operator is discrete. -/
theorem isDiscrete_spectrum_sdiff_zero
    (T : H →L[ℂ] H) (hTcompact : IsCompactOperator T)
    (hTself : T.IsSymmetric) :
    IsDiscrete (spectrum ℂ T \ {0}) := by
  rw [isDiscrete_iff_forall_exists_isOpen]
  intro μ hμ
  have hμspec : μ ∈ spectrum ℂ T := hμ.1
  have hμ0 : μ ≠ 0 := by
    simpa only [Set.mem_singleton_iff] using hμ.2
  have hμEig : HasEigenvalue (T : Module.End ℂ H) μ :=
    (hTcompact.hasEigenvalue_iff_mem_spectrum hμ0).2 hμspec
  obtain ⟨r, hr, -, hiso⟩ :=
    T.exists_isolated_spectrum_radius_of_hasEigenvalue
      hTcompact hTself hμ0 hμEig
  refine ⟨Metric.ball μ r, Metric.isOpen_ball, ?_⟩
  ext z
  constructor
  · rintro ⟨hzball, hzspec, -⟩
    by_contra hzμmem
    have hzμ : z ≠ μ := by
      simpa only [Set.mem_singleton_iff] using hzμmem
    have := hiso z hzspec hzμ
    exact (not_lt_of_ge this) (by simpa [mem_ball] using hzball)
  · intro hz
    have hzμ : z = μ := by
      simpa only [Set.mem_singleton_iff] using hz
    subst z
    exact ⟨Metric.mem_ball_self hr, hμspec, hμ.2⟩

/-- Only finitely many spectral points of a compact self-adjoint operator have
norm bounded below by a fixed positive number. -/
theorem finite_spectrum_norm_ge
    (T : H →L[ℂ] H) (hTcompact : IsCompactOperator T)
    (hTself : T.IsSymmetric) {δ : ℝ} (hδ : 0 < δ) :
    {z : ℂ | z ∈ spectrum ℂ T ∧ δ ≤ ‖z‖}.Finite := by
  let K : Set ℂ := {z : ℂ | δ ≤ ‖z‖}
  have hKclosed : IsClosed K :=
    isClosed_le continuous_const continuous_norm
  have hcompact : IsCompact (spectrum ℂ T ∩ K) :=
    (spectrum.isCompact (𝕜 := ℂ) T).inter_right hKclosed
  have hsubset : spectrum ℂ T ∩ K ⊆ spectrum ℂ T \ {0} := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    intro hz0
    rw [Set.mem_singleton_iff] at hz0
    subst z
    have hzle : δ ≤ 0 := by simpa only [K, Set.mem_setOf_eq, norm_zero] using hz.2
    exact (not_le_of_gt hδ) hzle
  have hdisc : IsDiscrete (spectrum ℂ T ∩ K) :=
    (T.isDiscrete_spectrum_sdiff_zero hTcompact hTself).mono hsubset
  have hfinite : (spectrum ℂ T ∩ K).Finite := hcompact.finite hdisc
  change (spectrum ℂ T ∩ K).Finite
  exact hfinite


end ContinuousLinearMap
