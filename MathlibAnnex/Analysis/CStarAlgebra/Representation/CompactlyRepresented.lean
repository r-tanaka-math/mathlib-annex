/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.SimultaneousClipping
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorIdeal
import MathlibAnnex.Analysis.InnerProductSpace.CompactSpectrum
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Finite-rank spectral projections in faithfully compact representations

A faithful representation whose every represented operator is compact contains
actual finite-rank projections.  The point which requires proof is membership in
the represented algebra: an ambient finite-rank approximation is not enough.

For a nonzero positive represented compact operator we choose a nonzero
eigenvalue, isolate it by restricting to the orthogonal complement of its
eigenspace and using the Fredholm alternative, and apply a zero-preserving
continuous functional calculus cutoff.  The resulting element is a nonzero star
projection in the original nonunital C-star algebra.  Its represented range is
contained in the finite-dimensional eigenspace.

No separability, countable basis, unitality, irreducibility, or pre-existing
rank-one element is assumed.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Set Metric Module Module.End
open scoped CStarAlgebra ComplexConjugate Topology

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A faithful representation is compactly represented when every represented
operator is compact in the original operator norm.  This is deliberately weaker
than `IsCompactOperatorModel`: no surjectivity onto all compact operators is
part of the definition. -/
def NonUnitalCStarRepresentation.IsCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H) : Prop :=
  Function.Injective pi ∧ ∀ a : A, IsCompactOperator (pi a)

namespace NonUnitalCStarRepresentation

/-- The normal-element version of the existing self-adjoint transport lemma. -/
theorem map_cfcₙ_eq_cfc_normal
    (pi : NonUnitalCStarRepresentation A H) (a : A) (ha : IsStarNormal a)
    (f : ℂ → ℂ) (hf : Continuous f) (hf0 : f 0 = 0) :
    pi (cfcₙ f a) = cfc f (pi a) := by
  rw [pi.map_cfcₙ f a hf.continuousOn hf0 (by fun_prop) ha (ha.map pi),
    cfcₙ_eq_cfc hf.continuousOn hf0]

end NonUnitalCStarRepresentation


/-- Radial peak used to isolate one nonzero point of a compact-operator
spectrum.  It is one at `μ`, vanishes outside the open `r`-ball, and is
zero at the origin when `r < ‖μ‖`. -/
def compactSpectralPeak (μ : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  ((max 0 (1 - ‖z - μ‖ / r) : ℝ) : ℂ)

namespace compactSpectralPeak

variable {μ z : ℂ} {r : ℝ}

theorem continuous (hr : 0 < r) : Continuous (compactSpectralPeak μ r) := by
  unfold compactSpectralPeak
  fun_prop

@[simp]
theorem apply_center (hr : r ≠ 0) : compactSpectralPeak μ r μ = 1 := by
  simp [compactSpectralPeak, hr]

@[simp]
theorem apply_zero (hr : 0 < r) (hrμ : r ≤ ‖μ‖) :
    compactSpectralPeak μ r 0 = 0 := by
  have hdiv : 1 ≤ ‖μ‖ / r := (le_div_iff₀ hr).2 (by simpa only [one_mul] using hrμ)
  simp [compactSpectralPeak, norm_neg, max_eq_left, sub_nonpos.mpr hdiv]

@[simp]
theorem apply_eq_zero_of_le_dist (hr : 0 < r) (h : r ≤ dist z μ) :
    compactSpectralPeak μ r z = 0 := by
  have hdiv : 1 ≤ ‖z - μ‖ / r := by
    rw [dist_eq_norm] at h
    exact (le_div_iff₀ hr).2 (by simpa only [one_mul] using h)
  simp [compactSpectralPeak, max_eq_left, sub_nonpos.mpr hdiv]

@[simp]
theorem apply_eq_zero_or_one_on_isolated_spectrum
    {T : H →L[ℂ] H} (hr : 0 < r) (hμ : μ ∈ spectrum ℂ T)
    (hiso : ∀ z ∈ spectrum ℂ T, z ≠ μ → r ≤ dist z μ)
    {z : ℂ} (hz : z ∈ spectrum ℂ T) :
    compactSpectralPeak μ r z = 0 ∨ compactSpectralPeak μ r z = 1 := by
  by_cases h : z = μ
  · subst z
    exact Or.inr (apply_center hr.ne')
  · exact Or.inl (apply_eq_zero_of_le_dist hr (hiso z hz h))

end compactSpectralPeak

namespace NonUnitalCStarRepresentation

/-- The isolated compact spectral projection in the source algebra. -/
def compactSpectralProjection
    (pi : NonUnitalCStarRepresentation A H) (a : A) (μ : ℂ) (r : ℝ) : A :=
  cfcₙ (compactSpectralPeak μ r) a

/-- Functional calculus for the compact spectral peak is transported through
the given representation without changing the selected operator. -/
theorem compactSpectralProjection_apply
    (pi : NonUnitalCStarRepresentation A H) (a : A) (ha : IsStarNormal a)
    (μ : ℂ) {r : ℝ} (hr : 0 < r) (hrμ : r ≤ ‖μ‖) :
    pi (pi.compactSpectralProjection a μ r) =
      cfc (compactSpectralPeak μ r) (pi a) := by
  exact pi.map_cfcₙ_eq_cfc_normal a ha _
    (compactSpectralPeak.continuous hr)
    (compactSpectralPeak.apply_zero hr hrμ)

/-- The represented peak is an actual nonzero finite-rank star projection. -/
theorem exists_nonzero_finite_rank_spectral_projection
    (pi : NonUnitalCStarRepresentation A H) (hpi : Function.Injective pi)
    (a : A) (ha : 0 ≤ a) (ha0 : a ≠ 0)
    (hcompact : IsCompactOperator (pi a)) :
    ∃ p : A,
      IsStarProjection p ∧ p ≠ 0 ∧
      FiniteDimensional ℂ (LinearMap.range (pi p).toLinearMap) ∧
      ∃ (μ : ℂ) (r : ℝ),
        μ ≠ 0 ∧ 0 < r ∧ r < ‖μ‖ ∧
        HasEigenvalue ((pi a) : Module.End ℂ H) μ ∧
        pi p = cfc (compactSpectralPeak μ r) (pi a) ∧
        (pi a) * (pi p) = μ • (pi p) := by
  have haSelf : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha
  have hTSelf : (pi a).IsSymmetric := (haSelf.map pi).isSymmetric
  have hT0 : pi a ≠ 0 := fun h => ha0 (hpi (by simpa using h))
  obtain ⟨μ, r, hμ0, hr, hrμ, hμEig, hiso⟩ :=
    (pi a).exists_isolated_nonzero_eigenvalue hcompact hTSelf hT0
  let f : ℂ → ℂ := compactSpectralPeak μ r
  let p : A := pi.compactSpectralProjection a μ r
  let q : H →L[ℂ] H := cfc f (pi a)
  have hμspec : μ ∈ spectrum ℂ (pi a) :=
    (hcompact.hasEigenvalue_iff_mem_spectrum hμ0).1 hμEig
  have hf : Continuous f := compactSpectralPeak.continuous hr
  have hf0 : f 0 = 0 := compactSpectralPeak.apply_zero hr hrμ.le
  have hmap : pi p = q := by
    exact pi.compactSpectralProjection_apply a haSelf.isStarNormal μ hr hrμ.le
  have hqIdem : IsIdempotentElem q := by
    rw [IsIdempotentElem]
    change q * q = q
    rw [show q * q = cfc (fun z => f z * f z) (pi a) by
      exact (cfc_mul f f (pi a) hf.continuousOn hf.continuousOn).symm]
    apply cfc_congr
    intro z hz
    rcases compactSpectralPeak.apply_eq_zero_or_one_on_isolated_spectrum
      hr hμspec hiso hz with hz0 | hz1
    · simp [f, hz0]
    · simp [f, hz1]
  have hqNormal : IsStarNormal q :=
    cfc_predicate f (pi a)
  have hqProj : IsStarProjection q :=
    isStarProjection_iff_isIdempotentElem_and_isStarNormal.mpr ⟨hqIdem, hqNormal⟩
  have hpIdem : IsIdempotentElem p := by
    rw [IsIdempotentElem]
    apply hpi
    rw [map_mul, hmap, hqIdem.eq]
  have hpNormal : IsStarNormal p := by
    exact cfcₙ_predicate f a
  have hpProj : IsStarProjection p :=
    isStarProjection_iff_isIdempotentElem_and_isStarNormal.mpr ⟨hpIdem, hpNormal⟩
  have hq0 : q ≠ 0 := by
    intro hq
    have h1 : (1 : ℂ) ∈ spectrum ℂ q := by
      rw [cfc_map_spectrum f (pi a) (haSelf.map pi).isStarNormal hf.continuousOn]
      exact ⟨μ, hμspec, compactSpectralPeak.apply_center hr.ne'⟩
    obtain ⟨x, _, hx0⟩ :=
      ((hcompact.hasEigenvalue_iff_mem_spectrum hμ0).2 hμspec).exists_hasEigenvector
    letI : Nontrivial H := ⟨⟨x, 0, hx0⟩⟩
    rw [hq, CFC.spectrum_zero_eq (R := ℂ)] at h1
    exact one_ne_zero (Set.mem_singleton_iff.mp h1)
  have hp0 : p ≠ 0 := fun hp => hq0 (by rw [← hmap, hp, map_zero])
  have hTq : (pi a) * q = μ • q := by
    calc
      (pi a) * q = cfc (fun z : ℂ => z * f z) (pi a) := by
        have hmul := cfc_mul (fun z : ℂ => z) f (pi a)
          continuousOn_id hf.continuousOn
        rw [cfc_id' ℂ (pi a) (haSelf.map pi).isStarNormal] at hmul
        exact hmul.symm
      _ = cfc (fun z : ℂ => μ * f z) (pi a) := by
        apply cfc_congr
        intro z hz
        rcases compactSpectralPeak.apply_eq_zero_or_one_on_isolated_spectrum
          hr hμspec hiso hz with hz0 | hz1
        · simp [f, hz0]
        · have hzμ : z = μ := by
            by_contra h
            have := compactSpectralPeak.apply_eq_zero_of_le_dist hr (hiso z hz h)
            exact one_ne_zero (hz1.symm.trans this)
          simp [hzμ, hz1]
      _ = μ • q := by
        simpa [q] using cfc_smul μ f (pi a) hf.continuousOn
  have hrange : LinearMap.range q.toLinearMap ≤
      Module.End.eigenspace (pi a).toLinearMap μ := by
    rintro y ⟨x, rfl⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa [ContinuousLinearMap.mul_apply] using congrArg (fun T : H →L[ℂ] H => T x) hTq
  haveI : FiniteDimensional ℂ
      (Module.End.eigenspace (pi a).toLinearMap μ) :=
    ContinuousLinearMap.finite_dimensional_eigenspace hcompact μ hμ0
  have hfinite : FiniteDimensional ℂ (LinearMap.range q.toLinearMap) :=
    Submodule.finiteDimensional_of_le hrange
  have hfinite' : FiniteDimensional ℂ (LinearMap.range (pi p).toLinearMap) := by
    rw [hmap]
    exact hfinite
  exact ⟨p, hpProj, hp0, hfinite', μ, r, hμ0, hr, hrμ, hμEig, hmap,
    by simpa only [hmap] using hTq⟩

/-- The compact-representation hypothesis supplies the preceding projection
for every nonzero positive source element. -/
theorem exists_nonzero_finite_rank_projection_of_isCompactlyRepresented
    (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsCompactlyRepresented)
    (a : A) (ha : 0 ≤ a) (ha0 : a ≠ 0) :
    ∃ p : A, IsStarProjection p ∧ p ≠ 0 ∧
      FiniteDimensional ℂ (LinearMap.range (pi p).toLinearMap) := by
  obtain ⟨p, hp, hp0, hfin, -⟩ :=
    pi.exists_nonzero_finite_rank_spectral_projection hpi.1 a ha ha0 (hpi.2 a)
  exact ⟨p, hp, hp0, hfin⟩

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
