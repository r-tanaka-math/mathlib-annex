/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.CyclicRestriction

/-!
# Norm-preserving coefficients on the original cyclic subspace

Project both vectors onto the closure of the original-algebra source orbit.
This preserves the coefficient. If the original vectors have norm at most
one and the coefficient has norm one, the projected vectors both have norm
one. In fact, both original vectors already belong to this subspace.
No extremality or irreducibility is used here.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Compression to the original cyclic subspace preserves the full coefficient. -/
theorem matrixCoefficient_cyclicRestriction (pi : NonUnitalCStarRepresentation A H)
    (x y : H) :
    matrixCoefficient (cyclicRestriction pi x)
      ((cyclicSubspace pi x).orthogonalProjectionOnto x)
      ((cyclicSubspace pi x).orthogonalProjectionOnto y) = matrixCoefficient pi x y := by
  apply ContinuousLinearMap.ext
  intro a
  change inner ℂ ((cyclicSubspace pi x).starProjection y)
    (pi a ((cyclicSubspace pi x).starProjection x)) = inner ℂ y (pi a x)
  rw [apply_starProjection_cyclicSubspace]
  have h := (cyclicSubspace pi x).starProjection_inner_eq_zero y (pi a x)
    (apply_mem_cyclicSubspace pi x a)
  rw [inner_sub_left] at h
  exact (sub_eq_zero.mp h).symm

/-- A norm-one coefficient of contractions forces both compressed vectors to
have norm one, not just their product to be bounded above by one. -/
theorem norm_orthogonalProjectionOnto_cyclicSubspace_eq_one
    (pi : NonUnitalCStarRepresentation A H) (x y : H)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hn : ‖matrixCoefficient pi x y‖ = 1) :
    ‖(cyclicSubspace pi x).orthogonalProjectionOnto x‖ = 1 ∧
    ‖(cyclicSubspace pi x).orthogonalProjectionOnto y‖ = 1 := by
  let M := cyclicSubspace pi x
  let xM := M.orthogonalProjectionOnto x
  let yM := M.orthogonalProjectionOnto y
  have hp (z : H) : ‖M.orthogonalProjectionOnto z‖ ≤ ‖z‖ :=
    M.norm_orthogonalProjectionOnto_apply_le z
  have hxm : ‖xM‖ ≤ 1 := (hp x).trans hx
  have hym : ‖yM‖ ≤ 1 := (hp y).trans hy
  have hlower : 1 ≤ ‖xM‖ * ‖yM‖ := by
    have h := norm_matrixCoefficient_le (cyclicRestriction pi x) xM yM
    rw [matrixCoefficient_cyclicRestriction, hn] at h
    exact h
  have hleft : ‖xM‖ * ‖yM‖ ≤ ‖xM‖ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hym (norm_nonneg xM)
  have hright : ‖xM‖ * ‖yM‖ ≤ ‖yM‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hxm (norm_nonneg yM)
  exact ⟨le_antisymm hxm (hlower.trans hleft), le_antisymm hym (hlower.trans hright)⟩

/-- Both original vectors belong to the original-algebra cyclic subspace.
Thus unitization-only cyclicity or an unproved nondegeneracy assumption is
not being used to put either vector in the restriction space. -/
theorem mem_cyclicSubspace_of_norm_matrixCoefficient_eq_one
    (pi : NonUnitalCStarRepresentation A H) (x y : H)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hn : ‖matrixCoefficient pi x y‖ = 1) :
    x ∈ cyclicSubspace pi x ∧ y ∈ cyclicSubspace pi x := by
  obtain ⟨hpx, hpy⟩ := norm_orthogonalProjectionOnto_cyclicSubspace_eq_one pi x y hx hy hn
  let M := cyclicSubspace pi x
  have mem_of_norm (z : H) (hz : ‖z‖ ≤ 1)
      (hpz : ‖M.orthogonalProjectionOnto z‖ = 1) : z ∈ M := by
    have horth := Submodule.inner_right_of_mem_orthogonal (K := M)
      (M.starProjection_apply_mem z) (M.sub_starProjection_mem_orthogonal z)
    have hsq := norm_add_sq (𝕜 := ℂ) (M.starProjection z) (z - M.starProjection z)
    rw [show M.starProjection z + (z - M.starProjection z) = z by abel, horth] at hsq
    have hpz' : ‖M.starProjection z‖ = 1 := hpz
    rw [hpz'] at hsq
    have hzero : ‖z - M.starProjection z‖ = 0 := by
      norm_num at hsq
      nlinarith [norm_nonneg z, norm_nonneg (z - M.starProjection z)]
    exact M.starProjection_eq_self_iff.mp
      (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  exact ⟨mem_of_norm x hx hpx, mem_of_norm y hy hpy⟩

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
