/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.CompactRankOne
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Irreducible representations of the concrete compact operators

A nonzero representation cannot kill a unit rank-one projection: it would kill
all rank-one operators, finite-rank sums and, by norm approximation, all compacts.
A unit vector fixed by that projection image gives the actual corner map
`x ↦ rho (compactRankOne ℂ x e) xi`. The inner-product identity makes it an
isometry. Its nonzero closed reducing range is full by irreducibility.
No faithfulness, rank-one image projection, cyclicity or separability is assumed.
The two Hilbert universes are independent. Rank-one retains its actual convention
`rankOne 𝕜 x y z = inner 𝕜 y z • x`.
-/

set_option autoImplicit false
noncomputable section
open Set InnerProductSpace
open scoped InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : Type v} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

open NonUnitalCStarRepresentation

/-- A nonzero representation detects every unit rank-one projection.
Finite-rank norm approximation, not injectivity, is used. -/
theorem map_compactRankOne_self_ne_zero
    (rho : NonUnitalCStarRepresentation
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) L)
    (hrho : rho.IsNonzero) (e : H) (he : ‖e‖ = 1) :
    rho (compactRankOne ℂ e e) ≠ 0 := by
  classical
  intro hp
  have hee : inner ℂ e e = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, he]
    norm_num
  have hrank : ∀ x y : H, rho (compactRankOne ℂ x y) = 0 := by
    intro x y
    have hfac : compactRankOne ℂ x y =
        (compactRankOne ℂ x e * compactRankOne ℂ e e) * compactRankOne ℂ e y := by
      simp only [compactRankOne_mul, hee, one_smul]
    rw [hfac, map_mul, map_mul, hp, mul_zero, zero_mul]
  have hfinite : ∀ (F : H →L[ℂ] H)
      (hF : FiniteDimensional ℂ (LinearMap.range F.toLinearMap)),
      rho ⟨F, by letI := hF; exact F.isCompactOperator_of_finiteDimensional_range⟩ = 0 := by
    intro F hF
    letI := hF
    obtain ⟨n, x, y, hsum⟩ := F.exists_sum_rankOne_eq_of_finiteDimensional_range
    have hsum' : (∑ i : Fin n, compactRankOne ℂ (x i) (y i)) =
        ⟨F, F.isCompactOperator_of_finiteDimensional_range⟩ := by
      apply Subtype.ext
      change (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H).subtype
        (∑ i : Fin n, compactRankOne ℂ (x i) (y i)) = F
      rw [map_sum]
      exact hsum
    rw [← hsum', map_sum]
    simp only [hrank, Finset.sum_const_zero]
  obtain ⟨a, ha⟩ := hrho
  have hpos : 0 < ‖rho a‖ := norm_pos_iff.mpr ha
  obtain ⟨F, hF, hdist⟩ := a.property.exists_finiteDimensional_range_norm_sub_lt hpos
  let F' : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H :=
    ⟨F, by letI := hF; exact F.isCompactOperator_of_finiteDimensional_range⟩
  have hFzero : rho F' = 0 := hfinite F hF
  have hbound := NonUnitalStarAlgHom.norm_apply_le rho (a - F')
  rw [map_sub, hFzero, sub_zero] at hbound
  have hnorm : ‖a - F'‖ = ‖(a : H →L[ℂ] H) - F‖ := rfl
  rw [hnorm] at hbound
  exact (lt_of_le_of_lt hbound hdist).false

/-- A normalized fixed vector is constructed from a nonzero projection image.
No rank-one property of that image is assumed. -/
theorem exists_norm_eq_one_fixed_compactRankOne
    (rho : NonUnitalCStarRepresentation
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) L)
    (hrho : rho.IsNonzero) (e : H) (he : ‖e‖ = 1) :
    ∃ xi : L, ‖xi‖ = 1 ∧ rho (compactRankOne ℂ e e) xi = xi := by
  classical
  let p := compactRankOne ℂ e e
  have hp := map_compactRankOne_self_ne_zero rho hrho e he
  obtain ⟨z, hz⟩ : ∃ z : L, rho p z ≠ 0 := by
    by_contra! h
    apply hp
    ext z
    exact h z
  have hee : inner ℂ e e = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, he]
    norm_num
  have hpp : p * p = p := by simp only [p, compactRankOne_mul, hee, one_smul]
  have hfix : rho p (rho p z) = rho p z := by
    change (rho p * rho p) z = rho p z
    rw [← map_mul, hpp]
  let xi : L := (‖rho p z‖ : ℂ)⁻¹ • rho p z
  have hn : 0 < ‖rho p z‖ := norm_pos_iff.mpr hz
  refine ⟨xi, ?_, ?_⟩
  · simp only [xi, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  · change rho p ((‖rho p z‖ : ℂ)⁻¹ • rho p z) = _
    rw [map_smul, hfix]

/-- The actual rank-one corner intertwiner before its norm is proved. -/
def compactRepresentationIntertwiner
    (rho : NonUnitalCStarRepresentation
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) L)
    (e : H) (xi : L) : H →ₗ[ℂ] L where
  toFun x := rho (compactRankOne ℂ x e) xi
  map_add' x y := by
    simp only [compactRankOne_add_left, map_add, ContinuousLinearMap.add_apply]
  map_smul' c x := by
    simp only [compactRankOne_smul_left, map_smul, ContinuousLinearMap.smul_apply,
      RingHom.id_apply]

@[simp]
theorem compactRepresentationIntertwiner_apply
    (rho : NonUnitalCStarRepresentation
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) L)
    (e : H) (xi : L) (x : H) :
    compactRepresentationIntertwiner rho e xi x = rho (compactRankOne ℂ x e) xi := rfl

/-- Exact inner-product identity, using the unit fixed vector. -/
theorem inner_compactRepresentationIntertwiner
    (rho : NonUnitalCStarRepresentation
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) L)
    (e : H) (xi : L) (hxi : ‖xi‖ = 1)
    (hfix : rho (compactRankOne ℂ e e) xi = xi) (x y : H) :
    inner ℂ (compactRepresentationIntertwiner rho e xi x)
      (compactRepresentationIntertwiner rho e xi y) = inner ℂ x y := by
  change inner ℂ (rho (compactRankOne ℂ x e) xi)
    (rho (compactRankOne ℂ y e) xi) = _
  calc
    _ = inner ℂ xi ((rho (compactRankOne ℂ x e)).adjoint
        (rho (compactRankOne ℂ y e) xi)) :=
      (ContinuousLinearMap.adjoint_inner_right _ xi _).symm
    _ = inner ℂ xi (rho (star (compactRankOne ℂ x e) * compactRankOne ℂ y e) xi) := by
      simp only [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.mul_apply]
    _ = inner ℂ xi (inner ℂ x y • xi) := by
      rw [star_compactRankOne, compactRankOne_mul, map_smul,
        ContinuousLinearMap.smul_apply, hfix]
    _ = inner ℂ x y := by
      rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hxi]
      simp

/-- The same corner map as a genuine linear isometry. -/
def compactRepresentationIsometry
    (rho : NonUnitalCStarRepresentation
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) L)
    (e : H) (xi : L) (hxi : ‖xi‖ = 1)
    (hfix : rho (compactRankOne ℂ e e) xi = xi) : H →ₗᵢ[ℂ] L :=
  (compactRepresentationIntertwiner rho e xi).isometryOfInner
    (inner_compactRepresentationIntertwiner rho e xi hxi hfix)

@[simp]
theorem compactRepresentationIsometry_apply
    (rho : NonUnitalCStarRepresentation
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) L)
    (e : H) (xi : L) (hxi : ‖xi‖ = 1)
    (hfix : rho (compactRankOne ℂ e e) xi = xi) (x : H) :
    compactRepresentationIsometry rho e xi hxi hfix x =
      rho (compactRankOne ℂ x e) xi := rfl

/-- Intertwining holds directly for every compact operator. -/
theorem compactRepresentationIsometry_intertwines
    (rho : NonUnitalCStarRepresentation
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) L)
    (e : H) (xi : L) (hxi : ‖xi‖ = 1)
    (hfix : rho (compactRankOne ℂ e e) xi = xi)
    (a : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) (x : H) :
    compactRepresentationIsometry rho e xi hxi hfix ((a : H →L[ℂ] H) x) =
      rho a (compactRepresentationIsometry rho e xi hxi hfix x) := by
  change rho (compactRankOne ℂ ((a : H →L[ℂ] H) x) e) xi =
    rho a (rho (compactRankOne ℂ x e) xi)
  rw [← mul_compactRankOne, map_mul]
  rfl

/-- Completeness makes the isometric range closed; star compatibility makes
its invariance reducing. -/
theorem reduces_range_compactRepresentationIsometry
    (rho : NonUnitalCStarRepresentation
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) L)
    (e : H) (xi : L) (hxi : ‖xi‖ = 1)
    (hfix : rho (compactRankOne ℂ e e) xi = xi) :
    rho.Reduces (compactRepresentationIsometry rho e xi hxi hfix).toLinearMap.range := by
  let U := compactRepresentationIsometry rho e xi hxi hfix
  refine ⟨U.isometry.isClosedEmbedding.isClosed_range, ?_⟩
  intro a z hz
  obtain ⟨x, rfl⟩ := hz
  refine ⟨⟨(a : H →L[ℂ] H) x,
    compactRepresentationIsometry_intertwines rho e xi hxi hfix a x⟩, ?_⟩
  refine ⟨((star a : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) : H →L[ℂ] H) x, ?_⟩
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  exact compactRepresentationIsometry_intertwines rho e xi hxi hfix (star a) x

/-- Irreducibility makes the nonzero closed reducing range full. -/
theorem compactRepresentationIsometry_surjective
    (rho : NonUnitalCStarRepresentation
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) L)
    (hrho : rho.IsIrreducible) (e : H) (xi : L) (hxi : ‖xi‖ = 1)
    (hfix : rho (compactRankOne ℂ e e) xi = xi) :
    Function.Surjective (compactRepresentationIsometry rho e xi hxi hfix) := by
  let U := compactRepresentationIsometry rho e xi hxi hfix
  have hnonzero : xi ≠ 0 := by
    intro h
    simpa [h] using hxi
  have hxi_range : xi ∈ U.toLinearMap.range := ⟨e, hfix⟩
  have htop : U.toLinearMap.range = ⊤ := by
    rcases hrho.2 _ (reduces_range_compactRepresentationIsometry rho e xi hxi hfix) with h | h
    · change U.toLinearMap.range = ⊥ at h
      have hxzero : xi = 0 := (Submodule.mem_bot (R := ℂ) (x := xi)).mp (h ▸ hxi_range)
      exact (hnonzero hxzero).elim
    · exact h
  intro y
  have hy : y ∈ U.toLinearMap.range := by rw [htop]; trivial
  exact hy

/-- A true surjective linear isometry with the original corner formula. -/
def compactRepresentationEquiv
    (rho : NonUnitalCStarRepresentation
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) L)
    (hrho : rho.IsIrreducible) (e : H) (xi : L) (hxi : ‖xi‖ = 1)
    (hfix : rho (compactRankOne ℂ e e) xi = xi) : H ≃ₗᵢ[ℂ] L :=
  LinearIsometryEquiv.ofSurjective (compactRepresentationIsometry rho e xi hxi hfix)
    (compactRepresentationIsometry_surjective rho hrho e xi hxi hfix)

@[simp]
theorem compactRepresentationEquiv_apply
    (rho : NonUnitalCStarRepresentation
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) L)
    (hrho : rho.IsIrreducible) (e : H) (xi : L) (hxi : ‖xi‖ = 1)
    (hfix : rho (compactRankOne ℂ e e) xi = xi) (x : H) :
    compactRepresentationEquiv rho hrho e xi hxi hfix x =
      rho (compactRankOne ℂ x e) xi := rfl

/-- Inverse intertwining for the very same unitary. -/
theorem compactRepresentationEquiv_symm_intertwines
    (rho : NonUnitalCStarRepresentation
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) L)
    (hrho : rho.IsIrreducible) (e : H) (xi : L) (hxi : ‖xi‖ = 1)
    (hfix : rho (compactRankOne ℂ e e) xi = xi)
    (a : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) (z : L) :
    (compactRepresentationEquiv rho hrho e xi hxi hfix).symm (rho a z) =
      (a : H →L[ℂ] H) ((compactRepresentationEquiv rho hrho e xi hxi hfix).symm z) := by
  let U := compactRepresentationEquiv rho hrho e xi hxi hfix
  apply U.injective
  rw [U.apply_symm_apply]
  have ht : U ((a : H →L[ℂ] H) (U.symm z)) = rho a (U (U.symm z)) :=
    compactRepresentationIsometry_intertwines rho e xi hxi hfix a (U.symm z)
  rw [U.apply_symm_apply] at ht
  exact ht.symm

/-- Arbitrary-Hilbert-universe irreducible representation classification. -/
theorem exists_compactRepresentationEquiv [Nontrivial H]
    (rho : NonUnitalCStarRepresentation
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) L)
    (hrho : rho.IsIrreducible) :
    ∃ U : H ≃ₗᵢ[ℂ] L,
      ∀ (a : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) (x : H),
        U ((a : H →L[ℂ] H) x) = rho a (U x) := by
  obtain ⟨z, hz⟩ := exists_ne (0 : H)
  let e := NormedSpace.normalize z
  have he : ‖e‖ = 1 := NormedSpace.norm_normalize hz
  obtain ⟨xi, hxi, hfix⟩ := exists_norm_eq_one_fixed_compactRankOne rho hrho.1 e he
  exact ⟨compactRepresentationEquiv rho hrho e xi hxi hfix,
    compactRepresentationIsometry_intertwines rho e xi hxi hfix⟩

/-- Actual unitary equivalence, never inferred merely from kernel equality. -/
theorem unitaryEquivalent_compactOperatorRepresentation [Nontrivial H]
    (rho : NonUnitalCStarRepresentation
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) L)
    (hrho : rho.IsIrreducible) :
    (compactOperatorRepresentation H).UnitaryEquivalent rho := by
  obtain ⟨U, hU⟩ := exists_compactRepresentationEquiv rho hrho
  exact ⟨U, hU⟩

end MathlibAnnex.Analysis.CStarAlgebra
