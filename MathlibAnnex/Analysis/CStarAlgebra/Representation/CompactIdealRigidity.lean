/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactOperators
import MathlibAnnex.Analysis.CStarAlgebra.Representation.EqualKernel

/-!
# Compact-ideal rigidity of irreducible representations

A representation of an operator algebra containing the compacts need only be
nonzero on the compact ideal. Its restriction is NOT assumed irreducible. The
existing compact corner isometry intertwines the whole algebra, so that the
irreducibility of the original representation makes its closed range full.

Equal actual kernels permit descent through an existing hom-kernel quotient
and its actual image equivalence. Compact containment is then essential to
turn kernel equality into unitary equivalence. This is a local result, not
an identification of an independent Type I definition with GCR.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set InnerProductSpace
open scoped CStarAlgebra InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : Type v} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
open NonUnitalCStarRepresentation

/-- The actual compact-ideal inclusion, with the inherited operations. -/
def compactIdealInclusion (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hK : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H →⋆ₙₐ[ℂ] S where
  toFun a := ⟨a.val, hK a.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem compactIdealInclusion_apply
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hK : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S)
    (a : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :
    (compactIdealInclusion S hK a).val = a.val := rfl

theorem compactIdealInclusion_injective
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hK : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S) :
    Function.Injective (compactIdealInclusion S hK) := by
  intro a b h
  exact Subtype.ext (congrArg (fun z : S => z.val) h)

section OperatorAlgebra
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (hS : IsClosed (S : Set (H →L[ℂ] H)))
local notation "closedOperatorS" =>
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hS)
variable (hK : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ S)

/-- Multiplication by ANY element of S acts on the output rank-one slot. -/
theorem mul_compactIdealInclusion_rankOne (a : S) (x e : H) :
    a * compactIdealInclusion S hK (compactRankOne ℂ x e) =
      compactIdealInclusion S hK (compactRankOne ℂ (a.val x) e) := by
  apply Subtype.ext
  exact comp_rankOne x e a.val

include hS hK in
/-- The old compact isometry intertwines all of S, not just its compact ideal. -/
theorem compactRepresentationIsometry_intertwines_of_compact_le
    (rho : @NonUnitalCStarRepresentation S closedOperatorS L _ _ _) (e : H) (xi : L)
    (hxi : ‖xi‖ = 1)
    (hfix : (rho.comp (compactIdealInclusion S hK)) (compactRankOne ℂ e e) xi = xi)
    (a : S) (x : H) :
    compactRepresentationIsometry (rho.comp (compactIdealInclusion S hK)) e xi hxi hfix
        (a.val x) =
      rho a (compactRepresentationIsometry (rho.comp (compactIdealInclusion S hK))
        e xi hxi hfix x) := by
  letI : NonUnitalCStarAlgebra S := closedOperatorS
  change rho (compactIdealInclusion S hK (compactRankOne ℂ (a.val x) e)) xi =
    rho a (rho (compactIdealInclusion S hK (compactRankOne ℂ x e)) xi)
  rw [← mul_compactIdealInclusion_rankOne, map_mul]
  rfl

include hS hK in
/-- The same range is closed and reducing for rho(S). -/
theorem reduces_range_compactRepresentationIsometry_of_compact_le
    (rho : @NonUnitalCStarRepresentation S closedOperatorS L _ _ _) (e : H) (xi : L)
    (hxi : ‖xi‖ = 1)
    (hfix : (rho.comp (compactIdealInclusion S hK)) (compactRankOne ℂ e e) xi = xi) :
    @NonUnitalCStarRepresentation.Reduces S closedOperatorS L _ _ _ rho
      (compactRepresentationIsometry (rho.comp (compactIdealInclusion S hK))
        e xi hxi hfix).toLinearMap.range := by
  letI : NonUnitalCStarAlgebra S := closedOperatorS
  let U := compactRepresentationIsometry (rho.comp (compactIdealInclusion S hK))
    e xi hxi hfix
  refine ⟨U.isometry.isClosedEmbedding.isClosed_range, ?_⟩
  intro a z hz
  obtain ⟨x, rfl⟩ := hz
  refine ⟨⟨a.val x, compactRepresentationIsometry_intertwines_of_compact_le S hS hK rho e xi hxi hfix a x⟩, ?_⟩
  refine ⟨(star a).val x, ?_⟩
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  exact compactRepresentationIsometry_intertwines_of_compact_le S hS hK rho e xi hxi hfix (star a) x

include hS hK in
/-- Only the original representation is required to be irreducible. -/
theorem compactRepresentationIsometry_surjective_of_compact_le
    (rho : @NonUnitalCStarRepresentation S closedOperatorS L _ _ _) (hrho : @NonUnitalCStarRepresentation.IsIrreducible S closedOperatorS L _ _ _ rho)
    (e : H) (xi : L) (hxi : ‖xi‖ = 1)
    (hfix : (rho.comp (compactIdealInclusion S hK)) (compactRankOne ℂ e e) xi = xi) :
    Function.Surjective
      (compactRepresentationIsometry (rho.comp (compactIdealInclusion S hK))
        e xi hxi hfix) := by
  letI : NonUnitalCStarAlgebra S := closedOperatorS
  let U := compactRepresentationIsometry (rho.comp (compactIdealInclusion S hK))
    e xi hxi hfix
  have hn : xi ≠ 0 := by intro h; simpa [h] using hxi
  have hm : xi ∈ U.toLinearMap.range := ⟨e, hfix⟩
  have ht : U.toLinearMap.range = ⊤ := by
    rcases hrho.2 _ (reduces_range_compactRepresentationIsometry_of_compact_le S hS hK rho e xi hxi hfix) with h | h
    · have hbot : U.toLinearMap.range = ⊥ := h
      rw [hbot] at hm
      exact (hn ((Submodule.mem_bot ℂ).1 hm)).elim
    · exact h
  intro z
  have hz : z ∈ U.toLinearMap.range := by rw [ht]; trivial
  exact hz

/-- A genuine unitary with the original rank-one corner formula. -/
def compactIdealRepresentationEquiv
    (rho : @NonUnitalCStarRepresentation S closedOperatorS L _ _ _) (hrho : @NonUnitalCStarRepresentation.IsIrreducible S closedOperatorS L _ _ _ rho)
    (e : H) (xi : L) (hxi : ‖xi‖ = 1)
    (hfix : (rho.comp (compactIdealInclusion S hK)) (compactRankOne ℂ e e) xi = xi) :
    H ≃ₗᵢ[ℂ] L := by
  letI : NonUnitalCStarAlgebra S := closedOperatorS
  exact LinearIsometryEquiv.ofSurjective
    (compactRepresentationIsometry (rho.comp (compactIdealInclusion S hK)) e xi hxi hfix)
    (compactRepresentationIsometry_surjective_of_compact_le S hS hK rho hrho e xi hxi hfix)

@[simp]
theorem compactIdealRepresentationEquiv_apply
    (rho : @NonUnitalCStarRepresentation S closedOperatorS L _ _ _) (hrho : @NonUnitalCStarRepresentation.IsIrreducible S closedOperatorS L _ _ _ rho)
    (e : H) (xi : L) (hxi : ‖xi‖ = 1)
    (hfix : (rho.comp (compactIdealInclusion S hK)) (compactRankOne ℂ e e) xi = xi)
    (x : H) :
    compactIdealRepresentationEquiv S hS hK rho hrho e xi hxi hfix x =
      rho (compactIdealInclusion S hK (compactRankOne ℂ x e)) xi := rfl

include hS hK in
/-- Both all-point intertwining formulas use one and the same unitary. -/
theorem exists_compactIdealRepresentationEquiv [Nontrivial H]
    (rho : @NonUnitalCStarRepresentation S closedOperatorS L _ _ _) (hrho : @NonUnitalCStarRepresentation.IsIrreducible S closedOperatorS L _ _ _ rho)
    (hres : NonUnitalCStarRepresentation.IsNonzero (rho.comp (compactIdealInclusion S hK))) :
    ∃ U : H ≃ₗᵢ[ℂ] L,
      (∀ (a : S) (x : H), U (a.val x) = rho a (U x)) ∧
      (∀ (a : S) (z : L), U.symm (rho a z) = a.val (U.symm z)) := by
  letI : NonUnitalCStarAlgebra S := closedOperatorS
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  let e := NormedSpace.normalize x
  have he : ‖e‖ = 1 := NormedSpace.norm_normalize hx
  obtain ⟨xi, hxi, hfix⟩ :=
    exists_norm_eq_one_fixed_compactRankOne (rho.comp (compactIdealInclusion S hK)) hres e he
  let U := compactIdealRepresentationEquiv S hS hK rho hrho e xi hxi hfix
  have hi : ∀ (a : S) (x : H), U (a.val x) = rho a (U x) :=
    compactRepresentationIsometry_intertwines_of_compact_le S hS hK rho e xi hxi hfix
  refine ⟨U, hi, ?_⟩
  intro a z
  apply U.injective
  rw [U.apply_symm_apply, hi, U.apply_symm_apply]

include hS hK in
/-- Local uniqueness with only a nonzero compact restriction. -/
theorem unitaryEquivalent_inclusion_of_nonzero_compact_restriction [Nontrivial H]
    (rho : @NonUnitalCStarRepresentation S closedOperatorS L _ _ _) (hrho : @NonUnitalCStarRepresentation.IsIrreducible S closedOperatorS L _ _ _ rho)
    (hres : NonUnitalCStarRepresentation.IsNonzero (rho.comp (compactIdealInclusion S hK))) :
    @NonUnitalCStarRepresentation.UnitaryEquivalent S closedOperatorS
      H L _ _ _ _ _ _ (NonUnitalStarSubalgebraClass.subtype S) rho := by
  letI : NonUnitalCStarAlgebra S := closedOperatorS
  obtain ⟨U, hU, _⟩ := exists_compactIdealRepresentationEquiv S hS hK rho hrho hres
  exact ⟨U, hU⟩

include hS hK in
/-- Faithfulness implies nonzero restriction, by a genuine nonzero compact. -/
theorem isNonzero_compact_restriction_of_injective [Nontrivial H]
    (rho : @NonUnitalCStarRepresentation S closedOperatorS L _ _ _) (hinj : Function.Injective rho) :
    NonUnitalCStarRepresentation.IsNonzero (rho.comp (compactIdealInclusion S hK)) := by
  letI : NonUnitalCStarAlgebra S := closedOperatorS
  obtain ⟨a, ha⟩ := (isIrreducible_compactOperatorRepresentation H).1
  refine ⟨a, ?_⟩
  intro hz
  have hz' : compactIdealInclusion S hK a = 0 :=
    hinj (by simpa only [NonUnitalStarAlgHom.comp_apply, map_zero] using hz)
  exact ha (congrArg (fun z : S => z.val) hz')

include hS hK in
/-- The faithful special case needs neither separability nor a unit in S. -/
theorem unitaryEquivalent_inclusion_of_injective [Nontrivial H]
    (rho : @NonUnitalCStarRepresentation S closedOperatorS L _ _ _) (hrho : @NonUnitalCStarRepresentation.IsIrreducible S closedOperatorS L _ _ _ rho)
    (hinj : Function.Injective rho) :
    @NonUnitalCStarRepresentation.UnitaryEquivalent S closedOperatorS
      H L _ _ _ _ _ _ (NonUnitalStarSubalgebraClass.subtype S) rho := by
  letI : NonUnitalCStarAlgebra S := closedOperatorS
  exact unitaryEquivalent_inclusion_of_nonzero_compact_restriction S hS hK rho hrho
    (isNonzero_compact_restriction_of_injective S hS hK rho hinj)

end OperatorAlgebra

namespace NonUnitalCStarRepresentation

variable {A : Type w} [NonUnitalCStarAlgebra A]
variable (pi : NonUnitalCStarRepresentation A H) (rho : NonUnitalCStarRepresentation A L)

variable [PartialOrder A] [StarOrderedRing A]
local instance : NonUnitalCStarAlgebra (NonUnitalStarAlgHom.range pi) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (NonUnitalStarAlgHom.range pi)
    (h_closed := HomKernelQuotient.isClosed_image pi)

/-- Same kernel plus compact containment, NOT same kernel alone, yields a
unitary between the original Hilbert spaces. The source action need only have
compact-containing range; its nonzeroness is derived from rho and the kernel. -/
theorem unitaryEquivalent_of_kernelIdeal_eq_of_compact_le_range
    (hrho : rho.IsIrreducible) (hker : kernelIdeal pi = kernelIdeal rho)
    (hK : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ (NonUnitalStarAlgHom.range pi)) :
    pi.UnitaryEquivalent rho := by
  have hn : pi.IsNonzero := by
    obtain ⟨a, ha⟩ := hrho.1
    refine ⟨a, ?_⟩
    intro hz
    have hm : a ∈ kernelIdeal pi := (mem_kernelIdeal pi a).2 hz
    rw [hker] at hm
    exact ha ((mem_kernelIdeal rho a).1 hm)
  letI : Nontrivial H := nontrivial_of_isNonzero pi hn
  have hf := (isIrreducible_factorThroughImage_iff pi rho hker).2 hrho
  obtain ⟨U, hU⟩ := unitaryEquivalent_inclusion_of_injective
    (NonUnitalStarAlgHom.range pi) (HomKernelQuotient.isClosed_image pi) hK
    (factorThroughImage pi rho hker) hf (factorThroughImage_injective pi rho hker)
  refine ⟨U, ?_⟩
  intro a x
  have h := hU ((NonUnitalStarAlgHom.rangeRestrict pi) a) x
  simpa only [factorThroughImage_apply, NonUnitalStarSubalgebraClass.subtype_apply,
    NonUnitalStarAlgHom.rangeRestrict, NonUnitalStarAlgHom.coe_codRestrict] using h

/-- The converse is the already proved unitary invariance of the actual kernel. -/
theorem unitaryEquivalent_iff_kernelIdeal_eq_of_compact_le_range
    (hrho : rho.IsIrreducible)
    (hK : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ (NonUnitalStarAlgHom.range pi)) :
    pi.UnitaryEquivalent rho ↔ kernelIdeal pi = kernelIdeal rho :=
  ⟨fun h => h.kernelIdeal_eq,
    fun h => unitaryEquivalent_of_kernelIdeal_eq_of_compact_le_range pi rho hrho h hK⟩

/-- Direct and inverse formulas for one unitary on the ORIGINAL actions. -/
theorem exists_unitary_intertwiner_of_kernelIdeal_eq_of_compact_le_range
    (hrho : rho.IsIrreducible) (hker : kernelIdeal pi = kernelIdeal rho)
    (hK : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤ (NonUnitalStarAlgHom.range pi)) :
    ∃ U : H ≃ₗᵢ[ℂ] L,
      (∀ (a : A) (x : H), U (pi a x) = rho a (U x)) ∧
      (∀ (a : A) (y : L), U.symm (rho a y) = pi a (U.symm y)) := by
  obtain ⟨U, hU⟩ :=
    unitaryEquivalent_of_kernelIdeal_eq_of_compact_le_range pi rho hrho hker hK
  refine ⟨U, hU, ?_⟩
  intro a y
  apply U.injective
  rw [U.apply_symm_apply, hU, U.apply_symm_apply]

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
