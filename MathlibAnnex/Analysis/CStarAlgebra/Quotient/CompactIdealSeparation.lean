/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.SingletonOperatorIdeal
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Representatives
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.ImageRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.CompactPreimage
import MathlibAnnex.Analysis.Normed.Module.QuotientDual
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Compact annihilators: an actual Banach quotient and the singleton obstruction

The first part supplies a norm-one continuous linear separator on the original
operator subalgebra whenever it contains a noncompact member. The quotient is
the standard normed VECTOR SPACE quotient by its compact subspace; no quotient
multiplication, star, positivity or C-star identity is asserted. The separator
is not claimed to be a state or a representation.

The second part proves the other end of the proposed contradiction: a genuine
irreducible action annihilating these compacts cannot exist under the original
singleton-spectrum and multiplier hypotheses. It uses actual unitary equivalence
of representations and a nonzero rank-one operator, not equality of primitive
kernels. Existence of a nonzero irreducible separating action in the general
nonunital proper-ideal case is deliberately not asserted by this module.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The inverse image of the existing compact-operator submodule under the
literal inclusion. This is a submodule of `S`, not a new compactness predicate. -/
def compactOperatorSubmoduleIn (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    Submodule ℂ S :=
  (compactOperator (RingHom.id ℂ) H H).comap (LinearMapClass.linearMap S.subtype)

@[simp]
theorem mem_compactOperatorSubmoduleIn
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) (a : S) :
    a ∈ compactOperatorSubmoduleIn S ↔ IsCompactOperator (a : H →L[ℂ] H) := Iff.rfl

/-- Closedness is inherited from the original operator-norm topology. -/
theorem isClosed_compactOperatorSubmoduleIn
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    IsClosed (compactOperatorSubmoduleIn S : Set S) := by
  change IsClosed ((fun a : S => (a : H →L[ℂ] H)) ⁻¹'
    {T : H →L[ℂ] H | IsCompactOperator T})
  exact isClosed_setOf_isCompactOperator.preimage continuous_subtype_val

/-- For a closed C-star subalgebra, this is precisely the carrier of the
already existing compact preimage ideal, not an independently defined ideal. -/
theorem coe_compactOperatorSubmoduleIn_eq_compactPreimageIdeal
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hclosed : IsClosed (S : Set (H →L[ℂ] H))) :
    letI : NonUnitalCStarAlgebra S :=
      NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hclosed)
    (compactOperatorSubmoduleIn S : Set S) =
      ((MathlibAnnex.CStarAlgebra.compactPreimageIdeal
        (NonUnitalStarSubalgebraClass.subtype S) : TwoSidedIdeal S) : Set S) := by
  letI : NonUnitalCStarAlgebra S :=
    NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hclosed)
  ext a
  exact (MathlibAnnex.CStarAlgebra.mem_compactPreimageIdeal
    (NonUnitalStarSubalgebraClass.subtype S) a).symm

/-- The canonical quotient kills exactly the compact members of `S`. -/
theorem mkQ_compactOperatorSubmoduleIn_eq_zero_iff
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) (a : S) :
    (compactOperatorSubmoduleIn S).mkQ a = 0 ↔
      IsCompactOperator (a : H →L[ℂ] H) := by
  exact Submodule.Quotient.mk_eq_zero (compactOperatorSubmoduleIn S)

/-- An actual noncompact member gives an actual nonzero quotient vector. -/
theorem nontrivial_quotient_compactOperatorSubmoduleIn
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) (a : S)
    (ha : ¬ IsCompactOperator (a : H →L[ℂ] H)) :
    Nontrivial (S ⧸ compactOperatorSubmoduleIn S) := by
  exact nontrivial_of_ne ((compactOperatorSubmoduleIn S).mkQ a) 0
    (fun h => ha ((mkQ_compactOperatorSubmoduleIn_eq_zero_iff S a).1 h))

/-- Completeness of the standard quotient follows from closedness of `S`;
there is no norm transported from an unspecified representation. -/
theorem completeSpace_quotient_compactOperatorSubmoduleIn
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hclosed : IsClosed (S : Set (H →L[ℂ] H))) :
    CompleteSpace (S ⧸ compactOperatorSubmoduleIn S) := by
  letI : CompleteSpace S := hclosed.completeSpace_coe
  infer_instance

/-- Hahn--Banach gives a norm-one functional annihilating compacts and
nonzero on the specified noncompact member. It is only a linear separator:
positivity, purity and a separating representation require further proof. -/
theorem exists_norm_one_functional_annihilating_compacts
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) (a : S)
    (ha : ¬ IsCompactOperator (a : H →L[ℂ] H)) :
    ∃ f : StrongDual ℂ S,
      ‖f‖ = 1 ∧
      (∀ b : S, IsCompactOperator (b : H →L[ℂ] H) → f b = 0) ∧
      f a = (‖(compactOperatorSubmoduleIn S).mkQ a‖ : ℂ) ∧ f a ≠ 0 := by
  let N := compactOperatorSubmoduleIn S
  letI : IsClosed (N : Set S) := isClosed_compactOperatorSubmoduleIn S
  have hqa : N.mkQ a ≠ 0 := by
    intro h
    exact ha ((mkQ_compactOperatorSubmoduleIn_eq_zero_iff S a).1 h)
  have hn : ‖N.mkQ a‖ ≠ 0 :=
    (@norm_ne_zero_iff (S ⧸ N)
      (@NormedAddCommGroup.toNormedAddGroup _
        (Submodule.Quotient.normedAddCommGroup N)) (N.mkQ a)).mpr hqa
  obtain ⟨g, hg, hga⟩ := exists_dual_vector ℂ (N.mkQ a) hn
  let f : StrongDual ℂ S := g.comp N.mkQL
  have hfa : f a = (‖N.mkQ a‖ : ℂ) := hga
  refine ⟨f, (N.norm_comp_mkQL g).trans hg, ?_, hfa, ?_⟩
  · intro b hb
    change g (N.mkQ b) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 hb, map_zero]
  · rw [hfa]
    intro h
    apply hn
    simpa only [Complex.ofReal_re, Complex.zero_re] using congrArg Complex.re h

/-- The linear separator characterizes noncompactness; the reverse
implication is evaluation on the specified compact vector itself. -/
theorem not_isCompactOperator_iff_exists_annihilating_functional
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) (a : S) :
    (¬ IsCompactOperator (a : H →L[ℂ] H)) ↔
      ∃ f : StrongDual ℂ S, ‖f‖ = 1 ∧
        (∀ b : S, IsCompactOperator (b : H →L[ℂ] H) → f b = 0) ∧ f a ≠ 0 := by
  constructor
  · intro ha
    obtain ⟨f, hf, hann, _hvalue, hne⟩ :=
      exists_norm_one_functional_annihilating_compacts S a ha
    exact ⟨f, hf, hann, hne⟩
  · rintro ⟨f, _hf, hann, hne⟩ ha
    exact hne (hann a ha)

/-- Strict compact containment supplies a specified noncompact element,
not a quotient-representation premise. -/
theorem exists_noncompact_of_compactOperatorStarSubalgebra_lt
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hproper : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H < S) :
    ∃ a : S, ¬ IsCompactOperator (a : H →L[ℂ] H) := by
  classical
  by_contra hnone
  have hle : S ≤ ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H := by
    intro a ha
    by_contra hnoncompact
    exact hnone ⟨⟨a, ha⟩, hnoncompact⟩
  exact (not_le_of_gt hproper) hle

/-- Properness gives both a nonzero standard quotient and a genuine linear
annihilator. This still does NOT equip that quotient with C-star operations. -/
theorem exists_quotient_separator_of_compactOperatorStarSubalgebra_lt
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hproper : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H < S) :
    Nontrivial (S ⧸ compactOperatorSubmoduleIn S) ∧
      ∃ (a : S) (f : StrongDual ℂ S), ‖f‖ = 1 ∧
        (∀ b : S, IsCompactOperator (b : H →L[ℂ] H) → f b = 0) ∧
        f a = (‖(compactOperatorSubmoduleIn S).mkQ a‖ : ℂ) ∧ f a ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_noncompact_of_compactOperatorStarSubalgebra_lt S hproper
  obtain ⟨f, hf, hann, hvalue, hne⟩ :=
    exists_norm_one_functional_annihilating_compacts S a ha
  exact ⟨nontrivial_quotient_compactOperatorSubmoduleIn S a ha,
    a, f, hf, hann, hvalue, hne⟩

section Singleton

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Every irreducible action detects each rank-one preimage: equality of
actual spectrum points supplies a unitary intertwiner in arbitrary universes. -/
theorem exists_preimage_rankOne_map_ne_zero_of_singleton
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hinj : Function.Injective pi)
    (hmul : ∀ (b a : H →L[ℂ] H), a ∈ (NonUnitalStarAlgHom.range pi) →
      b * a ∈ (NonUnitalStarAlgHom.range pi) ∧ a * b ∈ (NonUnitalStarAlgHom.range pi))
    (rho : NonUnitalCStarRepresentation A K) (hrho : rho.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ a : A, pi a = InnerProductSpace.rankOne ℂ x y ∧ rho a ≠ 0 := by
  obtain ⟨q, hq⟩ := hsingle
  have heq : IrreducibleSpectrum.ofRepresentation pi hpi =
      IrreducibleSpectrum.ofRepresentation rho hrho :=
    (hq _).trans (hq _).symm
  obtain ⟨U, hU⟩ := (IrreducibleSpectrum.ofRepresentation_eq_iff pi rho hpi hrho).1 heq
  obtain ⟨a, ha⟩ := exists_preimage_compact_of_image_mul_mem pi hinj hpi.1 hmul
    (InnerProductSpace.rankOne ℂ x y) (InnerProductSpace.isCompactOperator_rankOne x y)
  refine ⟨a, ha, ?_⟩
  intro hzero
  have hpizero : pi a = 0 := by
    ext z
    apply U.injective
    calc
      U (pi a z) = rho a (U z) := hU a z
      _ = U 0 := by rw [hzero]; simp
  exact InnerProductSpace.rankOne_ne_zero hx hy (ha.symm.trans hpizero)

/-- The singleton hypothesis obstructs a compact-annihilating irreducible
representation. This proves the contradiction end, not existence of the
separating representation when the compact ideal is proper. -/
theorem not_isIrreducible_of_annihilates_compact_preimages
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hinj : Function.Injective pi)
    (hmul : ∀ (b a : H →L[ℂ] H), a ∈ (NonUnitalStarAlgHom.range pi) →
      b * a ∈ (NonUnitalStarAlgHom.range pi) ∧ a * b ∈ (NonUnitalStarAlgHom.range pi))
    (rho : NonUnitalCStarRepresentation A K)
    (hann : ∀ a : A, IsCompactOperator (pi a) → rho a = 0) :
    ¬ rho.IsIrreducible := by
  intro hrho
  letI : Nontrivial H := NonUnitalCStarRepresentation.nontrivial_of_isNonzero pi hpi.1
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  obtain ⟨a, ha, hne⟩ := exists_preimage_rankOne_map_ne_zero_of_singleton
    hsingle pi hpi hinj hmul rho hrho x x hx hx
  apply hne
  apply hann a
  rw [ha]
  exact InnerProductSpace.isCompactOperator_rankOne x x

local instance (pi : NonUnitalCStarRepresentation A H) :
    NonUnitalCStarAlgebra (NonUnitalStarAlgHom.range pi) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (NonUnitalStarAlgHom.range pi)
    (h_closed := HomKernelQuotient.isClosed_image pi)

/-- An action on the literal image is pulled back through the actual
surjective range restriction. No quotient action is postulated or created. -/
theorem not_isIrreducible_of_image_annihilates_compacts
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hinj : Function.Injective pi)
    (hmul : ∀ (b a : H →L[ℂ] H), a ∈ (NonUnitalStarAlgHom.range pi) →
      b * a ∈ (NonUnitalStarAlgHom.range pi) ∧ a * b ∈ (NonUnitalStarAlgHom.range pi))
    (rho : NonUnitalCStarRepresentation (NonUnitalStarAlgHom.range pi) K)
    (hann : ∀ a : (NonUnitalStarAlgHom.range pi), IsCompactOperator (a : H →L[ℂ] H) → rho a = 0) :
    ¬ rho.IsIrreducible := by
  intro hrho
  have hpull : NonUnitalCStarRepresentation.IsIrreducible
      (rho.comp (NonUnitalStarAlgHom.rangeRestrict pi)) :=
    (NonUnitalCStarRepresentation.isIrreducible_comp_iff_of_surjective
      rho (NonUnitalStarAlgHom.rangeRestrict pi) (NonUnitalCStarRepresentation.rangeRestrict_surjective pi)).2 hrho
  exact (not_isIrreducible_of_annihilates_compact_preimages
    hsingle pi hpi hinj hmul (rho.comp (NonUnitalStarAlgHom.rangeRestrict pi))
      (fun a ha => hann ((NonUnitalStarAlgHom.rangeRestrict pi) a) ha)) hpull

end Singleton
end MathlibAnnex.Analysis.CStarAlgebra
