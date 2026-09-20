import MathlibAnnex.Topology.CompactCardinality
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.MinimalProjection
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CharacterCardinality

/-!
# Minimal projections without a unit under a density bound

The scalar character is removed before applying the locally compact-space
lemma.  The selected isolated character therefore gives a projection in the
original algebra, not merely in its unitization.
-/

set_option autoImplicit false

open Set
open scoped Cardinal ComplexOrder IsMulCommutative

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- A nonzero element with zero scalar part is detected by a non-scalar
character.  No representation or cardinality hypothesis is needed. -/
theorem exists_character_ne_infinity_apply_ne_zero
    (D : StarSubalgebra ℂ (Unitization ℂ A))
    [IsClosed (D : Set (Unitization ℂ A))] [IsMulCommutative D]
    (d : D) (hd : d ≠ 0) (hdfst : (d : Unitization ℂ A).fst = 0) :
    ∃ chi : WeakDual.characterSpace ℂ D,
      chi ≠ infinityCharacterOn (A := A) D ∧ chi d ≠ 0 := by
  letI : CommCStarAlgebra D := {}
  have hchar : ∃ chi : WeakDual.characterSpace ℂ D, chi d ≠ 0 := by
    by_contra hex
    have hall : ∀ chi : WeakDual.characterSpace ℂ D, chi d = 0 := by
      intro chi
      by_contra hne
      exact hex ⟨chi, hne⟩
    apply hd
    apply (gelfandTransform_isometry D).injective
    ext chi
    simpa using hall chi
  obtain ⟨chi, hchi⟩ := hchar
  refine ⟨chi, ?_, hchi⟩
  intro heq
  apply hchi
  rw [heq]
  exact hdfst

/-- Find an isolated character in the non-scalar open complement. -/
theorem exists_isolated_character_ne_infinity_of_cardinalMk_lt_continuum
    (D : StarSubalgebra ℂ (Unitization ℂ A))
    [IsClosed (D : Set (Unitization ℂ A))] [IsMulCommutative D]
    (hcard : #(NonScalarCharacterSpace (A := A) D) < Cardinal.continuum)
    (d : D) (hd : d ≠ 0) (hdfst : (d : Unitization ℂ A).fst = 0) :
    ∃ chi : WeakDual.characterSpace ℂ D,
      chi ≠ infinityCharacterOn (A := A) D ∧
        IsOpen ({chi} : Set (WeakDual.characterSpace ℂ D)) := by
  letI : CommCStarAlgebra D := {}
  let X := WeakDual.characterSpace ℂ D
  let U : Set X := {infinityCharacterOn (A := A) D}ᶜ
  have hUopen : IsOpen U := isClosed_singleton.isOpen_compl
  obtain ⟨chi, hchi, -⟩ := exists_character_ne_infinity_apply_ne_zero D d hd hdfst
  letI : Nonempty U := ⟨⟨chi, hchi⟩⟩
  letI : LocallyCompactSpace U := hUopen.locallyCompactSpace
  have hUcard : #U < Cardinal.continuum := hcard
  obtain ⟨psi, hpsiOpen⟩ :=
    MathlibAnnex.Topology.exists_isOpen_singleton_of_cardinalMk_lt_continuum hUcard
  refine ⟨psi.1, psi.2, ?_⟩
  simpa only [Set.image_singleton] using
    hUopen.isOpenMap_subtype_val ({psi} : Set U) hpsiOpen

/-- An isolated non-scalar character of a maximal abelian subalgebra of the
unitization produces a nonzero scalar corner in the original algebra. -/
theorem exists_nonzero_projection_scalar_corner_of_isolated_character_ne_infinity
    (D : StarSubalgebra ℂ (Unitization ℂ A)) (hD : IsMaximalAbelian D)
    [IsClosed (D : Set (Unitization ℂ A))] [IsMulCommutative D]
    (chi : WeakDual.characterSpace ℂ D)
    (hchiInf : chi ≠ infinityCharacterOn (A := A) D)
    (hchiOpen : IsOpen ({chi} : Set (WeakDual.characterSpace ℂ D))) :
    ∃ p : A, IsStarProjection p ∧ p ≠ 0 ∧
      ∀ a : A, ∃ c : ℂ, p * a * p = c • p := by
  letI : CommCStarAlgebra D := {}
  obtain ⟨p, hp, hpne, hpd⟩ :=
    exists_projection_mul_eq_smul_of_isOpen_singleton chi hchiOpen
  have hpInf : infinityCharacterOn (A := A) D p = 0 :=
    character_apply_eq_zero_of_projection_mul_eq_smul D chi
      (infinityCharacterOn (A := A) D) hchiInf p hp hpne hpd
  have hpfst : (p : Unitization ℂ A).fst = 0 := by simpa using hpInf
  let pA : A := (p : Unitization ℂ A).snd
  have hp_eq : (p : Unitization ℂ A) = (pA : Unitization ℂ A) := by
    ext <;> simp [pA, hpfst]
  have hpA : IsStarProjection pA := by
    apply IsStarProjection.of_inr (R := ℂ)
    rw [← hp_eq]
    exact hp.map D.subtype
  have hpAne : pA ≠ 0 := by
    intro hzero
    apply hpne
    apply Subtype.ext
    rw [hp_eq, hzero]
    rfl
  have hcornerU := corner_eq_smul_of_maximalAbelian D hD chi p hp hpd
  refine ⟨pA, hpA, hpAne, ?_⟩
  intro x
  obtain ⟨c, hc⟩ := hcornerU (x : Unitization ℂ A)
  refine ⟨c, ?_⟩
  apply Unitization.inr_injective (R := ℂ)
  simpa [← hp_eq] using hc

/-- The cardinal version of the genuinely nonunital minimal-projection theorem. -/
theorem exists_nonzero_projection_scalar_corner_of_singleton_of_dense [Nontrivial A]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (s : Set H) (hs : Dense s) (hcard : #s < Cardinal.continuum) :
    ∃ p : A, IsStarProjection p ∧ p ≠ 0 ∧
      ∀ a : A, ∃ c : ℂ, p * a * p = c • p := by
  obtain ⟨a, ha⟩ : ∃ a : A, a ≠ 0 := exists_ne 0
  let b : A := star a * a
  have hbne : b ≠ 0 := CStarRing.star_mul_self_ne_zero_iff a |>.2 ha
  have hbself : IsSelfAdjoint b := IsSelfAdjoint.star_mul_self a
  obtain ⟨D, hD, hbD⟩ :=
    exists_maximalAbelian_containing_isSelfAdjoint
      (b : Unitization ℂ A) (hbself.inr ℂ)
  letI : IsClosed (D : Set (Unitization ℂ A)) := hD.isClosed
  letI : IsMulCommutative D := hD.1
  let d : D := ⟨(b : Unitization ℂ A), hbD⟩
  have hdne : d ≠ 0 := by
    intro hzero
    apply hbne
    apply Unitization.inr_injective (R := ℂ)
    exact congrArg Subtype.val hzero
  have hsmall := cardinalMk_nonScalarCharacterSpace_lt_continuum_of_singleton_of_dense
    pi hsingle s hs hcard D
  obtain ⟨chi, hchiInf, hchiOpen⟩ :=
    exists_isolated_character_ne_infinity_of_cardinalMk_lt_continuum D hsmall d hdne rfl
  exact exists_nonzero_projection_scalar_corner_of_isolated_character_ne_infinity
    D hD chi hchiInf hchiOpen

end NonUnitalCStarRepresentation
end MathlibAnnex.Analysis.CStarAlgebra
