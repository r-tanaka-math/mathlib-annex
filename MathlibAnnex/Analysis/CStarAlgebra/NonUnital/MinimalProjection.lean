import Mathlib.Topology.Baire.LocallyCompactRegular
import MathlibAnnex.Topology.CountableBaire
import MathlibAnnex.Analysis.CStarAlgebra.IsolatedCharacter
import MathlibAnnex.Analysis.CStarAlgebra.MaximalAbelianContaining
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CharacterCountable
import MathlibAnnex.Analysis.CStarAlgebra.Representation.MinimalProjection

/-!
# A minimal projection in a non-unital singleton model

A maximal abelian subalgebra of the unitization is chosen to contain a
nonzero element of the original algebra.  Its non-scalar character space is
a nonempty open countable Baire space, so it has an isolated point away from
the scalar character.  The associated Gelfand projection consequently lies
in the original algebra.
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder IsMulCommutative

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- If a closed commutative subalgebra of a minimal unitization contains a
nonzero element with zero scalar coordinate, its countable character space
has an isolated character different from the scalar character. -/
theorem exists_isolated_character_ne_infinity
    (D : StarSubalgebra ℂ (Unitization ℂ A))
    [IsClosed (D : Set (Unitization ℂ A))]
    [IsMulCommutative D]
    [Countable (WeakDual.characterSpace ℂ D)]
    (d : D) (hd : d ≠ 0)
    (hdfst : (d : Unitization ℂ A).fst = 0) :
    ∃ chi : WeakDual.characterSpace ℂ D,
      chi ≠ infinityCharacterOn (A := A) D ∧
        IsOpen ({chi} : Set (WeakDual.characterSpace ℂ D)) := by
  letI : CommCStarAlgebra D := {}
  let X := WeakDual.characterSpace ℂ D
  let chiInf : X := infinityCharacterOn (A := A) D
  let U : Set X := {chiInf}ᶜ
  have hUopen : IsOpen U := isClosed_singleton.isOpen_compl
  have hchar : ∃ chi : X, chi d ≠ 0 := by
    by_contra hex
    have hall : ∀ chi : X, chi d = 0 := by
      intro chi
      by_contra hne
      exact hex ⟨chi, hne⟩
    apply hd
    apply (gelfandTransform_isometry D).injective
    ext chi
    simpa using hall chi
  have hUne : U.Nonempty := by
    obtain ⟨chi, hchi⟩ := hchar
    refine ⟨chi, ?_⟩
    change chi ≠ chiInf
    intro heq
    apply hchi
    rw [heq]
    exact hdfst
  letI : Nonempty U := hUne.to_subtype
  letI : BaireSpace U := hUopen.baireSpace
  obtain ⟨chi, hchiOpen⟩ :=
    MathlibAnnex.Topology.exists_isOpen_singleton (X := U)
  refine ⟨chi.1, chi.2, ?_⟩
  simpa using hUopen.isOpenMap_subtype_val ({chi} : Set U) hchiOpen

/-- For the Gelfand projection attached to `chi`, every different character
vanishes on that projection. -/
theorem character_apply_eq_zero_of_projection_mul_eq_smul
    (D : StarSubalgebra ℂ (Unitization ℂ A))
    [IsClosed (D : Set (Unitization ℂ A))]
    [IsMulCommutative D]
    (chi psi : WeakDual.characterSpace ℂ D)
    (hchi : chi ≠ psi) (p : D) (hp : IsStarProjection p) (hpne : p ≠ 0)
    (hpd : ∀ d : D, p * d = chi d • p) :
    psi p = 0 := by
  have hchip : chi p = 1 := by
    apply smul_left_injective ℂ hpne
    calc
      (chi p) • p = p * p := (hpd p).symm
      _ = p := hp.isIdempotentElem.eq
      _ = (1 : ℂ) • p := (one_smul ℂ p).symm
  by_contra hpsine
  apply hchi
  apply WeakDual.CharacterSpace.ext
  intro d
  have heq := congrArg psi (hpd d)
  have heq' : psi p * psi d = psi p * chi d := by
    simpa [mul_comm (chi d) (psi p)] using heq
  exact (mul_left_cancel₀ hpsine heq').symm

/-- A separable singleton irreducible model of a genuinely non-unital
C-star algebra forces a nonzero projection with scalar corner in that
algebra. -/
theorem exists_nonzero_projection_scalar_corner [Nontrivial A]
    [TopologicalSpace.SeparableSpace H]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi) :
    ∃ p : A, IsStarProjection p ∧ p ≠ 0 ∧
      ∀ a : A, ∃ c : ℂ, p * a * p = c • p := by
  obtain ⟨a, ha⟩ : ∃ a : A, a ≠ 0 := exists_ne 0
  let b : A := star a * a
  have hbne : b ≠ 0 := CStarRing.star_mul_self_ne_zero_iff a |>.2 ha
  have hbself : IsSelfAdjoint b := IsSelfAdjoint.star_mul_self a
  have hbinrself : IsSelfAdjoint (b : Unitization ℂ A) := hbself.inr ℂ
  obtain ⟨D, hD, hbD⟩ :=
    exists_maximalAbelian_containing_isSelfAdjoint (b : Unitization ℂ A) hbinrself
  letI : IsClosed (D : Set (Unitization ℂ A)) := hD.isClosed
  letI : IsMulCommutative D := hD.1
  letI : CommCStarAlgebra D := {}
  let d : D := ⟨(b : Unitization ℂ A), hbD⟩
  have hdne : d ≠ 0 := by
    intro hzero
    apply hbne
    apply Unitization.inr_injective (R := ℂ)
    exact congrArg Subtype.val hzero
  have hdfst : (d : Unitization ℂ A).fst = 0 := rfl
  have hcount := countable_characterSpace_of_nonUnital_singleton pi hsingle D
  letI : Countable (WeakDual.characterSpace ℂ D) := hcount
  obtain ⟨chi, hchiInf, hchiOpen⟩ :=
    exists_isolated_character_ne_infinity D d hdne hdfst
  obtain ⟨p, hp, hpne, hpd⟩ :=
    exists_projection_mul_eq_smul_of_isOpen_singleton chi hchiOpen
  have hpInf : infinityCharacterOn (A := A) D p = 0 :=
    character_apply_eq_zero_of_projection_mul_eq_smul D chi
      (infinityCharacterOn (A := A) D) hchiInf p hp hpne hpd
  have hpfst : (p : Unitization ℂ A).fst = 0 := by
    simpa using hpInf
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
  have hcornerU :=
    corner_eq_smul_of_maximalAbelian D hD chi p hp hpd
  refine ⟨pA, hpA, hpAne, ?_⟩
  intro x
  obtain ⟨c, hc⟩ := hcornerU (x : Unitization ℂ A)
  refine ⟨c, ?_⟩
  apply Unitization.inr_injective (R := ℂ)
  simpa [← hp_eq] using hc

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
