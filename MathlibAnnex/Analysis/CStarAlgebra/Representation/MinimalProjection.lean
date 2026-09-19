import Mathlib.Topology.Baire.LocallyCompactRegular
import MathlibAnnex.Topology.CountableBaire
import MathlibAnnex.Analysis.CStarAlgebra.IsolatedCharacter
import MathlibAnnex.Analysis.CStarAlgebra.MaximalAbelian
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CharacterCountable

/-!
# A minimal projection from a separable singleton model
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder IsMulCommutative

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The projection belonging to an isolated character of a maximal abelian
subalgebra has a one-dimensional corner in the ambient algebra. -/
theorem corner_eq_smul_of_maximalAbelian
    (D : StarSubalgebra ℂ A) (hD : IsMaximalAbelian D)
    (chi : WeakDual.characterSpace ℂ D) (p : D)
    (hp : IsStarProjection p)
    (hpd : ∀ d : D, p * d = chi d • p) :
    ∀ a : A, ∃ c : ℂ, (p : A) * a * (p : A) = c • (p : A) := by
  letI : IsMulCommutative D := hD.1
  intro a
  let x : A := (p : A) * a * (p : A)
  have hpda (d : D) : (p : A) * (d : A) = chi d • (p : A) :=
    congrArg Subtype.val (hpd d)
  have hdpa (d : D) : (d : A) * (p : A) = chi d • (p : A) := by
    calc
      (d : A) * (p : A) = ((d * p : D) : A) := rfl
      _ = ((p * d : D) : A) := congrArg Subtype.val (mul_comm' d p)
      _ = chi d • (p : A) := hpda d
  have hxcomm (d : D) : x * (d : A) = (d : A) * x := by
    calc
      x * (d : A) = (p : A) * a * ((p : A) * (d : A)) := by simp [x, mul_assoc]
      _ = (p : A) * a * (chi d • (p : A)) := by rw [hpda d]
      _ = chi d • x := by simp [x, mul_assoc]
      _ = (chi d • (p : A)) * a * (p : A) := by simp [x, mul_assoc]
      _ = ((d : A) * (p : A)) * a * (p : A) := by rw [hdpa d]
      _ = (d : A) * x := by simp [x, mul_assoc]
  have hxmem : x ∈ D := hD.mem_of_commute hxcomm
  let xd : D := ⟨x, hxmem⟩
  have hcorner := congrArg Subtype.val (hpd xd)
  change (p : A) * x = chi xd • (p : A) at hcorner
  have hpidem : (p : A) * (p : A) = (p : A) :=
    congrArg Subtype.val hp.isIdempotentElem.eq
  have hpx : (p : A) * x = x := by
    calc
      (p : A) * x = ((p : A) * (p : A)) * a * (p : A) := by
        simp [x, mul_assoc]
      _ = x := by rw [hpidem]
  refine ⟨chi xd, ?_⟩
  change x = chi xd • (p : A)
  exact hpx.symm.trans hcorner

namespace Representation

/-- A separable singleton irreducible model forces the ambient unital
C-star algebra to contain a nonzero projection with scalar corner. -/
theorem exists_nonzero_projection_scalar_corner [Nontrivial A]
    [TopologicalSpace.SeparableSpace H]
    (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi) :
    ∃ p : A, IsStarProjection p ∧ p ≠ 0 ∧
      ∀ a : A, ∃ c : ℂ, p * a * p = c • p := by
  obtain ⟨D, hD⟩ := exists_maximalAbelian (A := A)
  letI : IsClosed (D : Set A) := hD.isClosed
  letI : IsMulCommutative D := hD.1
  letI : CommCStarAlgebra D := {}
  have hcount := countable_characterSpace_of_singleton pi hsingle D
  letI : Countable (WeakDual.characterSpace ℂ D) := hcount
  obtain ⟨chi, hchi⟩ :=
    MathlibAnnex.Topology.exists_isOpen_singleton
      (X := WeakDual.characterSpace ℂ D)
  obtain ⟨p, hp, hpne, hpd⟩ :=
    exists_projection_mul_eq_smul_of_isOpen_singleton chi hchi
  refine ⟨(p : A), hp.map D.subtype, ?_,
    corner_eq_smul_of_maximalAbelian D hD chi p hp hpd⟩
  intro hzero
  apply hpne
  apply Subtype.ext
  exact hzero

end Representation

end MathlibAnnex.Analysis.CStarAlgebra
