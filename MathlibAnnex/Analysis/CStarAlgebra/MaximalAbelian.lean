import Mathlib.Order.Zorn
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Maximal abelian star subalgebras

This file constructs maximal commutative unital star subalgebras by Zorn's
lemma and records that they are norm closed in a C-star algebra.
-/

set_option autoImplicit false

open Set
open scoped ComplexStarModule

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

variable {A : Type u} [CStarAlgebra A]

/-- A maximal abelian unital star subalgebra, expressed without installing a
global commutative-ring instance on its subtype. -/
def IsMaximalAbelian (D : StarSubalgebra ℂ A) : Prop :=
  IsMulCommutative D ∧
    ∀ E : StarSubalgebra ℂ A, IsMulCommutative E → D ≤ E → E ≤ D

/-- Every unital C-star algebra has a maximal abelian star subalgebra. -/
theorem exists_maximalAbelian :
    ∃ D : StarSubalgebra ℂ A, IsMaximalAbelian D := by
  let S : Set (StarSubalgebra ℂ A) := {D | IsMulCommutative D}
  have hbot : (⊥ : StarSubalgebra ℂ A) ∈ S := by
    change IsMulCommutative (⊥ : StarSubalgebra ℂ A)
    refine IsMulCommutative.of_comm fun x y => ?_
    apply Subtype.ext
    obtain ⟨r, hr⟩ := x.2
    obtain ⟨s, hs⟩ := y.2
    change (x : A) * (y : A) = (y : A) * (x : A)
    rw [← hr, ← hs]
    exact Algebra.commutes r (algebraMap ℂ A s)
  obtain ⟨D, _hbotD, hD, hmax⟩ :=
    zorn_le_nonempty₀ S (fun c hcS hc y hy => by
      letI : Nonempty c := ⟨⟨y, hy⟩⟩
      let F : c → StarSubalgebra ℂ A := fun d => d.1
      have hdir : Directed (· ≤ ·) F := by
        intro i j
        by_cases hij' : i = j
        · subst j
          exact ⟨i, le_rfl, le_rfl⟩
        have hcoe : (i.1 : StarSubalgebra ℂ A) ≠ j.1 :=
          fun h => hij' (Subtype.ext h)
        rcases hc i.2 j.2 hcoe with hij | hji
        · exact ⟨j, hij, le_rfl⟩
        · exact ⟨i, le_rfl, hji⟩
      letI (d : c) : IsMulCommutative (F d) := hcS d.2
      refine ⟨⨆ d : c, F d, ?_, ?_⟩
      · change IsMulCommutative (↥(⨆ d : c, F d))
        exact StarSubalgebra.isMulCommutative_iSup hdir
      · intro z hz
        exact le_iSup F ⟨z, hz⟩)
      (⊥ : StarSubalgebra ℂ A) hbot
  exact ⟨D, hD, fun E hE hDE => hmax hE hDE⟩

/-- Maximal abelian star subalgebras of a C-star algebra are norm closed. -/
theorem IsMaximalAbelian.isClosed {D : StarSubalgebra ℂ A}
    (hD : IsMaximalAbelian D) : IsClosed (D : Set A) := by
  let E : StarSubalgebra ℂ A := D.topologicalClosure
  have hE : IsMulCommutative E := by
    letI : IsMulCommutative D := hD.1
    letI : CommRing E :=
      StarSubalgebra.commRingTopologicalClosure D (fun x y => mul_comm' x y)
    infer_instance
  have hED : E ≤ D := hD.2 E hE (StarSubalgebra.le_topologicalClosure D)
  have heq : E = D := le_antisymm hED (StarSubalgebra.le_topologicalClosure D)
  rw [← heq]
  exact StarSubalgebra.isClosed_topologicalClosure D

/-- A self-adjoint element commuting with a maximal abelian star subalgebra
belongs to that subalgebra. -/
theorem IsMaximalAbelian.mem_of_isSelfAdjoint_of_commute
    {D : StarSubalgebra ℂ A} (hD : IsMaximalAbelian D)
    {x : A} (hx : IsSelfAdjoint x)
    (hcomm : ∀ d : D, x * (d : A) = (d : A) * x) : x ∈ D := by
  let S : Set A := insert x (D : Set A)
  have hpair : ∀ y ∈ S, ∀ z ∈ S, y * z = z * y := by
    intro y hy z hz
    change y = x ∨ y ∈ D at hy
    change z = x ∨ z ∈ D at hz
    rcases hy with rfl | hy <;> rcases hz with rfl | hz
    · rfl
    · exact hcomm ⟨z, hz⟩
    · exact (hcomm ⟨y, hy⟩).symm
    · letI : IsMulCommutative D := hD.1
      exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : D) (⟨z, hz⟩ : D))
  have hstarS : ∀ y ∈ S, star y ∈ S := by
    intro y hy
    change y = x ∨ y ∈ D at hy
    change star y = x ∨ star y ∈ D
    rcases hy with rfl | hy
    · exact Or.inl hx.star_eq
    · exact Or.inr (star_mem hy)
  let E : StarSubalgebra ℂ A := StarAlgebra.adjoin ℂ S
  have hE : IsMulCommutative E :=
    StarAlgebra.isMulCommutative_adjoin ℂ hpair
      (fun y hy z hz => hpair y hy (star z) (hstarS z hz))
  have hDE : D ≤ E := by
    intro d hd
    exact StarAlgebra.subset_adjoin ℂ S (show (d : A) ∈ S from Or.inr hd)
  have hED : E ≤ D := hD.2 E hE hDE
  exact hED (StarAlgebra.subset_adjoin ℂ S (show x ∈ S from Or.inl rfl))

/-- A maximal abelian star subalgebra equals its commutant: no
self-adjointness assumption on the commuting element is needed. -/
theorem IsMaximalAbelian.mem_of_commute
    {D : StarSubalgebra ℂ A} (hD : IsMaximalAbelian D)
    {x : A} (hcomm : ∀ d : D, x * (d : A) = (d : A) * x) : x ∈ D := by
  have hxcomm (d : D) : Commute x (d : A) := hcomm d
  have hstarcomm (d : D) : Commute (star x) (d : A) := by
    have h := hxcomm (star d)
    change Commute x (star (d : A)) at h
    exact h.star_left
  have hrcomm (d : D) : (ℜ x : A) * (d : A) = (d : A) * (ℜ x : A) := by
    rw [realPart_apply_coe]
    exact ((hxcomm d).add_left (hstarcomm d)).smul_left (2 : ℝ)⁻¹
  have hicomm (d : D) : (ℑ x : A) * (d : A) = (d : A) * (ℑ x : A) := by
    rw [imaginaryPart_apply_coe]
    exact (((hxcomm d).sub_left (hstarcomm d)).smul_left (2 : ℝ)⁻¹).smul_left (-Complex.I)
  have hr : (ℜ x : A) ∈ D :=
    hD.mem_of_isSelfAdjoint_of_commute (ℜ x).property hrcomm
  have hi : (ℑ x : A) ∈ D :=
    hD.mem_of_isSelfAdjoint_of_commute (ℑ x).property hicomm
  rw [← realPart_add_I_smul_imaginaryPart x]
  exact D.add_mem hr (D.smul_mem hi Complex.I)

end MathlibAnnex.Analysis.CStarAlgebra
