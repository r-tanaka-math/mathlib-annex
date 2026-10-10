/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.WeakOperatorDensity

/-!
# Unitary equivalence obstructs full joint weak-operator density

A unitary intertwiner imposes a closed equality between two matrix
coefficients. A tuple equal to the identity in the first coordinate and zero
in the second violates that equality on any nonzero vector. This proves the
exclusivity of the alternatives in the product-WOT model, without comparing
kernels, using irreducibility of a direct sum, or restricting dimension.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {I : Type v} {H : I → Type w}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- Two distinct, nonzero, unitarily equivalent coordinates preclude full
joint weak-operator density. The index type need not be finite and the
representations need not be irreducible for this obstruction. -/
theorem not_denseRange_pi_wot_of_unitaryEquivalent
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (i k : I) (hik : i ≠ k) (hi : (pi i).IsNonzero)
    (hequiv : (pi i).UnitaryEquivalent (pi k)) :
    ¬ DenseRange (fun a : A => fun j => ContinuousLinearMapWOT.ofCLM (pi j a)) := by
  classical
  letI : Nontrivial (H i) := nontrivial_of_isNonzero (pi i) hi
  obtain ⟨x, hx⟩ := exists_ne (0 : H i)
  obtain ⟨U, hU⟩ := hequiv
  let W := ∀ j, H j →WOT[ℂ] H j
  let f : W → ℂ := fun T => inner ℂ x (T i x)
  let g : W → ℂ := fun T => inner ℂ (U x) (T k (U x))
  have hf : Continuous f :=
    (ContinuousLinearMapWOT.continuous_dual_apply x (innerSL ℂ x)).comp (continuous_apply i)
  have hg : Continuous g :=
    (ContinuousLinearMapWOT.continuous_dual_apply (U x) (innerSL ℂ (U x))).comp
      (continuous_apply k)
  have hclosed : IsClosed {T : W | f T = g T} := isClosed_eq hf hg
  have hsource : Set.range (fun a : A => fun j => ContinuousLinearMapWOT.ofCLM (pi j a)) ⊆
      {T : W | f T = g T} := by
    rintro _ ⟨a, rfl⟩
    change inner ℂ x (pi i a x) = inner ℂ (U x) (pi k a (U x))
    rw [← hU a x]
    exact (U.inner_map_map x (pi i a x)).symm
  have hclosure := closure_minimal hsource hclosed
  intro hdense
  let T : W := fun j => ContinuousLinearMapWOT.ofCLM
    (if j = k then (0 : H j →L[ℂ] H j) else 1)
  have h := hclosure (hdense T)
  have hxx : inner ℂ x x = 0 := by
    change inner ℂ x (((if i = k then 0 else 1) : H i →L[ℂ] H i) x) =
      inner ℂ (U x) (((if k = k then 0 else 1) : H k →L[ℂ] H k) (U x)) at h
    simpa only [if_neg hik, if_pos rfl, ite_true, ContinuousLinearMap.one_apply,
      zero_apply, inner_zero_right] using h
  exact hx (inner_self_eq_zero.mp hxx)

/-- For a finite family of nonzero irreducible representations, joint
product-WOT density holds exactly when distinct members are inequivalent. -/
theorem denseRange_pi_wot_iff_pairwise_not_unitaryEquivalent [Fintype I]
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible) :
    DenseRange (fun a : A => fun i => ContinuousLinearMapWOT.ofCLM (pi i a)) ↔
      ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k) := by
  constructor
  · intro hdense i k hik hequiv
    exact not_denseRange_pi_wot_of_unitaryEquivalent pi i k hik (hirr i).1 hequiv hdense
  · exact denseRange_pi_wot_of_pairwise_not_unitaryEquivalent pi hirr

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
