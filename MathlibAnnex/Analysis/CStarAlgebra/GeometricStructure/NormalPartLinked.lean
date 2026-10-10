/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartSemilinear
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CoefficientProjective
import MathlibAnnex.Analysis.Normed.Module.DualKernelGeometry
import MathlibAnnex.Analysis.Normed.Module.DualKernelPair

/-!
# Linked coefficient kernels in the normal part

Every closure and every `Linked` in this file is computed in the subspace
`normalPart S` of the original GSS. No identification of this relation with
`Linked` on the whole GSS is used. The third point is an actual coefficient
kernel. In the converse direction an arbitrary normal point is represented
by a coefficient, so the rank-two obstruction applies to precisely this
subspace, not to all extreme functionals.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable [IsClosed (S : Set (H →L[ℂ] H))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))

/-- A general pair of nonzero coefficients has the same kernel exactly when
both projective vector lines agree. No normalization is needed. -/
theorem normalPartPoint_eq_iff_span_eq_and_span_eq
    (x₁ x₂ y₁ y₂ : H) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    normalPartPoint S hS x₁ y₁ hx₁ hy₁ = normalPartPoint S hS x₂ y₂ hx₂ hy₂ ↔
      Submodule.span ℂ {x₁} = Submodule.span ℂ {x₂} ∧
      Submodule.span ℂ {y₁} = Submodule.span ℂ {y₂} := by
  rw [← NonUnitalCStarRepresentation.ker_matrixCoefficient_eq_iff_span_eq_and_span_eq
    (NonUnitalStarSubalgebraClass.subtype S) hS hx₁ hx₂ hy₁ hy₂]
  constructor
  · intro h
    exact SetLike.coe_injective (congrArg (fun I : normalPart S => I.val.val) h)
  · intro h
    exact Subtype.ext (Subtype.ext (congrArg (fun P : Submodule ℂ S => (P : Set S)) h))

/-- With source fixed, distinct points admit a third NORMAL point in their
closure, namely the kernel with target `y₁ + y₂`. -/
theorem linked_normalPartPoint_right (x y₁ y₂ : H)
    (hx : x ≠ 0) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Linked
      (normalPartPoint S hS x y₁ hx hy₁) (normalPartPoint S hS x y₂ hx hy₂) := by
  classical
  by_cases heq : normalPartPoint S hS x y₁ hx hy₁ = normalPartPoint S hS x y₂ hx hy₂
  · exact Or.inl heq
  refine Or.inr ?_
  intro hclosed
  let pi := NonUnitalStarSubalgebraClass.subtype S
  let f := NonUnitalCStarRepresentation.matrixCoefficient pi x y₁
  let g := NonUnitalCStarRepresentation.matrixCoefficient pi x y₂
  have hf : f ≠ 0 := (NonUnitalCStarRepresentation.matrixCoefficient_ne_zero_iff
    pi hS x y₁).2 ⟨hx, hy₁⟩
  have hg : g ≠ 0 := (NonUnitalCStarRepresentation.matrixCoefficient_ne_zero_iff
    pi hS x y₂).2 ⟨hx, hy₂⟩
  have hne : (f : S → ℂ) ⁻¹' {0} ≠ (g : S → ℂ) ⁻¹' {0} := by
    intro h
    exact heq (Subtype.ext (Subtype.ext h))
  obtain ⟨hfg, hl, hr, hsub⟩ :=
    NormedSpace.add_dual_ne_zero_and_preimage_zero_ne_of_preimage_zero_ne hf hg hne
  have hsum : y₁ + y₂ ≠ 0 := by
    intro hz
    apply hfg
    ext a
    change inner ℂ y₁ ((a : H →L[ℂ] H) x) +
      inner ℂ y₂ ((a : H →L[ℂ] H) x) = 0
    rw [← inner_add_left, hz, inner_zero_left]
  let J := normalPartPoint S hS x (y₁ + y₂) hx hsum
  have hJ : J.val.val = ((f + g : StrongDual ℂ S) : S → ℂ) ⁻¹' {0} := by
    ext a
    change inner ℂ (y₁ + y₂) ((a : H →L[ℂ] H) x) = 0 ↔ _
    simp only [inner_add_left, Set.mem_preimage, Set.mem_singleton_iff,
      ContinuousLinearMap.add_apply, f, g,
      NonUnitalCStarRepresentation.matrixCoefficient_apply, pi,
      NonUnitalStarSubalgebraClass.subtype_apply]
  have hmem : J ∈ ((NormedSpace.geometricStructureClosure ℂ S).subspace
      (normalPart S)).closure {normalPartPoint S hS x y₁ hx hy₁,
        normalPartPoint S hS x y₂ hx hy₂} := by
    apply (mem_normalPart_closure_iff S _ J).2
    intro a ha
    rw [hJ]
    exact hsub ⟨ha (normalPartPoint S hS x y₁ hx hy₁) (by simp),
      ha (normalPartPoint S hS x y₂ hx hy₂) (by simp)⟩
  have hp := (((NormedSpace.geometricStructureClosure ℂ S).subspace
    (normalPart S)).isClosed_iff_closure_subset _).1 hclosed hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp
  · apply hl
    exact hJ.symm.trans (congrArg (fun I : normalPart S => I.val.val) hp)
  · apply hr
    exact hJ.symm.trans (congrArg (fun I : normalPart S => I.val.val) hp)

/-- The corresponding third-point argument with target fixed. -/
theorem linked_normalPartPoint_left (x₁ x₂ y : H)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hy : y ≠ 0) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Linked
      (normalPartPoint S hS x₁ y hx₁ hy) (normalPartPoint S hS x₂ y hx₂ hy) := by
  classical
  by_cases heq : normalPartPoint S hS x₁ y hx₁ hy = normalPartPoint S hS x₂ y hx₂ hy
  · exact Or.inl heq
  refine Or.inr ?_
  intro hclosed
  let pi := NonUnitalStarSubalgebraClass.subtype S
  let f := NonUnitalCStarRepresentation.matrixCoefficient pi x₁ y
  let g := NonUnitalCStarRepresentation.matrixCoefficient pi x₂ y
  have hf : f ≠ 0 := (NonUnitalCStarRepresentation.matrixCoefficient_ne_zero_iff
    pi hS x₁ y).2 ⟨hx₁, hy⟩
  have hg : g ≠ 0 := (NonUnitalCStarRepresentation.matrixCoefficient_ne_zero_iff
    pi hS x₂ y).2 ⟨hx₂, hy⟩
  have hne : (f : S → ℂ) ⁻¹' {0} ≠ (g : S → ℂ) ⁻¹' {0} := by
    intro h
    exact heq (Subtype.ext (Subtype.ext h))
  obtain ⟨hfg, hl, hr, hsub⟩ :=
    NormedSpace.add_dual_ne_zero_and_preimage_zero_ne_of_preimage_zero_ne hf hg hne
  have hsum : x₁ + x₂ ≠ 0 := by
    intro hz
    apply hfg
    ext a
    change inner ℂ y ((a : H →L[ℂ] H) x₁) +
      inner ℂ y ((a : H →L[ℂ] H) x₂) = 0
    rw [← inner_add_right, ← map_add, hz, map_zero, inner_zero_right]
  let J := normalPartPoint S hS (x₁ + x₂) y hsum hy
  have hJ : J.val.val = ((f + g : StrongDual ℂ S) : S → ℂ) ⁻¹' {0} := by
    ext a
    change inner ℂ y ((a : H →L[ℂ] H) (x₁ + x₂)) = 0 ↔ _
    simp only [map_add, inner_add_right, Set.mem_preimage, Set.mem_singleton_iff,
      ContinuousLinearMap.add_apply, f, g,
      NonUnitalCStarRepresentation.matrixCoefficient_apply, pi,
      NonUnitalStarSubalgebraClass.subtype_apply]
  have hmem : J ∈ ((NormedSpace.geometricStructureClosure ℂ S).subspace
      (normalPart S)).closure {normalPartPoint S hS x₁ y hx₁ hy,
        normalPartPoint S hS x₂ y hx₂ hy} := by
    apply (mem_normalPart_closure_iff S _ J).2
    intro a ha
    rw [hJ]
    exact hsub ⟨ha (normalPartPoint S hS x₁ y hx₁ hy) (by simp),
      ha (normalPartPoint S hS x₂ y hx₂ hy) (by simp)⟩
  have hp := (((NormedSpace.geometricStructureClosure ℂ S).subspace
    (normalPart S)).isClosed_iff_closure_subset _).1 hclosed hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp
  · exact hl (hJ.symm.trans (congrArg (fun I : normalPart S => I.val.val) hp))
  · exact hr (hJ.symm.trans (congrArg (fun I : normalPart S => I.val.val) hp))

/-- Two independent source lines and two independent target lines give a
closed pair in the normal part, not an assertion about the full GSS. -/
theorem isClosed_pair_normalPartPoint_of_span_ne
    (x₁ x₂ y₁ y₂ : H) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hX : Submodule.span ℂ {x₁} ≠ Submodule.span ℂ {x₂})
    (hY : Submodule.span ℂ {y₁} ≠ Submodule.span ℂ {y₂}) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).IsClosed
      {normalPartPoint S hS x₁ y₁ hx₁ hy₁, normalPartPoint S hS x₂ y₂ hx₂ hy₂} := by
  apply (((NormedSpace.geometricStructureClosure ℂ S).subspace
    (normalPart S)).isClosed_iff_closure_subset _).2
  intro I hI
  obtain ⟨z, w, hz, hw, rfl⟩ := exists_normalPartPoint_eq S hS I
  let pi := NonUnitalStarSubalgebraClass.subtype S
  let f := NonUnitalCStarRepresentation.matrixCoefficient pi x₁ y₁
  let g := NonUnitalCStarRepresentation.matrixCoefficient pi x₂ y₂
  let h := NonUnitalCStarRepresentation.matrixCoefficient pi z w
  have hh0 : h ≠ 0 := (NonUnitalCStarRepresentation.matrixCoefficient_ne_zero_iff
    pi hS z w).2 ⟨hz, hw⟩
  have hi : f.ker ⊓ g.ker ≤ h.ker := by
    intro a ha
    apply (mem_normalPart_closure_iff S _ _).1 hI a
    intro J hJ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hJ
    rcases hJ with rfl | rfl
    · exact ha.1
    · exact ha.2
  obtain ⟨a, b, hab⟩ :=
    (ContinuousLinearMap.inf_ker_le_ker_iff_exists_smul_add_smul f g h).1 hi
  have hzab := NonUnitalCStarRepresentation.eq_zero_or_eq_zero_of_matrixCoefficient_eq_smul_add_smul
    pi hS hx₁ hx₂ hy₁ hy₂ hX hY hab
  rcases hzab with ha | hb
  · have heq : h = b • g := by simpa only [ha, _root_.zero_smul ℂ f, zero_add] using hab
    have hb : b ≠ 0 := by intro hb; exact hh0 (by simpa only [hb, _root_.zero_smul ℂ g] using heq)
    have hker := (ContinuousLinearMap.ker_eq_ker_iff_exists_ne_zero_smul
      ((NonUnitalCStarRepresentation.matrixCoefficient_ne_zero_iff
        pi hS x₂ y₂).2 ⟨hx₂, hy₂⟩)).2 ⟨b, hb, heq⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    right
    exact Subtype.ext (Subtype.ext
      (congrArg (fun P : Submodule ℂ S => (P : Set S)) hker.symm))
  · have heq : h = a • f := by simpa only [hb, _root_.zero_smul ℂ g, add_zero] using hab
    have ha : a ≠ 0 := by intro ha; exact hh0 (by simpa only [ha, _root_.zero_smul ℂ f] using heq)
    have hker := (ContinuousLinearMap.ker_eq_ker_iff_exists_ne_zero_smul
      ((NonUnitalCStarRepresentation.matrixCoefficient_ne_zero_iff
        pi hS x₁ y₁).2 ⟨hx₁, hy₁⟩)).2 ⟨a, ha, heq⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    left
    exact Subtype.ext (Subtype.ext
      (congrArg (fun P : Submodule ℂ S => (P : Set S)) hker.symm))

/-- Lemma 6.10, with linear dependence expressed as equality of nonzero
projective lines. The equality branch of `Linked` is included. -/
theorem linked_normalPartPoint_iff_span_eq_or_span_eq
    (x₁ x₂ y₁ y₂ : H) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Linked
      (normalPartPoint S hS x₁ y₁ hx₁ hy₁) (normalPartPoint S hS x₂ y₂ hx₂ hy₂) ↔
      Submodule.span ℂ {x₁} = Submodule.span ℂ {x₂} ∨
      Submodule.span ℂ {y₁} = Submodule.span ℂ {y₂} := by
  classical
  constructor
  · intro h
    by_contra hne
    obtain ⟨hX, hY⟩ := not_or.mp hne
    rcases h with heq | hclosed
    · exact hX ((normalPartPoint_eq_iff_span_eq_and_span_eq S hS
        x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂).1 heq).1
    · exact hclosed (isClosed_pair_normalPartPoint_of_span_ne S hS
        x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂ hX hY)
  · rintro (hX | hY)
    · have heq : normalPartPoint S hS x₂ y₂ hx₂ hy₂ =
          normalPartPoint S hS x₁ y₂ hx₁ hy₂ :=
        (normalPartPoint_eq_iff_span_eq_and_span_eq S hS
          x₂ x₁ y₂ y₂ hx₂ hx₁ hy₂ hy₂).2 ⟨hX.symm, rfl⟩
      rw [heq]
      exact linked_normalPartPoint_right S hS x₁ y₁ y₂ hx₁ hy₁ hy₂
    · have heq : normalPartPoint S hS x₂ y₂ hx₂ hy₂ =
          normalPartPoint S hS x₂ y₁ hx₂ hy₁ :=
        (normalPartPoint_eq_iff_span_eq_and_span_eq S hS
          x₂ x₂ y₂ y₁ hx₂ hx₂ hy₂ hy₁).2 ⟨rfl, hY.symm⟩
      rw [heq]
      exact linked_normalPartPoint_left S hS x₁ x₂ y₁ hx₁ hx₂ hy₁

end MathlibAnnex.Analysis.CStarAlgebra
