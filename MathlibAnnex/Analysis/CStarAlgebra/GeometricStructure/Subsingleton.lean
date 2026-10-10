/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

public import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.StarAlgEquiv
public import MathlibAnnex.Analysis.Normed.GeometricStructure.Separation
public import Mathlib.Analysis.CStarAlgebra.Hom

/-! # The zero-algebra boundary of geometric structure homeomorphisms

These declarations have no bounded-operator-model hypothesis.
They are preserved from the R43 author source without changes to statements or proofs.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w z

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {B : Type v} [NonUnitalCStarAlgebra B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type z} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Geometric separation discharges the target zero branch without requiring
a target model or choosing a nonexistent geometric point. -/
private theorem subsingleton_of_geometricStructure_homeomorph [Subsingleton A]
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B)) : Subsingleton B := by
  classical
  letI : IsEmpty (NormedSpace.GeometricStructureSpace ℂ A) :=
    NormedSpace.isEmpty_geometricStructureSpace_of_subsingleton ℂ A
  have hzero : ∀ b : B, b = 0 := by
    intro b
    by_contra hb
    obtain ⟨I, _hI⟩ := NormedSpace.exists_geometricStructureSpace_notMem ℂ B hb
    exact isEmptyElim (e.toEquiv.symm I)
  exact ⟨fun b c => (hzero b).trans (hzero c).symm⟩

/-- A full geometric-structure homeomorphism preserves the zero/nonzero
boundary, independently of any bounded-operator-model assumption. -/
theorem subsingleton_iff_of_geometricStructure_homeomorph
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B)) : Subsingleton A ↔ Subsingleton B := by
  constructor
  · intro hA
    letI : Subsingleton A := hA
    exact subsingleton_of_geometricStructure_homeomorph e
  · intro hB
    letI : Subsingleton B := hB
    exact subsingleton_of_geometricStructure_homeomorph e.symm

/-- The zero branch produces the actual unique star equivalence between the
two zero algebras. The target is proved zero from geometric separation. -/
theorem nonempty_starAlgEquiv_of_geometricStructure_homeomorph_of_subsingleton
    [Subsingleton A]
    (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B)) : Nonempty (A ≃⋆ₐ[ℂ] B) := by
  letI : Subsingleton B := subsingleton_of_geometricStructure_homeomorph e
  exact ⟨{
    toFun := fun _ => 0
    invFun := fun _ => 0
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _
    map_add' := fun _ _ => Subsingleton.elim _ _
    map_mul' := fun _ _ => Subsingleton.elim _ _
    map_star' := fun _ => Subsingleton.elim _ _
    map_smul' := fun _ _ => Subsingleton.elim _ _ }⟩

end MathlibAnnex.Analysis.CStarAlgebra
