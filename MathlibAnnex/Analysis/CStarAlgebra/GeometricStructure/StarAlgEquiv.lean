/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import MathlibAnnex.Analysis.Normed.GeometricStructure.Preserver

/-!
# Geometric-structure homeomorphisms induced by C-star equivalences

A nonunital complex C-star equivalence is an actual norm isometry, hence it
preserves Birkhoff--James orthogonality in both directions and induces the
corresponding full homeomorphism of geometric structure spaces.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uA uB uι uκ uH uK uI uJ

/-- A C-star equivalence preserves and reflects Birkhoff--James
orthogonality through its actual norm isometry. -/
theorem birkhoffJamesOrthogonal_starAlgEquiv_iff
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (E : A ≃⋆ₐ[ℂ] B) (x y : A) :
    NormedSpace.BirkhoffJamesOrthogonal ℂ (E x) (E y) ↔
      NormedSpace.BirkhoffJamesOrthogonal ℂ x y := by
  have hE := NonUnitalStarAlgHom.isometry E.toNonUnitalStarAlgHom E.injective
  have hnorm (a : A) : ‖E a‖ = ‖a‖ := by
    simpa only [StarAlgEquiv.toNonUnitalStarAlgHom_apply, map_zero, dist_zero_right]
      using hE.dist_eq a 0
  constructor
  · intro h a
    calc
      ‖x‖ = ‖E x‖ := (hnorm x).symm
      _ ≤ ‖E x + a • E y‖ := h a
      _ = ‖E (x + a • y)‖ := by rw [map_add, map_smul]
      _ = ‖x + a • y‖ := hnorm _
  · intro h a
    calc
      ‖E x‖ = ‖x‖ := hnorm x
      _ ≤ ‖x + a • y‖ := h a
      _ = ‖E (x + a • y)‖ := (hnorm _).symm
      _ = ‖E x + a • E y‖ := by rw [map_add, map_smul]

/-- The actual GSS homeomorphism induced by a non-unital C-star equivalence. -/
def geometricStructureHomeomorphOfStarAlgEquiv
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (E : A ≃⋆ₐ[ℂ] B) :
    ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B) :=
  NormedSpace.geometricStructureHomeomorphOfBirkhoffJames ℂ ℂ E.toEquiv
    (birkhoffJamesOrthogonal_starAlgEquiv_iff E)

@[simp]
theorem geometricStructureHomeomorphOfStarAlgEquiv_apply_val
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (E : A ≃⋆ₐ[ℂ] B) (I : NormedSpace.GeometricStructureSpace ℂ A) :
    ((geometricStructureHomeomorphOfStarAlgEquiv E).toEquiv I).val =
      E '' I.val := rfl

end MathlibAnnex.Analysis.CStarAlgebra
