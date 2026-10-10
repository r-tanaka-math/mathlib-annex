/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.MatrixCoefficient

/-!
# Representations pulled back through a surjective nonunital star homomorphism

Surjectivity, not faithfulness and not a unitary lifting assertion, makes the
represented actions identical. The Hilbert universe is independent of both
algebra universes. No quotient norm or quotient algebra is postulated here.
-/

set_option autoImplicit false
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private noncomputable def pullbackContinuousMap (q : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun := q, map_add' := map_add q, map_smul' := map_smul q }
    1 (fun a => by
      change ‖q a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le q a)

/-- Pullback reflects nonzeroness because every element of the target is hit. -/
theorem isNonzero_comp_iff_of_surjective
    (pi : NonUnitalCStarRepresentation B H) (q : A →⋆ₙₐ[ℂ] B)
    (hq : Function.Surjective q) : IsNonzero (pi.comp q) ↔ pi.IsNonzero := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨q a, ha⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := hq b
    exact ⟨a, hb⟩

/-- A subspace reduces the pullback exactly when it reduces the original action. -/
theorem reduces_comp_iff_of_surjective
    (pi : NonUnitalCStarRepresentation B H) (q : A →⋆ₙₐ[ℂ] B)
    (hq : Function.Surjective q) (L : Submodule ℂ H) :
    Reduces (pi.comp q) L ↔ pi.Reduces L := by
  constructor
  · rintro ⟨hclosed, hred⟩
    refine ⟨hclosed, ?_⟩
    intro b x hx
    obtain ⟨a, rfl⟩ := hq b
    exact hred a x hx
  · rintro ⟨hclosed, hred⟩
    exact ⟨hclosed, fun a x hx => hred (q a) x hx⟩

/-- Surjective pullback preserves and reflects nonzero irreducibility. -/
theorem isIrreducible_comp_iff_of_surjective
    (pi : NonUnitalCStarRepresentation B H) (q : A →⋆ₙₐ[ℂ] B)
    (hq : Function.Surjective q) : IsIrreducible (pi.comp q) ↔ pi.IsIrreducible := by
  constructor
  · rintro ⟨hnz, hirr⟩
    refine ⟨(isNonzero_comp_iff_of_surjective pi q hq).1 hnz, ?_⟩
    intro L hL
    exact hirr L ((reduces_comp_iff_of_surjective pi q hq L).2 hL)
  · rintro ⟨hnz, hirr⟩
    refine ⟨(isNonzero_comp_iff_of_surjective pi q hq).2 hnz, ?_⟩
    intro L hL
    exact hirr L ((reduces_comp_iff_of_surjective pi q hq L).1 hL)

/-- The coefficient pullback is literally composition of continuous linear maps. -/
theorem matrixCoefficient_comp
    (pi : NonUnitalCStarRepresentation B H) (q : A →⋆ₙₐ[ℂ] B) (x y : H) :
    matrixCoefficient (pi.comp q) x y =
      (matrixCoefficient pi x y).comp (pullbackContinuousMap q) := by
  ext a
  rfl

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
