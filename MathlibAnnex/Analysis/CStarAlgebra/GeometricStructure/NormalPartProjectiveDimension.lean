/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartProjectiveIncidence
import MathlibAnnex.LinearAlgebra.Projectivization.Dimension

/-!
# Submodule order maps and dimension from an actual normal-part finite homeomorphism

The point factors are the existing, jointly chosen factors of the given finite
homeomorphism. Their incidence iff is reversed to meet the hypothesis of
`Projectivization.submoduleOrderIsoOfFiniteSpan`. The resulting order maps act
on ALL algebraic submodules. No norm-closedness or semilinear realization is
part of this construction. Finite dimension is concluded only under a genuine
one-sided `Module.Finite` hypothesis; projective dimensions one and two need
no fundamental theorem of projective geometry.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped LinearAlgebra.Projectivization

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [IsClosed (S : Set (H →L[ℂ] H))] [IsClosed (T : Set (K →L[ℂ] K))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
variable (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
variable (e : ClosureSpace.FiniteHomeomorph
  ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
  ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)))

/-- The algebraic submodule order isomorphism of the actual first factor. -/
def normalPartFirstSubmoduleOrderIso : Submodule ℂ H ≃o Submodule ℂ K :=
  Projectivization.submoduleOrderIsoOfFiniteSpan
    (normalPartProjectiveFirstFactor S T hS hT e)
    (fun s hs p => ((normalPart_projective_factors_spec S T hS hT e).1 s hs p).symm)

/-- The second order isomorphism uses the second factor of the SAME factorization. -/
def normalPartSecondSubmoduleOrderIso : Submodule ℂ H ≃o Submodule ℂ K :=
  Projectivization.submoduleOrderIsoOfFiniteSpan
    (normalPartProjectiveSecondFactor S T hS hT e)
    (fun s hs p => ((normalPart_projective_factors_spec S T hS hT e).2.1 s hs p).symm)

/-- Forward evaluation of the first order map in actual projective coordinates. -/
theorem mem_projectivization_normalPartFirstSubmoduleOrderIso_iff
    (M : Submodule ℂ H) (q : ℙ ℂ K) :
    q ∈ (normalPartFirstSubmoduleOrderIso S T hS hT e M).projectivization ↔
      (normalPartProjectiveFirstFactor S T hS hT e).symm q ∈ M.projectivization :=
  Projectivization.mem_projectivization_submoduleOrderIsoOfFiniteSpan_iff
    (normalPartProjectiveFirstFactor S T hS hT e)
    (fun s hs p => ((normalPart_projective_factors_spec S T hS hT e).1 s hs p).symm)
    M q

/-- Forward evaluation of the second order map. -/
theorem mem_projectivization_normalPartSecondSubmoduleOrderIso_iff
    (M : Submodule ℂ H) (q : ℙ ℂ K) :
    q ∈ (normalPartSecondSubmoduleOrderIso S T hS hT e M).projectivization ↔
      (normalPartProjectiveSecondFactor S T hS hT e).symm q ∈ M.projectivization :=
  Projectivization.mem_projectivization_submoduleOrderIsoOfFiniteSpan_iff
    (normalPartProjectiveSecondFactor S T hS hT e)
    (fun s hs p => ((normalPart_projective_factors_spec S T hS hT e).2.1 s hs p).symm)
    M q

/-- The inverse first order map is a literal inverse image on nonzero rays. -/
theorem mem_symm_normalPartFirstSubmoduleOrderIso_iff
    (N : Submodule ℂ K) (x : H) (hx : x ≠ 0) :
    x ∈ (normalPartFirstSubmoduleOrderIso S T hS hT e).symm N ↔
      normalPartProjectiveFirstFactor S T hS hT e (Projectivization.mk ℂ x hx) ∈
        N.projectivization :=
  Projectivization.mem_symm_submoduleOrderIsoOfFiniteSpan_iff
    (normalPartProjectiveFirstFactor S T hS hT e)
    (fun s hs p => ((normalPart_projective_factors_spec S T hS hT e).1 s hs p).symm)
    N x hx

/-- The inverse second order map, including the correct factor direction. -/
theorem mem_symm_normalPartSecondSubmoduleOrderIso_iff
    (N : Submodule ℂ K) (x : H) (hx : x ≠ 0) :
    x ∈ (normalPartSecondSubmoduleOrderIso S T hS hT e).symm N ↔
      normalPartProjectiveSecondFactor S T hS hT e (Projectivization.mk ℂ x hx) ∈
        N.projectivization :=
  Projectivization.mem_symm_submoduleOrderIsoOfFiniteSpan_iff
    (normalPartProjectiveSecondFactor S T hS hT e)
    (fun s hs p => ((normalPart_projective_factors_spec S T hS hT e).2.1 s hs p).symm)
    N x hx

/-- No projective representative is needed to evaluate the first order map at zero. -/
@[simp]
theorem normalPartFirstSubmoduleOrderIso_bot :
    normalPartFirstSubmoduleOrderIso S T hS hT e ⊥ = ⊥ :=
  (normalPartFirstSubmoduleOrderIso S T hS hT e).map_bot

@[simp]
theorem normalPartSecondSubmoduleOrderIso_bot :
    normalPartSecondSubmoduleOrderIso S T hS hT e ⊥ = ⊥ :=
  (normalPartSecondSubmoduleOrderIso S T hS hT e).map_bot

@[simp]
theorem normalPartFirstSubmoduleOrderIso_top :
    normalPartFirstSubmoduleOrderIso S T hS hT e ⊤ = ⊤ :=
  (normalPartFirstSubmoduleOrderIso S T hS hT e).map_top

@[simp]
theorem normalPartSecondSubmoduleOrderIso_top :
    normalPartSecondSubmoduleOrderIso S T hS hT e ⊤ = ⊤ :=
  (normalPartSecondSubmoduleOrderIso S T hS hT e).map_top

/-- The first order map agrees with the already chosen projective point map on lines. -/
@[simp]
theorem normalPartFirstSubmoduleOrderIso_submodule (p : ℙ ℂ H) :
    normalPartFirstSubmoduleOrderIso S T hS hT e p.submodule =
      (normalPartProjectiveFirstFactor S T hS hT e p).submodule :=
  Projectivization.submoduleOrderIsoOfFiniteSpan_submodule
    (normalPartProjectiveFirstFactor S T hS hT e)
    (fun s hs p => ((normalPart_projective_factors_spec S T hS hT e).1 s hs p).symm)
    p

@[simp]
theorem normalPartSecondSubmoduleOrderIso_submodule (p : ℙ ℂ H) :
    normalPartSecondSubmoduleOrderIso S T hS hT e p.submodule =
      (normalPartProjectiveSecondFactor S T hS hT e p).submodule :=
  Projectivization.submoduleOrderIsoOfFiniteSpan_submodule
    (normalPartProjectiveSecondFactor S T hS hT e)
    (fun s hs p => ((normalPart_projective_factors_spec S T hS hT e).2.1 s hs p).symm)
    p

/-- The inverse first map recovers the line of the actual inverse point map. -/
@[simp]
theorem symm_normalPartFirstSubmoduleOrderIso_submodule (q : ℙ ℂ K) :
    (normalPartFirstSubmoduleOrderIso S T hS hT e).symm q.submodule =
      ((normalPartProjectiveFirstFactor S T hS hT e).symm q).submodule := by
  apply (normalPartFirstSubmoduleOrderIso S T hS hT e).injective
  rw [(normalPartFirstSubmoduleOrderIso S T hS hT e).apply_symm_apply,
    normalPartFirstSubmoduleOrderIso_submodule,
    Equiv.apply_symm_apply]

@[simp]
theorem symm_normalPartSecondSubmoduleOrderIso_submodule (q : ℙ ℂ K) :
    (normalPartSecondSubmoduleOrderIso S T hS hT e).symm q.submodule =
      ((normalPartProjectiveSecondFactor S T hS hT e).symm q).submodule := by
  apply (normalPartSecondSubmoduleOrderIso S T hS hT e).injective
  rw [(normalPartSecondSubmoduleOrderIso S T hS hT e).apply_symm_apply,
    normalPartSecondSubmoduleOrderIso_submodule,
    Equiv.apply_symm_apply]

/-- Literal nonzero-vector version of both line formulas. -/
theorem normalPart_submodule_order_isos_span_singleton (x : H) (hx : x ≠ 0) :
    normalPartFirstSubmoduleOrderIso S T hS hT e (ℂ ∙ x) =
        (normalPartProjectiveFirstFactor S T hS hT e (Projectivization.mk ℂ x hx)).submodule ∧
    normalPartSecondSubmoduleOrderIso S T hS hT e (ℂ ∙ x) =
        (normalPartProjectiveSecondFactor S T hS hT e (Projectivization.mk ℂ x hx)).submodule :=
  ⟨normalPartFirstSubmoduleOrderIso_submodule S T hS hT e (Projectivization.mk ℂ x hx),
    normalPartSecondSubmoduleOrderIso_submodule S T hS hT e (Projectivization.mk ℂ x hx)⟩

/-- The two order maps are tied to the original normal-part map, in one global
orientation. This statement is about lines, not a semilinear lift. -/
theorem normalPart_submodule_order_isos_evaluation :
    (∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      let q := (normalPartProjectivizationEquiv T hT).symm
        (e.toEquiv (normalPartProjectivizationEquiv S hS p))
      q.1.submodule = normalPartFirstSubmoduleOrderIso S T hS hT e p.1.submodule ∧
      q.2.submodule = normalPartSecondSubmoduleOrderIso S T hS hT e p.2.submodule) ∨
    (∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      let q := (normalPartProjectivizationEquiv T hT).symm
        (e.toEquiv (normalPartProjectivizationEquiv S hS p))
      q.1.submodule = normalPartSecondSubmoduleOrderIso S T hS hT e p.2.submodule ∧
      q.2.submodule = normalPartFirstSubmoduleOrderIso S T hS hT e p.1.submodule) := by
  rcases (normalPart_projective_factors_spec S T hS hT e).2.2 with h | h
  · refine Or.inl fun p => ?_
    dsimp only
    rw [h p, Equiv.symm_apply_apply]
    exact ⟨(normalPartFirstSubmoduleOrderIso_submodule S T hS hT e p.1).symm,
      (normalPartSecondSubmoduleOrderIso_submodule S T hS hT e p.2).symm⟩
  · refine Or.inr fun p => ?_
    dsimp only
    rw [h p, Equiv.symm_apply_apply]
    exact ⟨(normalPartSecondSubmoduleOrderIso_submodule S T hS hT e p.2).symm,
      (normalPartFirstSubmoduleOrderIso_submodule S T hS hT e p.1).symm⟩

/-- The actual inverse normal-part map recovers lines under the inverse order maps.
The point representatives are not asserted to be continuous functions of projective points. -/
theorem normalPart_submodule_order_isos_inverse_evaluation :
    (∀ q : (ℙ ℂ K) × (ℙ ℂ K),
      let p := (normalPartProjectivizationEquiv S hS).symm
        (e.toEquiv.symm (normalPartProjectivizationEquiv T hT q))
      p.1.submodule = (normalPartFirstSubmoduleOrderIso S T hS hT e).symm q.1.submodule ∧
      p.2.submodule = (normalPartSecondSubmoduleOrderIso S T hS hT e).symm q.2.submodule) ∨
    (∀ q : (ℙ ℂ K) × (ℙ ℂ K),
      let p := (normalPartProjectivizationEquiv S hS).symm
        (e.toEquiv.symm (normalPartProjectivizationEquiv T hT q))
      p.1.submodule = (normalPartFirstSubmoduleOrderIso S T hS hT e).symm q.2.submodule ∧
      p.2.submodule = (normalPartSecondSubmoduleOrderIso S T hS hT e).symm q.1.submodule) := by
  rcases normalPart_projective_factors_inverse_formula S T hS hT e with h | h
  · refine Or.inl fun q => ?_
    dsimp only
    rw [h q, Equiv.symm_apply_apply]
    exact ⟨(symm_normalPartFirstSubmoduleOrderIso_submodule S T hS hT e q.1).symm,
      (symm_normalPartSecondSubmoduleOrderIso_submodule S T hS hT e q.2).symm⟩
  · refine Or.inr fun q => ?_
    dsimp only
    rw [h q, Equiv.symm_apply_apply]
    exact ⟨(symm_normalPartFirstSubmoduleOrderIso_submodule S T hS hT e q.2).symm,
      (symm_normalPartSecondSubmoduleOrderIso_submodule S T hS hT e q.1).symm⟩

include hS hT e in
/-- One genuinely finite-dimensional side implies both are finite dimensional
and their dimensions agree. No dimension-three hypothesis is used. -/
theorem finite_and_finrank_eq_of_normalPart_finiteHomeomorph
    (hfinite : Module.Finite ℂ H ∨ Module.Finite ℂ K) :
    Module.Finite ℂ H ∧ Module.Finite ℂ K ∧ Module.finrank ℂ H = Module.finrank ℂ K :=
  Projectivization.finite_and_finrank_eq_of_finite_span
    (normalPartProjectiveFirstFactor S T hS hT e)
    (fun s hs p => ((normalPart_projective_factors_spec S T hS hT e).1 s hs p).symm)
    hfinite

include hS hT e in
/-- Finite dimensionality is reflected as well as preserved by the given normal-part map. -/
theorem finite_iff_of_normalPart_finiteHomeomorph :
    Module.Finite ℂ H ↔ Module.Finite ℂ K :=
  Projectivization.finite_iff_of_finite_span
    (normalPartProjectiveFirstFactor S T hS hT e)
    (fun s hs p => ((normalPart_projective_factors_spec S T hS hT e).1 s hs p).symm)

include hS hT e in
/-- The numerical equality is exposed only with an actual finite-dimensional hypothesis. -/
theorem finrank_eq_of_normalPart_finiteHomeomorph [Module.Finite ℂ H] :
    Module.finrank ℂ H = Module.finrank ℂ K :=
  (finite_and_finrank_eq_of_normalPart_finiteHomeomorph S T hS hT e
    (Or.inl inferInstance)).2.2

end MathlibAnnex.Analysis.CStarAlgebra
