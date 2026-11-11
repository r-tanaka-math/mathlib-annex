/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Support
import MathlibAnnex.Algebra.Star.ProjectionEquivalence

/-!
# Polar decomposition inside a von Neumann algebra

The partial isometry is constructed by extending the isometry
`|x| ξ ↦ x ξ` from the range of `|x|` to its closure, and setting it
equal to zero on the orthogonal complement. Commutation is first proved
on the range of `|x|`, then extended by continuity. The bicommutant
criterion therefore puts the witness in the specified algebra.

No dimension, countability, separability, or closed-range hypothesis is
imposed on the represented operator.
-/

set_option autoImplicit false
noncomputable section

open ContinuousLinearMap
open scoped CStarAlgebra

namespace VonNeumannAlgebra

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Equality after multiplication by an operator extends to the
projection onto its closed range. -/
private theorem mul_closed_range_projection_eq
    {S T A : H →L[ℂ] H} (h : S * A = T * A) :
    S * A.range.topologicalClosure.starProjection =
      T * A.range.topologicalClosure.starProjection := by
  have hcl : closure (Set.range A) ⊆ {ξ : H | S ξ = T ξ} := by
    apply closure_minimal
    · rintro ξ ⟨η, rfl⟩
      exact congrArg (fun B : H →L[ℂ] H ↦ B η) h
    · exact isClosed_eq S.continuous T.continuous
  ext ξ
  exact hcl (A.range.topologicalClosure.starProjection_apply_mem ξ)

/-- Equal star-squares give an isometry between the represented ranges,
extended by zero off the closed range of the second operator. -/
private theorem exists_range_isometry (T A : H →L[ℂ] H)
    (hsquare : star A * A = star T * T) :
    ∃ V : H →L[ℂ] H,
      V * A = T ∧
      V * A.range.topologicalClosure.starProjection = V ∧
      star V * V = A.range.topologicalClosure.starProjection := by
  let U : Submodule ℂ H := A.range.topologicalClosure
  let e : H →ₗ[ℂ] U := A.toLinearMap.codRestrict U
    (fun ξ ↦ Submodule.le_topologicalClosure _ ⟨ξ, rfl⟩)
  have he_dense : DenseRange e := by
    rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
    change closure (Set.range A) ⊆ closure (Set.range A)
    exact subset_rfl
  have hnorm : ∀ ξ : H, ‖T.toLinearMap ξ‖ = ‖e ξ‖ := by
    intro ξ
    change ‖T ξ‖ = ‖A ξ‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    have hcomp : A.adjoint ∘L A = T.adjoint ∘L T := by
      simpa only [ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.mul_def] using hsquare
    rw [T.apply_norm_sq_eq_inner_adjoint_left,
      A.apply_norm_sq_eq_inner_adjoint_left, hcomp]
  let j : U →ₗᵢ[ℂ] H := T.toLinearMap.extendOfIsometry he_dense hnorm
  let V : H →L[ℂ] H := j.toContinuousLinearMap ∘L U.orthogonalProjectionOnto
  have hVA : V * A = T := by
    ext ξ
    have heξ : U.orthogonalProjectionOnto (A ξ) = e ξ := by
      apply Subtype.ext
      change U.starProjection (A ξ) = A ξ
      exact Submodule.starProjection_eq_self_iff.2
        (Submodule.le_topologicalClosure _ ⟨ξ, rfl⟩)
    change j (U.orthogonalProjectionOnto (A ξ)) = T ξ
    rw [heξ]
    exact T.toLinearMap.extendOfIsometry_eq he_dense hnorm ξ
  have hVP : V * U.starProjection = V := by
    ext ξ
    change j (U.orthogonalProjectionOnto (U.starProjection ξ)) =
      j (U.orthogonalProjectionOnto ξ)
    congr 1
    apply Subtype.ext
    change U.starProjection (U.starProjection ξ) = U.starProjection ξ
    exact congrArg (fun B : H →L[ℂ] H ↦ B ξ)
      (isStarProjection_starProjection (U := U)).isIdempotentElem.eq
  have hVV : star V * V = U.starProjection := by
    calc
      star V * V =
          U.subtypeL ∘L
            ((j.toContinuousLinearMap.adjoint ∘L j.toContinuousLinearMap) ∘L
              U.orthogonalProjectionOnto) := by
        dsimp only [V]
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
          ContinuousLinearMap.adjoint_comp, Submodule.adjoint_orthogonalProjectionOnto]
        simp only [U, ContinuousLinearMap.comp_assoc]
      _ = U.subtypeL ∘L U.orthogonalProjectionOnto := by
        rw [j.adjoint_comp_self]
        rfl
      _ = U.starProjection := rfl
  exact ⟨V, hVA, hVP, hVV⟩

/-- The left support of the absolute value is the right support of the
original element. -/
theorem leftSupport_abs (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra) :
    leftSupport M (CFC.abs x) = rightSupport M x := by
  have ha : IsSelfAdjoint (CFC.abs x) := (CFC.abs_nonneg x).isSelfAdjoint
  have hsquare : star (CFC.abs x) * CFC.abs x = star x * x := by
    rw [ha.star_eq, CFC.abs_mul_abs]
  calc
    leftSupport M (CFC.abs x) = rightSupport M (CFC.abs x) := by
      rw [rightSupport, ha.star_eq]
    _ = rightSupport M (star (CFC.abs x) * CFC.abs x) :=
      (rightSupport_star_mul_self M (CFC.abs x)).symm
    _ = rightSupport M (star x * x) := by rw [hsquare]
    _ = rightSupport M x := rightSupport_star_mul_self M x

/-- Polar decomposition with a witness in the specified von Neumann
algebra. The initial and final projections are the internal right and
left supports. -/
theorem exists_polar_decomposition (M : VonNeumannAlgebra H)
    (x : M.toStarSubalgebra) :
    ∃ v : M.toStarSubalgebra,
      IsPartialIsometry v ∧
      v * CFC.abs x = x ∧
      star v * v = rightSupport M x ∧
      v * star v = leftSupport M x := by
  let a : M.toStarSubalgebra := CFC.abs x
  let A : H →L[ℂ] H := a
  let T : H →L[ℂ] H := x
  let P : H →L[ℂ] H := A.range.topologicalClosure.starProjection
  have ha : IsSelfAdjoint a := (CFC.abs_nonneg x).isSelfAdjoint
  have hsquare : star a * a = star x * x := by
    change star (CFC.abs x) * CFC.abs x = star x * x
    rw [ha.star_eq, CFC.abs_mul_abs]
  have hsquare_ambient : star A * A = star T * T :=
    congrArg (fun z : M.toStarSubalgebra ↦ (z : H →L[ℂ] H)) hsquare
  obtain ⟨V, hVA, hVP, hVV⟩ := exists_range_isometry T A hsquare_ambient
  have hPmem : P ∈ M := (leftSupport M a).property
  have hVmem : V ∈ M := by
    rw [← M.commutant_commutant, mem_commutant_iff]
    intro y hy
    have hTy : T * y = y * T := (mem_commutant_iff.1 hy) x x.property
    have hAy : A * y = y * A := (mem_commutant_iff.1 hy) a a.property
    have hPy : P * y = y * P := (mem_commutant_iff.1 hy) P hPmem
    have hmul : (y * V) * A = (V * y) * A := by
      calc
        (y * V) * A = y * T := by rw [mul_assoc, hVA]
        _ = T * y := hTy.symm
        _ = V * (A * y) := by rw [← hVA, mul_assoc]
        _ = V * (y * A) := by rw [hAy]
        _ = (V * y) * A := (mul_assoc _ _ _).symm
    have heq : (y * V) * P = (V * y) * P :=
      mul_closed_range_projection_eq hmul
    calc
      y * V = (y * V) * P := by rw [mul_assoc, hVP]
      _ = (V * y) * P := heq
      _ = V * y := by rw [mul_assoc, ← hPy, ← mul_assoc, hVP]
  let v : M.toStarSubalgebra := ⟨V, hVmem⟩
  have hv : IsPartialIsometry v := by
    change v * star v * v = v
    apply Subtype.ext
    change V * star V * V = V
    rw [mul_assoc, hVV, hVP]
  have hva : v * a = x := Subtype.ext hVA
  have hinitial : star v * v = leftSupport M a := Subtype.ext hVV
  have hleft : leftSupport M x * v = v := by
    apply Subtype.ext
    have hmul : ((leftSupport M x : H →L[ℂ] H) * V) * A = V * A := by
      rw [mul_assoc, hVA]
      exact congrArg (fun z : M.toStarSubalgebra ↦ (z : H →L[ℂ] H))
        (leftSupport_mul M x)
    have heq := mul_closed_range_projection_eq hmul
    change (leftSupport M x : H →L[ℂ] H) * V = V
    simpa only [mul_assoc, hVP] using heq
  have hfinal : v * star v = leftSupport M x := by
    apply le_antisymm
    · apply (hv.isStarProjection_mul_star_self.le_iff_mul_eq_right
        (isStarProjection_leftSupport M x)).2
      rw [← mul_assoc, hleft]
    · apply (leftSupport_le_iff M x hv.isStarProjection_mul_star_self).2
      calc
        (v * star v) * x = (v * star v) * (v * a) := by rw [hva]
        _ = (v * star v * v) * a := by simp only [mul_assoc]
        _ = x := by rw [hv.mul_star_self_mul, hva]
  refine ⟨v, hv, hva, ?_, hfinal⟩
  calc
    star v * v = leftSupport M a := hinitial
    _ = rightSupport M x := leftSupport_abs M x

/-- Right and left support projections are equivalent using an internal
partial isometry. -/
theorem murrayVonNeumannEquivalent_supports (M : VonNeumannAlgebra H)
    (x : M.toStarSubalgebra) :
    MurrayVonNeumannEquivalent (rightSupport M x) (leftSupport M x) := by
  obtain ⟨v, hv, _, hi, hf⟩ := exists_polar_decomposition M x
  exact ⟨isStarProjection_rightSupport M x,
    isStarProjection_leftSupport M x, v, hv, hi, hf⟩

end VonNeumannAlgebra
