/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Basic
import MathlibAnnex.Algebra.Star.PartialIsometry

/-!
# Internal support projections

The left support is the projection onto the closure of the represented
range. Range invariance under every operator in the commutant puts this
projection back in the given von Neumann algebra. The right support is the
left support of the adjoint. Their universal properties characterize the
least left and right projection identities for an element.
-/

set_option autoImplicit false
noncomputable section

open ContinuousLinearMap
open scoped CStarAlgebra

namespace VonNeumannAlgebra

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The left support, as an element of the specified algebra. -/
def leftSupport (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra) :
    M.toStarSubalgebra :=
  ⟨(x : H →L[ℂ] H).range.topologicalClosure.starProjection, by
    apply starProjection_mem
    intro y hy
    apply Submodule.topologicalClosure_mem_invtSubmodule
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    rintro ξ ⟨η, rfl⟩
    refine ⟨y η, ?_⟩
    exact congrArg (fun a : H →L[ℂ] H ↦ a η)
      ((mem_commutant_iff).1 hy x x.property)⟩

/-- The constructed left support is a star projection in `M`. -/
theorem isStarProjection_leftSupport (M : VonNeumannAlgebra H)
    (x : M.toStarSubalgebra) : IsStarProjection (leftSupport M x) := by
  have h := isStarProjection_starProjection
    (U := (x : H →L[ℂ] H).range.topologicalClosure)
  constructor
  · apply Subtype.ext
    exact h.isIdempotentElem.eq
  · apply Subtype.ext
    exact h.isSelfAdjoint.star_eq

/-- The range of the left support is exactly the closed range of `x`. -/
@[simp]
theorem range_leftSupport (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra) :
    (leftSupport M x : H →L[ℂ] H).range = (x : H →L[ℂ] H).range.topologicalClosure :=
  Submodule.range_starProjection _

/-- The left support acts identically on `x`. -/
@[simp]
theorem leftSupport_mul (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra) :
    leftSupport M x * x = x := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro ξ
  change (x : H →L[ℂ] H).range.topologicalClosure.starProjection
    ((x : H →L[ℂ] H) ξ) = (x : H →L[ℂ] H) ξ
  apply Submodule.starProjection_eq_self_iff.2
  exact Submodule.le_topologicalClosure _ ⟨ξ, rfl⟩

/-- The left support is the least projection that is a left identity
for `x`. -/
theorem leftSupport_le_iff (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p) :
    leftSupport M x ≤ p ↔ p * x = x := by
  constructor
  · intro h
    have hps : p * leftSupport M x = leftSupport M x :=
      ((isStarProjection_leftSupport M x).le_iff_mul_eq_right hp).1 h
    calc
      p * x = p * (leftSupport M x * x) := by rw [leftSupport_mul]
      _ = (p * leftSupport M x) * x := (mul_assoc _ _ _).symm
      _ = x := by rw [hps, leftSupport_mul]
  · intro h
    apply (projection_le_iff_range_le M (isStarProjection_leftSupport M x) hp).2
    rw [range_leftSupport]
    apply Submodule.topologicalClosure_minimal
    · rintro ξ ⟨η, rfl⟩
      refine ⟨(x : H →L[ℂ] H) η, ?_⟩
      exact congrArg (fun a : M.toStarSubalgebra ↦ (a : H →L[ℂ] H) η) h
    · exact (hp.map M.toStarSubalgebra.subtype).isIdempotentElem.isClosed_range

/-- A projection is its own left support. -/
theorem leftSupport_projection (M : VonNeumannAlgebra H)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p) : leftSupport M p = p := by
  apply le_antisymm
  · exact (leftSupport_le_iff M p hp).2 hp.isIdempotentElem.eq
  · apply (projection_le_iff_range_le M hp (isStarProjection_leftSupport M p)).2
    rw [range_leftSupport]
    exact Submodule.le_topologicalClosure _

@[simp]
theorem leftSupport_zero (M : VonNeumannAlgebra H) : leftSupport M 0 = 0 :=
  leftSupport_projection M (IsStarProjection.zero _)

@[simp]
theorem leftSupport_one (M : VonNeumannAlgebra H) : leftSupport M 1 = 1 :=
  leftSupport_projection M (IsStarProjection.one _)

/-- The support is zero precisely for the zero element. -/
@[simp]
theorem leftSupport_eq_zero_iff (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra) :
    leftSupport M x = 0 ↔ x = 0 := by
  constructor
  · intro h
    simpa only [h, zero_mul] using (leftSupport_mul M x).symm
  · rintro rfl
    exact leftSupport_zero M

/-- The right support is the left support of the adjoint. -/
def rightSupport (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra) :
    M.toStarSubalgebra := leftSupport M (star x)

theorem isStarProjection_rightSupport (M : VonNeumannAlgebra H)
    (x : M.toStarSubalgebra) : IsStarProjection (rightSupport M x) :=
  isStarProjection_leftSupport M (star x)

@[simp]
theorem leftSupport_star (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra) :
    leftSupport M (star x) = rightSupport M x := rfl

@[simp]
theorem rightSupport_star (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra) :
    rightSupport M (star x) = leftSupport M x := by simp only [rightSupport, star_star]

/-- The range formula for the right support uses the adjoint range. -/
theorem range_rightSupport (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra) :
    (rightSupport M x : H →L[ℂ] H).range =
      (star (x : H →L[ℂ] H)).range.topologicalClosure :=
  range_leftSupport M (star x)

/-- Equivalently, the right support projects onto the orthogonal
complement of the kernel. -/
theorem range_rightSupport_eq_orthogonal_ker (M : VonNeumannAlgebra H)
    (x : M.toStarSubalgebra) :
    (rightSupport M x : H →L[ℂ] H).range = (x : H →L[ℂ] H).kerᗮ := by
  rw [range_rightSupport]
  simpa only [ContinuousLinearMap.star_eq_adjoint] using
    (x : H →L[ℂ] H).orthogonal_ker.symm

/-- The right support acts identically on `x`. -/
@[simp]
theorem mul_rightSupport (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra) :
    x * rightSupport M x = x := by
  have h := congrArg star (leftSupport_mul M (star x))
  simpa only [rightSupport, star_mul, star_star,
    (isStarProjection_leftSupport M (star x)).isSelfAdjoint.star_eq] using h

/-- Leastness of the right support among projection right identities. -/
theorem rightSupport_le_iff (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p) :
    rightSupport M x ≤ p ↔ x * p = x := by
  rw [rightSupport, leftSupport_le_iff M (star x) hp]
  constructor
  · intro h
    simpa only [star_mul, star_star, hp.isSelfAdjoint.star_eq] using congrArg star h
  · intro h
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star h

theorem rightSupport_projection (M : VonNeumannAlgebra H)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p) : rightSupport M p = p := by
  rw [rightSupport, hp.isSelfAdjoint.star_eq]
  exact leftSupport_projection M hp

@[simp]
theorem rightSupport_zero (M : VonNeumannAlgebra H) : rightSupport M 0 = 0 :=
  rightSupport_projection M (IsStarProjection.zero _)

@[simp]
theorem rightSupport_one (M : VonNeumannAlgebra H) : rightSupport M 1 = 1 :=
  rightSupport_projection M (IsStarProjection.one _)

@[simp]
theorem rightSupport_eq_zero_iff (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra) :
    rightSupport M x = 0 ↔ x = 0 := by
  rw [rightSupport, leftSupport_eq_zero_iff, star_eq_zero]

/-- Passing to the right support leaves the kernel unchanged. -/
theorem ker_rightSupport (M : VonNeumannAlgebra H) (x : M.toStarSubalgebra) :
    (rightSupport M x : H →L[ℂ] H).ker = (x : H →L[ℂ] H).ker := by
  have hrange : (star (x : H →L[ℂ] H)).range.topologicalClosure =
      (x : H →L[ℂ] H).kerᗮ := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (x : H →L[ℂ] H).orthogonal_ker.symm
  change (star (x : H →L[ℂ] H)).range.topologicalClosure.starProjection.ker = _
  rw [Submodule.ker_starProjection, hrange, Submodule.orthogonal_orthogonal]

/-- Equality of kernels gives equality of right supports. -/
theorem rightSupport_eq_of_ker_eq (M : VonNeumannAlgebra H)
    {x y : M.toStarSubalgebra}
    (h : (x : H →L[ℂ] H).ker = (y : H →L[ℂ] H).ker) :
    rightSupport M x = rightSupport M y := by
  apply Subtype.ext
  apply (ContinuousLinearMap.IsStarProjection.ext_iff
    ((isStarProjection_rightSupport M x).map M.toStarSubalgebra.subtype)
    ((isStarProjection_rightSupport M y).map M.toStarSubalgebra.subtype)).2
  change (rightSupport M x : H →L[ℂ] H).range = (rightSupport M y : H →L[ℂ] H).range
  rw [range_rightSupport_eq_orthogonal_ker, range_rightSupport_eq_orthogonal_ker, h]

/-- Taking a star-square leaves the right support unchanged. -/
theorem rightSupport_star_mul_self (M : VonNeumannAlgebra H)
    (x : M.toStarSubalgebra) : rightSupport M (star x * x) = rightSupport M x := by
  apply rightSupport_eq_of_ker_eq
  change (star (x : H →L[ℂ] H) * (x : H →L[ℂ] H)).ker = (x : H →L[ℂ] H).ker
  simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] using
    (x : H →L[ℂ] H).ker_adjoint_comp_self

/-- For a partial isometry the left support is its final projection. -/
theorem leftSupport_eq_final (M : VonNeumannAlgebra H)
    (v : M.toStarSubalgebra) (hv : IsPartialIsometry v) :
    leftSupport M v = v * star v := by
  apply le_antisymm
  · exact (leftSupport_le_iff M v hv.isStarProjection_mul_star_self).2
      hv.mul_star_self_mul
  · apply (hv.isStarProjection_mul_star_self.le_iff_mul_eq_right
      (isStarProjection_leftSupport M v)).2
    rw [← mul_assoc, leftSupport_mul]

/-- For a partial isometry the right support is its initial projection. -/
theorem rightSupport_eq_initial (M : VonNeumannAlgebra H)
    (v : M.toStarSubalgebra) (hv : IsPartialIsometry v) :
    rightSupport M v = star v * v := by
  simpa only [rightSupport, star_star] using leftSupport_eq_final M (star v) hv.star

end VonNeumannAlgebra
