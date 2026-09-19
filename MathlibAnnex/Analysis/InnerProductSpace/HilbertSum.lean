import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
# Bounded diagonal maps on dependent Hilbert sums

This uses Mathlib's genuine dependent `lp E 2`, so neither the index type nor
the family of Hilbert spaces is replaced by a finite or constant family.
-/

set_option autoImplicit false

open scoped ENNReal lp

namespace MathlibAnnex.Analysis.InnerProductSpace

universe u v w

variable {I : Type u} {E : I → Type v} {F : I → Type w}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]

/-- The dependent Hilbert direct sum of a family. -/
abbrev HilbertSum (E : I → Type v) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] :=
  lp E 2

/-- A uniformly bounded family acts diagonally on the dependent Hilbert sum. -/
noncomputable def diagonal (T : ∀ i, E i →L[ℂ] F i) (C : ℝ)
    (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) :
    HilbertSum E →L[ℂ] HilbertSum F :=
  lp.mapCLM 2 T hC hT

@[simp]
theorem diagonal_apply (T : ∀ i, E i →L[ℂ] F i) (C : ℝ)
    (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C)
    (x : HilbertSum E) (i : I) :
    diagonal T C hC hT x i = T i (x i) :=
  rfl

theorem norm_diagonal_le (T : ∀ i, E i →L[ℂ] F i) (C : ℝ)
    (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) :
    ‖diagonal T C hC hT‖ ≤ C :=
  lp.norm_mapCLM_le 2 T hC hT

/-- A family of fiberwise unitaries gives a unitary between the two dependent
Hilbert sums. -/
noncomputable def diagonalLinearIsometryEquiv
    (U : ∀ i, E i ≃ₗᵢ[ℂ] F i) : HilbertSum E ≃ₗᵢ[ℂ] HilbertSum F := by
  let f : HilbertSum E →L[ℂ] HilbertSum F :=
    diagonal (fun i ↦ (U i : E i →L[ℂ] F i)) 1 zero_le_one
      (fun i ↦ (U i).toLinearIsometry.norm_toContinuousLinearMap_le)
  let g : HilbertSum F →L[ℂ] HilbertSum E :=
    diagonal (fun i ↦ ((U i).symm : F i →L[ℂ] E i)) 1 zero_le_one
      (fun i ↦ (U i).symm.toLinearIsometry.norm_toContinuousLinearMap_le)
  have hgf (x : HilbertSum E) : g (f x) = x := by
    apply lp.ext
    funext i
    exact (U i).symm_apply_apply (x i)
  have hfg (y : HilbertSum F) : f (g y) = y := by
    apply lp.ext
    funext i
    exact (U i).apply_symm_apply (y i)
  have hfNorm : ‖f‖ ≤ 1 :=
    norm_diagonal_le _ _ zero_le_one
      (fun i ↦ (U i).toLinearIsometry.norm_toContinuousLinearMap_le)
  have hgNorm : ‖g‖ ≤ 1 :=
    norm_diagonal_le _ _ zero_le_one
      (fun i ↦ (U i).symm.toLinearIsometry.norm_toContinuousLinearMap_le)
  have hfIso : Isometry f := by
    rw [AddMonoidHomClass.isometry_iff_norm]
    intro x
    apply le_antisymm
    · simpa using f.le_of_opNorm_le hfNorm x
    · have hgx := g.le_of_opNorm_le hgNorm (f x)
      rw [hgf] at hgx
      simpa using hgx
  let w : HilbertSum E →ₗᵢ[ℂ] HilbertSum F :=
    f.toLinearMap.toLinearIsometry hfIso
  exact LinearIsometryEquiv.ofSurjective w fun y ↦ ⟨g y, hfg y⟩

@[simp]
theorem diagonalLinearIsometryEquiv_apply
    (U : ∀ i, E i ≃ₗᵢ[ℂ] F i) (x : HilbertSum E) (i : I) :
    diagonalLinearIsometryEquiv U x i = U i (x i) :=
  rfl

/-- Taking adjoints commutes with forming a bounded diagonal map.  Separate
bounds are allowed on the two sides because the resulting operator is
independent of the chosen bound witness. -/
theorem diagonal_adjoint
    [∀ i, CompleteSpace (E i)] [∀ i, CompleteSpace (F i)]
    (T : ∀ i, E i →L[ℂ] F i)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hT : ∀ i, ‖T i‖ ≤ C)
    (hTa : ∀ i, ‖ContinuousLinearMap.adjoint (T i)‖ ≤ D) :
    diagonal (fun i ↦ ContinuousLinearMap.adjoint (T i)) D hD hTa =
      ContinuousLinearMap.adjoint (diagonal T C hC hT) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [lp.inner_eq_tsum, ContinuousLinearMap.adjoint_inner_left,
    lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp only [diagonal_apply]
  exact ContinuousLinearMap.adjoint_inner_left (T i) (y i) (x i)

end MathlibAnnex.Analysis.InnerProductSpace
