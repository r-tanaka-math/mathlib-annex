import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Common fixed subspaces for arbitrary families of bounded operators. -/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.InnerProductSpace

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The common fixed subspace of an arbitrary family of bounded operators. -/
def commonFixedSubspace (Q : ι → H →L[ℂ] H) : Submodule ℂ H :=
  ⨅ i, (Q i - 1).ker

@[simp]
theorem mem_commonFixedSubspace_iff (Q : ι → H →L[ℂ] H) (x : H) :
    x ∈ commonFixedSubspace Q ↔ ∀ i, Q i x = x := by
  simp [commonFixedSubspace, sub_eq_zero]

/-- The common fixed subspace is closed, without any countability assumption. -/
theorem isClosed_commonFixedSubspace (Q : ι → H →L[ℂ] H) :
    IsClosed (commonFixedSubspace Q : Set H) := by
  rw [show (commonFixedSubspace Q : Set H) =
      ⋂ i, ((Q i - 1).ker : Set H) by
    ext x
    simp [commonFixedSubspace]]
  exact isClosed_iInter fun i ↦ (Q i - 1).isClosed_ker

/-- The same common fixed space bundled with its closedness proof. -/
def commonFixedClosedSubspace (Q : ι → H →L[ℂ] H) : ClosedSubmodule ℂ H where
  toSubmodule := commonFixedSubspace Q
  isClosed' := isClosed_commonFixedSubspace Q

/-- Orthogonal projection onto the common fixed space. -/
noncomputable instance instHasOrthogonalProjectionCommonFixedSubspace [CompleteSpace H]
    (Q : ι → H →L[ℂ] H) : (commonFixedSubspace Q).HasOrthogonalProjection := by
  let K := commonFixedClosedSubspace Q
  change K.toSubmodule.HasOrthogonalProjection
  infer_instance

/-- Orthogonal projection onto the common fixed space. -/
noncomputable def commonFixedProjection [CompleteSpace H] (Q : ι → H →L[ℂ] H) :
    H →L[ℂ] H :=
  (commonFixedSubspace Q).starProjection

variable [CompleteSpace H]

theorem commonFixedProjection_mem (Q : ι → H →L[ℂ] H) (x : H) :
    commonFixedProjection Q x ∈ commonFixedSubspace Q := by
  exact Submodule.starProjection_apply_mem _ _

theorem commonFixedProjection_apply_fixed (Q : ι → H →L[ℂ] H)
    (i : ι) (x : H) :
    Q i (commonFixedProjection Q x) = commonFixedProjection Q x :=
  (mem_commonFixedSubspace_iff Q _).mp (commonFixedProjection_mem Q x) i

theorem adjoint_commonFixedProjection (Q : ι → H →L[ℂ] H) :
    ContinuousLinearMap.adjoint (commonFixedProjection Q) = commonFixedProjection Q := by
  exact Submodule.starProjection_isSymmetric
    (commonFixedSubspace Q) |>.clm_adjoint_eq

theorem commonFixedProjection_idempotent (Q : ι → H →L[ℂ] H) :
    commonFixedProjection Q * commonFixedProjection Q = commonFixedProjection Q := by
  exact Submodule.isIdempotentElem_starProjection
    (commonFixedSubspace Q)

@[simp]
theorem commonFixedProjection_eq_self_iff (Q : ι → H →L[ℂ] H) (x : H) :
    commonFixedProjection Q x = x ↔ x ∈ commonFixedSubspace Q := by
  exact Submodule.starProjection_eq_self_iff

end MathlibAnnex.Analysis.InnerProductSpace
