import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.KishimotoOzawaSakai
import MathlibAnnex.Analysis.CStarAlgebra.LocalPathTransport
import MathlibAnnex.Analysis.CStarAlgebra.PureState

/-!
# Inner invariance of the pure-state family

These are the first two fields of `FinitePathTransport`: norm bound and
closure under the pull convention `Ad(u*)`. The two path approximation
fields require separate mathematical suppliers.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.CStarAlgebra

open MathlibAnnex.CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem pull_mem_stateSpace (phi : A →L[ℂ] ℂ)
    (hphi : phi ∈ stateSpace A) (u : unitary A) :
    pull phi u ∈ stateSpace A := by
  constructor
  · intro a ha
    exact hphi.1 (innerAt u a) (map_nonneg (innerAt u) ha)
  · simpa using hphi.2

private noncomputable def pullLinearEquiv (u : unitary A) :
    (A →L[ℂ] ℂ) ≃ₗ[ℝ] (A →L[ℂ] ℂ) where
  toFun phi := pull phi u
  invFun phi := pull phi (star u)
  left_inv phi := by
    change pull (pull phi u) (star u) = phi
    rw [← pull_mul]
    simp
  right_inv phi := by
    change pull (pull phi (star u)) u = phi
    rw [← pull_mul]
    simp
  map_add' phi psi := by
    ext a
    rfl
  map_smul' r phi := by
    ext a
    rfl

theorem pull_pure (phi : A →L[ℂ] ℂ)
    (hphi : IsPureState A phi) (u : unitary A) :
    IsPureState A (pull phi u) := by
  let E := pullLinearEquiv (A := A) u
  have himage : E '' stateSpace A = stateSpace A := by
    ext psi
    constructor
    · rintro ⟨theta, htheta, rfl⟩
      exact pull_mem_stateSpace theta htheta u
    · intro hpsi
      refine ⟨E.symm psi, ?_, E.apply_symm_apply psi⟩
      exact pull_mem_stateSpace psi hpsi (star u)
  have h := image_extremePoints E (stateSpace A)
  have hmem : E phi ∈ E '' ((stateSpace A).extremePoints ℝ) :=
    ⟨phi, hphi, rfl⟩
  rw [h, himage] at hmem
  exact hmem

theorem pure_norm_le_one (phi : A →L[ℂ] ℂ)
    (hphi : IsPureState A phi) : ‖phi‖ ≤ 1 := by
  have hweak : StrongDual.toWeakDual phi ∈
      MathlibAnnex.Analysis.CStarAlgebra.weakStateSpace A := hphi.1
  simpa using
    (MathlibAnnex.Analysis.CStarAlgebra.norm_le_one_of_mem_weakStateSpace hweak)

theorem innerInvariantFamily_pure :
    InnerInvariantFamily (IsPureState A) where
  norm_le_one := fun phi hphi => pure_norm_le_one phi hphi
  pull_mem := fun phi hphi u => pull_pure phi hphi u

end MathlibAnnex.CStarAlgebra
