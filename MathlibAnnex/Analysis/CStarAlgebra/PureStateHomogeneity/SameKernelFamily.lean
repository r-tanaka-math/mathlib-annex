import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.PureFamily
import MathlibAnnex.Analysis.CStarAlgebra.State.GNSKernel

/-! C05 controller source, UNBUILT: the invariant family is a GNS-kernel
fibre, not all pure states and not the scalar functional's nullspace. -/
set_option autoImplicit false
noncomputable section
namespace MathlibAnnex.CStarAlgebra
open MathlibAnnex.CStarAlgebra MathlibAnnex.Analysis.CStarAlgebra
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def sameKernelPureStates (I : Set A) : Set (A →L[ℂ] ℂ) :=
  {phi | IsPureState A phi ∧ stateGNSKernel phi = I}

theorem innerInvariantFamily_sameKernelPure (I : Set A) :
    InnerInvariantFamily (sameKernelPureStates I) where
  norm_le_one := fun phi hphi => pure_norm_le_one phi hphi.1
  pull_mem := by
    intro phi hphi u
    exact ⟨pull_pure phi hphi.1 u, (stateGNSKernel_pull phi u).trans hphi.2⟩

theorem sameKernelPure_kernel_eq {I : Set A}
    (phi psi : A →L[ℂ] ℂ) (hphi : phi ∈ sameKernelPureStates I)
    (hpsi : psi ∈ sameKernelPureStates I) :
    stateGNSKernel phi = stateGNSKernel psi := hphi.2.trans hpsi.2.symm

end MathlibAnnex.CStarAlgebra
