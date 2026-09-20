import MathlibAnnex.Analysis.CStarAlgebra.GNS.Adapters
import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.KishimotoOzawaSakai

/-! Canonical GNS data supplied by an ordinary normalized positive state. -/

set_option autoImplicit false

open Set

namespace MathlibAnnex.CStarAlgebra

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The canonical vector of the GNS representation associated to a member of
`stateSpace`. -/
noncomputable def stateGNSVector (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) :
    (positiveLinearMapOfMemStateSpace phi hphi).GNS :=
  _root_.PositiveLinearMap.gnsCyclicVector (positiveLinearMapOfMemStateSpace phi hphi)

theorem norm_stateGNSVector (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) :
    ‖stateGNSVector phi hphi‖ = 1 :=
  _root_.PositiveLinearMap.norm_gnsCyclicVector _
    (positiveLinearMapOfMemStateSpace_one phi hphi)

/-- The original state is the vector functional of its canonical GNS vector. -/
theorem inner_gnsStarAlgHom_stateGNSVector
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) (a : A) :
    inner ℂ (stateGNSVector phi hphi)
      ((positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom a
        (stateGNSVector phi hphi)) = phi a := by
  exact _root_.PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom _ a

/-- The represented algebraic orbit of the canonical state vector is dense. -/
theorem denseRange_gnsStarAlgHom_stateGNSVector
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) :
    DenseRange (fun a : A ↦
      (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom a
        (stateGNSVector phi hphi)) :=
  _root_.PositiveLinearMap.denseRange_gnsStarAlgHom_apply_gnsCyclicVector _

/-- Complex-linearity probe for the state/GNS bridge. -/
theorem inner_gnsStarAlgHom_I_stateGNSVector
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) :
    inner ℂ (stateGNSVector phi hphi)
      ((positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom
        ((Complex.I : ℂ) • (1 : A)) (stateGNSVector phi hphi)) = Complex.I :=
  by
    rw [inner_gnsStarAlgHom_stateGNSVector]
    have hone : phi 1 = 1 := hphi.2
    simp [hone]

end MathlibAnnex.CStarAlgebra
