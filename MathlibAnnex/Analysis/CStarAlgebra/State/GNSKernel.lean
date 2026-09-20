import MathlibAnnex.Analysis.CStarAlgebra.State.Ideal
import MathlibAnnex.Analysis.CStarAlgebra.State.VectorApproximation
import MathlibAnnex.Analysis.CStarAlgebra.LocalPathTransport

/-!
# An intrinsic, inner-invariant description of a GNS representation kernel

C05 controller-authored source, UNBUILT. The nullspace of the state itself
is NOT its GNS kernel. All right translates of the star-square are tested.
The dense-orbit proof below follows the already preserved State.Ideal proof,
but does not assume simplicity, an ideal supplied by a caller, or faithfulness.
-/
set_option autoImplicit false
noncomputable section
open Set
open scoped ComplexOrder InnerProduct
namespace MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- This definition is made for any functional; the representation-kernel
interpretation below requires a state. -/
def stateGNSKernel (phi : A →L[ℂ] ℂ) : Set A :=
  {a | ∀ b : A, phi (star (a * b) * (a * b)) = 0}

/-- Intrinsic criterion, proved against the actual GNS representation. -/
theorem mem_stateGNSKernel_iff
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) (a : A) :
    a ∈ stateGNSKernel phi ↔
      (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom a = 0 := by
  let f := positiveLinearMapOfMemStateSpace phi hphi
  let pi : Representation A f.GNS := f.gnsStarAlgHom
  let xi := f.gnsCyclicVector
  have hcoeff (b : A) :
      inner ℂ (pi (a * b) xi) (pi (a * b) xi) =
        phi (star (a * b) * (a * b)) := by
    calc
      _ = Representation.vectorFunctional pi xi
          (star (a * b) * (a * b)) :=
        (Representation.vectorFunctional_star_mul pi xi (a * b) (a * b)).symm
      _ = f (star (a * b) * (a * b)) :=
        PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom f _
      _ = _ := rfl
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro y
    have hdense : DenseRange (StarAlgHom.orbitMap pi xi) :=
      PositiveLinearMap.denseRange_gnsStarAlgHom_apply_gnsCyclicVector f
    exact hdense.induction_on y
      (isClosed_eq (pi a).continuous continuous_const) fun b => by
        have hz : pi (a * b) xi = 0 :=
          inner_self_eq_zero.mp ((hcoeff b).trans (h b))
        change pi a (pi b xi) = 0
        simpa only [map_mul, ContinuousLinearMap.mul_apply] using hz
  · intro h b
    have hz : pi (a * b) xi = 0 := by rw [map_mul, h]; simp
    rw [← hcoeff b, hz]
    simp

/-- The kernel is preserved by the SAME inner pull used by the alternating
path engine. This does not assert that the state itself is invariant. -/
theorem stateGNSKernel_pull (phi : A →L[ℂ] ℂ) (u : unitary A) :
    stateGNSKernel (pull phi u) = stateGNSKernel phi := by
  have hsquare (a b : A) :
      pull phi u (star (a * b) * (a * b)) =
        phi (star (a * (b * (u : A))) * (a * (b * (u : A)))) := by
    simp [pull_apply, innerAt, star_mul, mul_assoc]
  ext a
  constructor
  · intro h b
    have hb := h (b * star (u : A))
    rw [hsquare] at hb
    have hu : star (u : A) * (u : A) = 1 := u.property.1
    simpa only [mul_assoc, hu, mul_one] using hb
  · intro h b
    rw [hsquare]
    exact h (b * (u : A))

/-- Equality of intrinsic kernels is exactly equality of the two actual GNS
zero sets, even when the GNS Hilbert spaces are different. -/
theorem stateGNSKernel_eq_iff
    (phi psi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpsi : psi ∈ stateSpace A) :
    stateGNSKernel phi = stateGNSKernel psi ↔
      ∀ a : A,
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom a = 0 ↔
        (positiveLinearMapOfMemStateSpace psi hpsi).gnsStarAlgHom a = 0 := by
  constructor
  · intro h a
    rw [← mem_stateGNSKernel_iff phi hphi a,
      ← mem_stateGNSKernel_iff psi hpsi a, h]
  · intro h
    ext a
    rw [mem_stateGNSKernel_iff phi hphi a,
      mem_stateGNSKernel_iff psi hpsi a]
    exact h a

/-- The comparison state annihilates the reference representation kernel.
No implication 'primitive quotient is simple' occurs here. -/
theorem annihilates_gnsKernel_of_stateGNSKernel_eq
    (phi psi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpsi : psi ∈ stateSpace A)
    (hker : stateGNSKernel phi = stateGNSKernel psi) :
    ∀ a : A, (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom a = 0 →
      psi a = 0 := by
  intro a ha
  have hb := (stateGNSKernel_eq_iff phi psi hphi hpsi).mp hker a
  exact state_eq_zero_of_gnsStarAlgHom_eq_zero psi hpsi (hb.mp ha)

end MathlibAnnex.Analysis.CStarAlgebra
