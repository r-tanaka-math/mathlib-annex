import MathlibAnnex.Analysis.CStarAlgebra.PureState
import MathlibAnnex.Analysis.CStarAlgebra.PureStateGNS.IrreduciblePure

/-!
# Pure GNS representations separated from closed ideals

This is the project adapter from the generic weak-star existence theorem to
the canonical Naimark state and representation interfaces.
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.CStarAlgebra

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open MathlibAnnex.Analysis.CStarAlgebra

/-- A proper closed two-sided ideal is annihilated by a genuine pure state. -/
theorem exists_pureState_annihilating [Nontrivial A]
    (I : TwoSidedIdeal A) (hI : I ≠ ⊤) (hclosed : IsClosed (I : Set A)) :
    ∃ phi : A →L[ℂ] ℂ,
      phi ∈ stateSpace A ∧ IsPureState A phi ∧
        ∀ x : A, x ∈ I → phi x = 0 := by
  obtain ⟨phi, hpure, hann⟩ :=
    MathlibAnnex.Analysis.CStarAlgebra.exists_extreme_state_annihilating
      I hI hclosed
  exact ⟨phi, hpure.1, hpure, hann⟩

/-- An element annihilated by a state ideal acts as zero in the associated
canonical GNS representation. -/
theorem gnsStarAlgHom_eq_zero_of_mem
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (I : TwoSidedIdeal A) (hann : ∀ x : A, x ∈ I → phi x = 0)
    {x : A} (hx : x ∈ I) :
    (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom x = 0 := by
  let f : A →ₚ[ℂ] ℂ := positiveLinearMapOfMemStateSpace phi hphi
  let pi : Representation A f.GNS := f.gnsStarAlgHom
  let xi : f.GNS := f.gnsCyclicVector
  have hdense : DenseRange (StarAlgHom.orbitMap pi xi) :=
    PositiveLinearMap.denseRange_gnsStarAlgHom_apply_gnsCyclicVector f
  apply ContinuousLinearMap.ext
  intro y
  exact hdense.induction_on y
    (isClosed_eq (pi x).continuous continuous_const) fun a => by
      have hxa : x * a ∈ I := I.mul_mem_right x a hx
      have hsq : star (x * a) * (x * a) ∈ I :=
        I.mul_mem_left (star (x * a)) (x * a) hxa
      have hinner : inner ℂ (pi (x * a) xi) (pi (x * a) xi) = 0 := by
        calc
          inner ℂ (pi (x * a) xi) (pi (x * a) xi) =
              Representation.vectorFunctional pi xi
                (star (x * a) * (x * a)) := by
            simpa using
              (Representation.vectorFunctional_star_mul pi xi (x * a) (x * a)).symm
          _ = f (star (x * a) * (x * a)) :=
            PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom f _
          _ = phi (star (x * a) * (x * a)) := rfl
          _ = 0 := hann _ hsq
      have hzero : pi (x * a) xi = 0 := inner_self_eq_zero.mp hinner
      change (pi x * pi a) xi = 0
      rw [← map_mul]
      exact hzero

/-- The separating pure state supplies a nonzero irreducible GNS
representation which annihilates the ideal elementwise. -/
theorem exists_irreducibleGNS_annihilating [Nontrivial A]
    (I : TwoSidedIdeal A) (hI : I ≠ ⊤) (hclosed : IsClosed (I : Set A)) :
    ∃ (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A),
      IsPureState A phi ∧
      Representation.IsIrreducible
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom ∧
      ∀ x : A, x ∈ I →
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom x = 0 := by
  obtain ⟨phi, hphi, hpure, hann⟩ :=
    exists_pureState_annihilating I hI hclosed
  let f : A →ₚ[ℂ] ℂ := positiveLinearMapOfMemStateSpace phi hphi
  let xi : f.GNS := f.gnsCyclicVector
  have hxi : ‖xi‖ = 1 :=
    PositiveLinearMap.norm_gnsCyclicVector f
      (positiveLinearMapOfMemStateSpace_one phi hphi)
  have hxi_ne : xi ≠ 0 := by
    intro hzero
    simp [hzero] at hxi
  letI : Nontrivial f.GNS := nontrivial_of_ne xi 0 hxi_ne
  have hirr : Representation.IsIrreducible f.gnsStarAlgHom :=
    (Representation.isIrreducible_iff_starAlgHom f.gnsStarAlgHom).2
      (isIrreducible_pureState_gnsStarAlgHom phi hphi hpure)
  exact ⟨phi, hphi, hpure, hirr, fun x hx =>
    gnsStarAlgHom_eq_zero_of_mem phi hphi I hann hx⟩

end MathlibAnnex.CStarAlgebra
