import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.Singleton
import MathlibAnnex.Analysis.CStarAlgebra.State.Extension

/-!
# Non-scalar unitization characters as eigenvectors
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- The scalar character of the minimal unitization. -/
noncomputable def infinityCharacter :
    WeakDual.characterSpace ℂ (Unitization ℂ A) :=
  WeakDual.CharacterSpace.equivAlgHom.symm (Unitization.fstHom (R := ℂ) (A := A))

@[simp]
theorem infinityCharacter_apply (z : Unitization ℂ A) :
    infinityCharacter (A := A) z = z.fst := by
  simp [infinityCharacter]

/-- The restriction of the scalar character to a unital star subalgebra of
the unitization. -/
noncomputable def infinityCharacterOn
    (D : StarSubalgebra ℂ (Unitization ℂ A))
    [IsClosed (D : Set (Unitization ℂ A))] :
    WeakDual.characterSpace ℂ D :=
  WeakDual.CharacterSpace.equivAlgHom.symm
    ((Unitization.fstHom (R := ℂ) (A := A)).comp D.subtype.toAlgHom)

@[simp]
theorem infinityCharacterOn_apply
    (D : StarSubalgebra ℂ (Unitization ℂ A))
    [IsClosed (D : Set (Unitization ℂ A))] (d : D) :
    infinityCharacterOn (A := A) D d = (d : Unitization ℂ A).fst := by
  change (d : Unitization ℂ A).fst = (d : Unitization ℂ A).fst
  rfl

/-- If the GNS representation of a state of the unitization vanishes on the
original algebra, then the state is the scalar character. -/
theorem state_eq_infinity_of_gns_restriction_zero
    (phi : Unitization ℂ A →L[ℂ] ℂ)
    (hphi : phi ∈ stateSpace (Unitization ℂ A))
    (hzero : ∀ a : A,
      (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom
        (Unitization.inr a) = 0) :
    phi = (Unitization.fstHom (R := ℂ) (A := A)).toContinuousLinearMap := by
  let f : Unitization ℂ A →ₚ[ℂ] ℂ :=
    positiveLinearMapOfMemStateSpace phi hphi
  apply ContinuousLinearMap.ext
  intro z
  induction z using Unitization.ind with
  | inl_add_inr c a =>
      have hinr : phi (Unitization.inr a) = 0 := by
        calc
          phi (Unitization.inr a) = f (Unitization.inr a) := rfl
          _ = inner ℂ f.gnsCyclicVector
              (f.gnsStarAlgHom (Unitization.inr a) f.gnsCyclicVector) :=
            (PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom f _).symm
          _ = 0 := by rw [hzero a]; simp
      have hinl : phi (Unitization.inl c) = c := by
        calc
          phi (Unitization.inl c) = phi (c • (1 : Unitization ℂ A)) := by
            congr 1
            simpa using
              (Unitization.inl_smul (A := A) c (1 : ℂ))
          _ = c • phi (1 : Unitization ℂ A) := map_smul phi c 1
          _ = c := by rw [hphi.2]; simp
      simp only [map_add, hinl, hinr, add_zero]
      simp [Unitization.fstHom]

/-- Every character of a closed unital star subalgebra of the unitization,
except the scalar character, occurs as a joint unit eigenvector for the
unitized singleton model. -/
theorem exists_unit_eigenvector_of_character_ne_infinity [Nontrivial A]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (D : StarSubalgebra ℂ (Unitization ℂ A))
    [IsClosed (D : Set (Unitization ℂ A))]
    (chi : WeakDual.characterSpace ℂ D)
    (hchi : chi ≠ infinityCharacterOn (A := A) D) :
    ∃ eta : H, ‖eta‖ = 1 ∧
      ∀ d : D, pi.unitization (d : Unitization ℂ A) eta = chi d • eta := by
  obtain ⟨phi, hphi, hpure, hext⟩ :=
    exists_pureState_extension D chi
  let f : Unitization ℂ A →ₚ[ℂ] ℂ :=
    positiveLinearMapOfMemStateSpace phi hphi
  let rhoU : Representation (Unitization ℂ A) f.GNS := f.gnsStarAlgHom
  let rho : NonUnitalCStarRepresentation A f.GNS :=
    rhoU.toNonUnitalStarAlgHom.comp
      (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hrho_nonzero : rho.IsNonzero := by
    by_contra hnz
    have hzero : ∀ a : A, rhoU (Unitization.inr a) = 0 := by
      intro a
      have : rho a = 0 := by
        by_contra ha
        exact hnz ⟨a, ha⟩
      simpa [rho] using this
    have hphi_inf :=
      state_eq_infinity_of_gns_restriction_zero phi hphi hzero
    apply hchi
    apply WeakDual.CharacterSpace.ext
    intro d
    calc
      chi d = phi (d : Unitization ℂ A) := (hext d).symm
      _ = (Unitization.fstHom (R := ℂ) (A := A)).toContinuousLinearMap
          (d : Unitization ℂ A) := by rw [hphi_inf]
      _ = infinityCharacterOn (A := A) D d := by
        simp
  have hxi : ‖f.gnsCyclicVector‖ = 1 :=
    PositiveLinearMap.norm_gnsCyclicVector f
      (positiveLinearMapOfMemStateSpace_one phi hphi)
  have hxi_ne : f.gnsCyclicVector ≠ 0 := by
    intro hzero
    simp [hzero] at hxi
  letI : Nontrivial f.GNS :=
    nontrivial_of_ne f.gnsCyclicVector 0 hxi_ne
  have hirrU : rhoU.IsIrreducible :=
    (Representation.isIrreducible_iff_starAlgHom rhoU).2
      (isIrreducible_pureState_gnsStarAlgHom phi hphi hpure)
  have hirr : rho.IsIrreducible :=
    isIrreducible_restriction_of_isIrreducible_unitization rhoU hirrU
      hrho_nonzero
  obtain ⟨U, hU⟩ := hsingle.2 f.GNS rho hirr
  have hUunit := unitization_unitaryEquivalent (pi := pi) (rho := rho) ⟨U, hU⟩
  obtain ⟨V, hV⟩ := hUunit
  have hrhoeq : rho.unitization = rhoU := by
    apply Unitization.starAlgHom_ext
    ext a
    simp [rho, unitization]
  have heigen (d : D) :
      rhoU (d : Unitization ℂ A) f.gnsCyclicVector =
        chi d • f.gnsCyclicVector := by
    let q : D := d - algebraMap ℂ D (chi d)
    have hchiq : chi q = 0 := by
      dsimp [q]
      rw [map_sub, AlgHomClass.commutes]
      simp
    have hchiqq : chi (star q * q) = 0 := by
      rw [map_mul, map_star, hchiq]
      simp
    have hphiqq : phi (star (q : Unitization ℂ A) *
        (q : Unitization ℂ A)) = 0 := by
      have hvalue := hext (star q * q)
      change phi (star (q : Unitization ℂ A) *
        (q : Unitization ℂ A)) = chi (star q * q) at hvalue
      exact hvalue.trans hchiqq
    have hinner : inner ℂ
        (rhoU (q : Unitization ℂ A) f.gnsCyclicVector)
        (rhoU (q : Unitization ℂ A) f.gnsCyclicVector) = 0 := by
      calc
        _ = Representation.vectorFunctional rhoU f.gnsCyclicVector
            (star (q : Unitization ℂ A) * (q : Unitization ℂ A)) := by
          simpa using
            (Representation.vectorFunctional_star_mul rhoU f.gnsCyclicVector
              (q : Unitization ℂ A) (q : Unitization ℂ A)).symm
        _ = f (star (q : Unitization ℂ A) *
            (q : Unitization ℂ A)) :=
          PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom f _
        _ = phi (star (q : Unitization ℂ A) *
            (q : Unitization ℂ A)) := rfl
        _ = 0 := hphiqq
    have hqzero : rhoU (q : Unitization ℂ A) f.gnsCyclicVector = 0 :=
      inner_self_eq_zero.mp hinner
    have hsub : rhoU (d : Unitization ℂ A) f.gnsCyclicVector -
        chi d • f.gnsCyclicVector = 0 := by
      calc
        _ = rhoU (q : Unitization ℂ A) f.gnsCyclicVector := by
          simp [q, Algebra.algebraMap_eq_smul_one]
        _ = 0 := hqzero
    exact sub_eq_zero.mp hsub
  refine ⟨V.symm f.gnsCyclicVector,
    (V.symm.norm_map f.gnsCyclicVector).trans hxi, ?_⟩
  intro d
  apply V.injective
  calc
    V (pi.unitization (d : Unitization ℂ A)
        (V.symm f.gnsCyclicVector)) =
        rho.unitization (d : Unitization ℂ A) f.gnsCyclicVector := by
      simpa using hV (d : Unitization ℂ A) (V.symm f.gnsCyclicVector)
    _ = rhoU (d : Unitization ℂ A) f.gnsCyclicVector := by rw [hrhoeq]
    _ = chi d • f.gnsCyclicVector := heigen d
    _ = V (chi d • V.symm f.gnsCyclicVector) := by simp

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
