import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Cyclic
import MathlibAnnex.Analysis.CStarAlgebra.PureStateGNS.Purity
import MathlibAnnex.Analysis.CStarAlgebra.PureStateGNS.VectorState

/-!
# The pure-to-irreducible GNS bridge

This file proves the projection half of the classical correspondence without
finite-dimensional reduction or Kadison transitivity.
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open MathlibAnnex.Analysis.CStarAlgebra

/-- A cyclic representation whose unit vector state is pure has no
nontrivial closed reducing subspace. -/
theorem isIrreducible_starAlgHom_of_isPureState
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (hcyclic : DenseRange (StarAlgHom.orbitMap pi ξ))
    (hpure : IsPureState A (Representation.vectorFunctional pi ξ)) :
    StarAlgHom.IsIrreducible pi := by
  intro K hKclosed hKreduces
  letI : IsClosed (K : Set H) := hKclosed
  letI : CompleteSpace K := inferInstance
  letI : K.HasOrthogonalProjection := inferInstance
  let P : H →L[ℂ] H := K.starProjection
  let x : H := P ξ
  let y : H := ξ - x
  let rho : A →L[ℂ] ℂ := Representation.vectorFunctional pi x
  have hxK : x ∈ K := by
    exact K.starProjection_apply_mem ξ
  have hyK : y ∈ Kᗮ := by
    exact K.sub_starProjection_mem_orthogonal ξ
  have hmapK (a : A) : pi a x ∈ K :=
    (hKreduces a).1 hxK
  have hmapOrth (a : A) : pi a y ∈ Kᗮ :=
    Representation.map_mem_orthogonal_of_adjoint_mem (pi a) K
      (hKreduces a).2 hyK
  have hdecomp (a : A) :
      Representation.vectorFunctional pi ξ a =
        rho a + Representation.vectorFunctional pi y a := by
    simp only [Representation.vectorFunctional_apply]
    rw [show ξ = x + y by simp [y], map_add]
    simp only [inner_add_left, inner_add_right]
    rw [K.inner_right_of_mem_orthogonal hxK (hmapOrth a),
      K.inner_left_of_mem_orthogonal (hmapK a) hyK]
    simp [rho]
  have hrho_nonneg : ∀ a : A, 0 ≤ a → 0 ≤ rho a := by
    intro a ha
    exact Representation.vectorFunctional_nonnegative pi x ha
  have hrho_le : ∀ a : A, 0 ≤ a →
      rho a ≤ Representation.vectorFunctional pi ξ a := by
    intro a ha
    rw [hdecomp]
    exact le_add_of_nonneg_right
      (Representation.vectorFunctional_nonnegative pi y ha)
  obtain ⟨t, ht, ht_one, hrho⟩ := eq_smul_of_pureState_of_nonnegative_le
    (Representation.vectorFunctional pi ξ) rho hpure hrho_nonneg hrho_le
  have hPcomm (a : A) : P.comp (pi a) = (pi a).comp P := by
    exact Submodule.Reduces.starProjection_commute (hKreduces a)
  have hP_orbit (a : A) : P (pi a ξ) = pi a x := by
    simpa [P, x, ContinuousLinearMap.comp_apply] using
      congrArg (fun T : H →L[ℂ] H ↦ T ξ) (hPcomm a)
  have hgram (a b : A) :
      inner ℂ (pi a ξ) (P (pi b ξ)) = rho (star a * b) := by
    calc
      inner ℂ (pi a ξ) (P (pi b ξ)) =
          inner ℂ (P (pi a ξ)) (pi b ξ) := by
            exact (K.inner_starProjection_left_eq_right (pi a ξ) (pi b ξ)).symm
      _ = inner ℂ (P (pi a ξ)) (P (pi b ξ)) := by
        let z : K := ⟨P (pi a ξ), K.starProjection_apply_mem (pi a ξ)⟩
        exact (K.inner_orthogonalProjectionOnto_eq_of_mem_left z (pi b ξ)).symm
      _ = inner ℂ (pi a x) (pi b x) := by rw [hP_orbit, hP_orbit]
      _ = rho (star a * b) :=
        (Representation.vectorFunctional_star_mul pi x a b).symm
  have hinner (a b : A) :
      inner ℂ (pi a ξ) (P (pi b ξ)) =
        inner ℂ (pi a ξ) (t • pi b ξ) := by
    calc
      inner ℂ (pi a ξ) (P (pi b ξ)) = rho (star a * b) := hgram a b
      _ = (t • Representation.vectorFunctional pi ξ) (star a * b) := by
        rw [hrho]
      _ = t • inner ℂ (pi a ξ) (pi b ξ) := by
        simp only [smul_apply, Representation.vectorFunctional_star_mul]
      _ = inner ℂ (pi a ξ) (t • pi b ξ) := by
        simpa [Complex.real_smul] using
          (inner_smul_right (pi a ξ) (pi b ξ) (t : ℂ)).symm
  have hP_on_orbit (b : A) : P (pi b ξ) = t • pi b ξ := by
    apply ext_inner_left ℂ
    intro z
    exact hcyclic.induction_on z
      (isClosed_eq (continuous_id.inner continuous_const)
        (continuous_id.inner continuous_const)) fun a ↦ hinner a b
  have hP : P = t • ContinuousLinearMap.id ℂ H := by
    apply ContinuousLinearMap.ext
    intro z
    exact hcyclic.induction_on z
      (isClosed_eq P.continuous (t • ContinuousLinearMap.id ℂ H).continuous) fun b ↦ by
        simpa [StarAlgHom.orbitMap] using hP_on_orbit b
  have hξ_ne : ξ ≠ 0 := by
    intro hzero
    simpa [hzero] using hξ
  have ht_idem : t * t = t := by
    apply smul_left_injective ℝ hξ_ne
    have hidem := congrArg (fun T : H →L[ℂ] H ↦ T ξ)
      K.isIdempotentElem_starProjection.eq
    change P (P ξ) = P ξ at hidem
    rw [hP] at hidem
    simpa [smul_smul] using hidem
  have ht_cases : t = 0 ∨ t = 1 := by
    rcases eq_zero_or_eq_zero_of_mul_eq_zero (show t * (t - 1) = 0 by nlinarith) with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  rcases ht_cases with rfl | rfl
  · left
    rw [← K.range_starProjection]
    simp [P] at hP
    simpa [hP]
  · right
    rw [← K.range_starProjection]
    simp [P] at hP
    simpa [hP]

/-- In particular, the GNS representation of a pure state is irreducible. -/
theorem isIrreducible_pureState_gnsStarAlgHom
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) (hpure : IsPureState A phi) :
    StarAlgHom.IsIrreducible
      (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom := by
  apply isIrreducible_starAlgHom_of_isPureState
    (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom
    (stateGNSVector phi hphi) (norm_stateGNSVector phi hphi)
    (denseRange_gnsStarAlgHom_stateGNSVector phi hphi)
  have hfunctional :
      Representation.vectorFunctional
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom
        (stateGNSVector phi hphi) = phi := by
    apply ContinuousLinearMap.ext
    intro a
    exact inner_gnsStarAlgHom_stateGNSVector phi hphi a
  rw [hfunctional]
  exact hpure

end MathlibAnnex.CStarAlgebra
