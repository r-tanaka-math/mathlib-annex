import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Cyclic
import MathlibAnnex.Analysis.CStarAlgebra.State.Purity

/-!
# Pure states give irreducible GNS representations
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A cyclic representation whose unit-vector state is pure is irreducible. -/
theorem isIrreducible_starAlgHom_of_isPureState
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hxi : ‖xi‖ = 1)
    (hcyclic : DenseRange (StarAlgHom.orbitMap pi xi))
    (hpure : IsPureState A (Representation.vectorFunctional pi xi)) :
    StarAlgHom.IsIrreducible pi := by
  intro K hKclosed hKreduces
  letI : IsClosed (K : Set H) := hKclosed
  letI : CompleteSpace K := inferInstance
  letI : K.HasOrthogonalProjection := inferInstance
  let P : H →L[ℂ] H := K.starProjection
  let x : H := P xi
  let y : H := xi - x
  let rho : A →L[ℂ] ℂ := Representation.vectorFunctional pi x
  have hxK : x ∈ K := K.starProjection_apply_mem xi
  have hyK : y ∈ Kᗮ := K.sub_starProjection_mem_orthogonal xi
  have hmapK (a : A) : pi a x ∈ K := (hKreduces a).1 hxK
  have hmapOrth (a : A) : pi a y ∈ Kᗮ :=
    Representation.map_mem_orthogonal_of_adjoint_mem (pi a) K
      (hKreduces a).2 hyK
  have hdecomp (a : A) :
      Representation.vectorFunctional pi xi a =
        rho a + Representation.vectorFunctional pi y a := by
    simp only [Representation.vectorFunctional_apply]
    rw [show xi = x + y by simp [y], map_add]
    simp only [inner_add_left, inner_add_right]
    rw [K.inner_right_of_mem_orthogonal hxK (hmapOrth a),
      K.inner_left_of_mem_orthogonal (hmapK a) hyK]
    simp [rho]
  have hrho_nonneg : ∀ a : A, 0 ≤ a → 0 ≤ rho a := by
    intro a ha
    exact Representation.vectorFunctional_nonnegative pi x ha
  have hrho_le : ∀ a : A, 0 ≤ a →
      rho a ≤ Representation.vectorFunctional pi xi a := by
    intro a ha
    rw [hdecomp]
    exact le_add_of_nonneg_right
      (Representation.vectorFunctional_nonnegative pi y ha)
  obtain ⟨t, ht, ht_one, hrho⟩ := eq_smul_of_pureState_of_nonnegative_le
    (Representation.vectorFunctional pi xi) rho hpure hrho_nonneg hrho_le
  have hPcomm (a : A) : P.comp (pi a) = (pi a).comp P :=
    Submodule.Reduces.starProjection_commute (hKreduces a)
  have hP_orbit (a : A) : P (pi a xi) = pi a x := by
    simpa [P, x, ContinuousLinearMap.comp_apply] using
      congrArg (fun T : H →L[ℂ] H ↦ T xi) (hPcomm a)
  have hgram (a b : A) :
      inner ℂ (pi a xi) (P (pi b xi)) = rho (star a * b) := by
    calc
      inner ℂ (pi a xi) (P (pi b xi)) =
          inner ℂ (P (pi a xi)) (pi b xi) := by
            exact (K.inner_starProjection_left_eq_right (pi a xi) (pi b xi)).symm
      _ = inner ℂ (P (pi a xi)) (P (pi b xi)) := by
        let z : K := ⟨P (pi a xi), K.starProjection_apply_mem (pi a xi)⟩
        exact (K.inner_orthogonalProjectionOnto_eq_of_mem_left z (pi b xi)).symm
      _ = inner ℂ (pi a x) (pi b x) := by rw [hP_orbit, hP_orbit]
      _ = rho (star a * b) :=
        (Representation.vectorFunctional_star_mul pi x a b).symm
  have hinner (a b : A) :
      inner ℂ (pi a xi) (P (pi b xi)) =
        inner ℂ (pi a xi) (t • pi b xi) := by
    calc
      inner ℂ (pi a xi) (P (pi b xi)) = rho (star a * b) := hgram a b
      _ = (t • Representation.vectorFunctional pi xi) (star a * b) := by rw [hrho]
      _ = t • inner ℂ (pi a xi) (pi b xi) := by
        simp only [smul_apply, Representation.vectorFunctional_star_mul]
      _ = inner ℂ (pi a xi) (t • pi b xi) := by
        simpa [Complex.real_smul] using
          (inner_smul_right (pi a xi) (pi b xi) (t : ℂ)).symm
  have hP_on_orbit (b : A) : P (pi b xi) = t • pi b xi := by
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
  have hxi_ne : xi ≠ 0 := by
    intro hzero
    simpa [hzero] using hxi
  have ht_idem : t * t = t := by
    apply smul_left_injective ℝ hxi_ne
    have hidem := congrArg (fun T : H →L[ℂ] H ↦ T xi)
      K.isIdempotentElem_starProjection.eq
    change P (P xi) = P xi at hidem
    rw [hP] at hidem
    simpa [smul_smul] using hidem
  have ht_cases : t = 0 ∨ t = 1 := by
    rcases eq_zero_or_eq_zero_of_mul_eq_zero
      (show t * (t - 1) = 0 by nlinarith) with h | h
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

/-- The canonical GNS representation of a pure state is irreducible. -/
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

end MathlibAnnex.Analysis.CStarAlgebra
