/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartScalarCompatibility

/-!
# Operator inclusion for the specified regular normal-part equivalence

The specified equivalence is first identified at every normal point with
its actual coefficient-transport construction, optionally followed by star.
Only after the two scalar types have been proved equal is Theorem 6.9 used.
Forward full continuity gives inclusion; inverse full continuity is an
additional hypothesis for equality. This is a reusable regular-pair theorem,
not the application of the generic regularity theorem to the chosen lifts.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

local instance (σ : ℂ ≃+* ℂ) : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ
local instance (σ : ℂ ≃+* ℂ) : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [IsClosed (S : Set (H →L[ℂ] H))] [IsClosed (T : Set (K →L[ℂ] K))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
variable (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))

/-- Equality on all nonzero coefficient representatives is equality of the
specified equivalence and the existing construction (or its star composite). -/
theorem normalPart_equiv_eq_semilinearEquiv_or_star
    {σ : ℂ →+* ℂ} [RingHomInvPair σ σ]
    (hσ : ∀ c : ℂ, σ (star c) = star (σ c)) (U V : H ≃ₛₗ[σ] K)
    (e : normalPart S ≃ normalPart T)
    (hpoint :
      (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
        e (normalPartPoint S hS x y hx hy) = normalPartPoint T hT (U x) (V y)
          (by simpa only [map_zero] using U.injective.ne hx)
          (by simpa only [map_zero] using V.injective.ne hy)) ∨
      (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
        e (normalPartPoint S hS x y hx hy) = normalPartPoint T hT (V y) (U x)
          (by simpa only [map_zero] using V.injective.ne hy)
          (by simpa only [map_zero] using U.injective.ne hx))) :
    e = normalPartSemilinearEquiv S T hS hT hσ U V ∨
      e = (normalPartSemilinearEquiv S T hS hT hσ U V).trans
        (normalPartStarHomeomorph T hT).toEquiv := by
  rcases hpoint with hd | hs
  · left
    apply Equiv.ext
    intro I
    obtain ⟨x, y, hx, hy, rfl⟩ := exists_normalPartPoint_eq S hS I
    exact (hd x y hx hy).trans
      (normalPartSemilinearMap_point S T hS hT hσ U V x y hx hy).symm
  · right
    apply Equiv.ext
    intro I
    obtain ⟨x, y, hx, hy, rfl⟩ := exists_normalPartPoint_eq S hS I
    change e (normalPartPoint S hS x y hx hy) =
      (normalPartStarHomeomorph T hT).toEquiv
        (normalPartSemilinearMap S T hT U V (normalPartPoint S hS x y hx hy))
    rw [normalPartSemilinearMap_point S T hS hT hσ, normalPartStarHomeomorph_point]
    exact hs x y hx hy

/-- Postcomposition with the full star homeomorphism preserves and reflects
full forward continuity. -/
theorem continuous_normalPart_equiv_trans_star_iff (e : normalPart S ≃ normalPart T) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))
        (e.trans (normalPartStarHomeomorph T hT).toEquiv) ↔
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e := by
  constructor
  · intro h
    have hh := (normalPartStarHomeomorph T hT).continuous_toFun.comp h
    have hf : (fun I => (normalPartStarHomeomorph T hT).toEquiv
        ((e.trans (normalPartStarHomeomorph T hT).toEquiv) I)) = e := by
      funext I
      exact normalPartStarHomeomorph_involutive T hT (e I)
    change ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))
      (fun I => (normalPartStarHomeomorph T hT).toEquiv
        ((e.trans (normalPartStarHomeomorph T hT).toEquiv) I)) at hh
    rwa [hf] at hh
  · intro h
    exact (normalPartStarHomeomorph T hT).continuous_toFun.comp h

/-- The inverse comparison is precomposition with star, not postcomposition
on the wrong normal part. -/
theorem continuous_normalPart_equiv_trans_star_symm_iff (e : normalPart S ≃ normalPart T) :
    ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
        (e.trans (normalPartStarHomeomorph T hT).toEquiv).symm ↔
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)) e.symm := by
  constructor
  · intro h
    have hh := h.comp (normalPartStarHomeomorph T hT).continuous_toFun
    have hf : (fun J => (e.trans (normalPartStarHomeomorph T hT).toEquiv).symm
        ((normalPartStarHomeomorph T hT).toEquiv J)) = e.symm := by
      funext J
      change e.symm ((normalPartStarHomeomorph T hT).toEquiv.symm
        ((normalPartStarHomeomorph T hT).toEquiv J)) = e.symm J
      rw [Equiv.symm_apply_apply]
    change ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      (fun J => (e.trans (normalPartStarHomeomorph T hT).toEquiv).symm
        ((normalPartStarHomeomorph T hT).toEquiv J)) at hh
    rwa [hf] at hh
  · intro h
    exact h.comp (normalPartStarHomeomorph T hT).continuous_invFun

/-- The actual specified linear-pair map has full continuity precisely for
operator inclusion, in either global orientation. -/
theorem continuous_normalPart_equiv_iff_of_linear_point_eq_or_swap
    (U V : H ≃L[ℂ] K) (e : normalPart S ≃ normalPart T)
    (heq : e = normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
        U.toLinearEquiv V.toLinearEquiv ∨
      e = (normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
        U.toLinearEquiv V.toLinearEquiv).trans (normalPartStarHomeomorph T hT).toEquiv) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e ↔
      ∀ b : T, InnerProductSpace.adjointSandwich U.toContinuousLinearMap
        V.toContinuousLinearMap (b : K →L[ℂ] K) ∈ S := by
  rcases heq with rfl | rfl
  · exact continuous_normalPartLinearMap_iff S T hS hT U V
  · rw [continuous_normalPart_equiv_trans_star_iff]
    exact continuous_normalPartLinearMap_iff S T hS hT U V

/-- Equality of operator subspaces requires full continuity of the inverse
specified map as well. No inverse-continuity assumption is discarded. -/
theorem continuous_normalPart_equiv_and_inverse_iff_of_linear_point_eq_or_swap
    (U V : H ≃L[ℂ] K) (e : normalPart S ≃ normalPart T)
    (heq : e = normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
        U.toLinearEquiv V.toLinearEquiv ∨
      e = (normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
        U.toLinearEquiv V.toLinearEquiv).trans (normalPartStarHomeomorph T hT).toEquiv) :
    (((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e ∧
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)) e.symm) ↔
      InnerProductSpace.adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap ''
        (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H)) := by
  rcases heq with rfl | rfl
  · exact continuous_normalPartLinearMap_and_inverse_iff S T hS hT U V
  · rw [continuous_normalPart_equiv_trans_star_iff,
      continuous_normalPart_equiv_trans_star_symm_iff]
    exact continuous_normalPartLinearMap_and_inverse_iff S T hS hT U V

/-- The same full-continuity criterion for two bounded conjugate-linear maps.
The sandwich is linear and its coefficient identity includes conjugation. -/
theorem continuous_normalPart_equiv_iff_of_conjugate_point_eq_or_swap
    (U V : H ≃SL[starRingEnd ℂ] K) (e : normalPart S ≃ normalPart T)
    (heq : e = normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
        U.toLinearEquiv V.toLinearEquiv ∨
      e = (normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
        U.toLinearEquiv V.toLinearEquiv).trans (normalPartStarHomeomorph T hT).toEquiv) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e ↔
      ∀ b : T, InnerProductSpace.conjugateAdjointSandwich U.toContinuousLinearMap
        V.toContinuousLinearMap (b : K →L[ℂ] K) ∈ S := by
  rcases heq with rfl | rfl
  · exact continuous_normalPartConjugateLinearMap_iff S T hS hT U V
  · rw [continuous_normalPart_equiv_trans_star_iff]
    exact continuous_normalPartConjugateLinearMap_iff S T hS hT U V

/-- The conjugate-pair equality criterion for the specified map and its inverse. -/
theorem continuous_normalPart_equiv_and_inverse_iff_of_conjugate_point_eq_or_swap
    (U V : H ≃SL[starRingEnd ℂ] K) (e : normalPart S ≃ normalPart T)
    (heq : e = normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
        U.toLinearEquiv V.toLinearEquiv ∨
      e = (normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
        U.toLinearEquiv V.toLinearEquiv).trans (normalPartStarHomeomorph T hT).toEquiv) :
    (((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e ∧
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)) e.symm) ↔
      InnerProductSpace.conjugateAdjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap ''
        (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H)) := by
  rcases heq with rfl | rfl
  · exact continuous_normalPartConjugateLinearMap_and_inverse_iff S T hS hT U V
  · rw [continuous_normalPart_equiv_trans_star_iff,
      continuous_normalPart_equiv_trans_star_symm_iff]
    exact continuous_normalPartConjugateLinearMap_and_inverse_iff S T hS hT U V

/-- A regular pair realizing the specified fully continuous kernel equivalence
has one common scalar type and yields the actual operator inclusion. The same
functions and inverses are retained in the continuous bundles. Operator equality
is supplied only conditional on full continuity of the original inverse.

This theorem does not assume scalar compatibility and does not assert that the
chosen projective lifts have already been regularized. -/
theorem exists_same_type_normalPart_operator_inclusion
    {σ τ : ℂ ≃+* ℂ} (U : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) H K) (V : LinearEquiv τ.toRingHom (σ' := τ.symm.toRingHom) H K)
    (hσ : σ = RingEquiv.refl ℂ ∨ σ = _root_.starRingAut (R := ℂ))
    (hτ : τ = RingEquiv.refl ℂ ∨ τ = _root_.starRingAut (R := ℂ))
    (hU : Continuous U) (hUi : Continuous U.symm)
    (hV : Continuous V) (hVi : Continuous V.symm)
    (e : normalPart S ≃ normalPart T) (hdim : 2 ≤ Module.rank ℂ K)
    (he : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e)
    (hpoint :
      (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
        e (normalPartPoint S hS x y hx hy) = normalPartPoint T hT (U x) (V y)
          (by simpa only [map_zero] using U.injective.ne hx)
          (by simpa only [map_zero] using V.injective.ne hy)) ∨
      (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
        e (normalPartPoint S hS x y hx hy) = normalPartPoint T hT (V y) (U x)
          (by simpa only [map_zero] using V.injective.ne hy)
          (by simpa only [map_zero] using U.injective.ne hx))) :
    σ = τ ∧
    ((∃ Uc Vc : H ≃L[ℂ] K,
      (∀ x, Uc x = U x) ∧ (∀ x, Vc x = V x) ∧
      (∀ z, Uc.symm z = U.symm z) ∧ (∀ z, Vc.symm z = V.symm z) ∧
      (e = normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
          Uc.toLinearEquiv Vc.toLinearEquiv ∨
        e = (normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
          Uc.toLinearEquiv Vc.toLinearEquiv).trans (normalPartStarHomeomorph T hT).toEquiv) ∧
      (∀ b : T, InnerProductSpace.adjointSandwich Uc.toContinuousLinearMap
        Vc.toContinuousLinearMap (b : K →L[ℂ] K) ∈ S) ∧
      (((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
          ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)) e.symm →
        InnerProductSpace.adjointSandwich Uc.toContinuousLinearMap Vc.toContinuousLinearMap ''
          (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H)))) ∨
    (∃ Uc Vc : H ≃SL[starRingEnd ℂ] K,
      (∀ x, Uc x = U x) ∧ (∀ x, Vc x = V x) ∧
      (∀ z, Uc.symm z = U.symm z) ∧ (∀ z, Vc.symm z = V.symm z) ∧
      (e = normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
          Uc.toLinearEquiv Vc.toLinearEquiv ∨
        e = (normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
          Uc.toLinearEquiv Vc.toLinearEquiv).trans (normalPartStarHomeomorph T hT).toEquiv) ∧
      (∀ b : T, InnerProductSpace.conjugateAdjointSandwich Uc.toContinuousLinearMap
        Vc.toContinuousLinearMap (b : K →L[ℂ] K) ∈ S) ∧
      (((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
          ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)) e.symm →
        InnerProductSpace.conjugateAdjointSandwich Uc.toContinuousLinearMap Vc.toContinuousLinearMap ''
          (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H))))) := by
  have hsame := ringEquiv_eq_of_continuous_normalPart_point_eq_or_swap S T hS hT
    U V hσ hτ hU hUi hV hVi e hdim he hpoint
  refine ⟨hsame, ?_⟩
  cases hsame
  rcases hσ with rfl | rfl
  · let Uc : H ≃L[ℂ] K := { U with continuous_toFun := hU, continuous_invFun := hUi }
    let Vc : H ≃L[ℂ] K := { V with continuous_toFun := hV, continuous_invFun := hVi }
    have hEq := normalPart_equiv_eq_semilinearEquiv_or_star S T hS hT (fun _ => rfl)
      Uc.toLinearEquiv Vc.toLinearEquiv e hpoint
    refine Or.inl ⟨Uc, Vc, (fun _ => rfl), (fun _ => rfl),
      (fun _ => rfl), (fun _ => rfl), hEq, ?_, ?_⟩
    · exact (continuous_normalPart_equiv_iff_of_linear_point_eq_or_swap S T hS hT
        Uc Vc e hEq).mp he
    · intro hinv
      exact (continuous_normalPart_equiv_and_inverse_iff_of_linear_point_eq_or_swap
        S T hS hT Uc Vc e hEq).mp ⟨he, hinv⟩
  · let Uc : H ≃SL[starRingEnd ℂ] K :=
      { U with continuous_toFun := hU, continuous_invFun := hUi }
    let Vc : H ≃SL[starRingEnd ℂ] K :=
      { V with continuous_toFun := hV, continuous_invFun := hVi }
    have hEq := normalPart_equiv_eq_semilinearEquiv_or_star S T hS hT (fun _ => rfl)
      Uc.toLinearEquiv Vc.toLinearEquiv e hpoint
    refine Or.inr ⟨Uc, Vc, (fun _ => rfl), (fun _ => rfl),
      (fun _ => rfl), (fun _ => rfl), hEq, ?_, ?_⟩
    · exact (continuous_normalPart_equiv_iff_of_conjugate_point_eq_or_swap S T hS hT
        Uc Vc e hEq).mp he
    · intro hinv
      exact (continuous_normalPart_equiv_and_inverse_iff_of_conjugate_point_eq_or_swap
        S T hS hT Uc Vc e hEq).mp ⟨he, hinv⟩

end MathlibAnnex.Analysis.CStarAlgebra
