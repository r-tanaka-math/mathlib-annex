/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.FiniteFixedVectors
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartBounded
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.StarHomeomorph
import MathlibAnnex.Analysis.InnerProductSpace.MatrixCoefficient.SemilinearProportionality

/-!
# Compatibility of the two regular scalar types

Individual identity/conjugation alternatives do not imply that a pair has
one scalar type. Full continuity of the specified normal-kernel map excludes
the mixed cases. A target element with two fixed independent vectors supplies
the rank hypothesis; closed zero-incidence and an excluded point supply the
source element. The mixed sandwiches use the actual ordinary or conjugate
adjoint and are conjugate-linear, not linear. Lemma 6.15 then forces their
scalar homomorphism to be the identity, a contradiction at `Complex.I`.

All points and closures below belong to the inherited normal part. No
compact-ideal dichotomy, positive element, or rank-one preimage is used.
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

/-- Closed incidence gives an actual source-algebra element with every required
zero coefficient and one specified nonzero diagonal test. The scalar maps may
be different and no continuity of the vector maps is used in this step. -/
theorem exists_normalPart_zero_imp_of_continuous_point_eq
    {σ τ : ℂ ≃+* ℂ} (U : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) H K) (V : LinearEquiv τ.toRingHom (σ' := τ.symm.toRingHom) H K)
    (e : normalPart S ≃ normalPart T)
    (he : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e)
    (hpoint : ∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
      e (normalPartPoint S hS x y hx hy) =
        normalPartPoint T hT (U x) (V y)
          (by simpa only [map_zero] using U.injective.ne hx)
          (by simpa only [map_zero] using V.injective.ne hy))
    (b : T) (z₀ : K) (hz₀ : z₀ ≠ 0) (hb₀ : inner ℂ z₀ (b.val z₀) ≠ 0) :
    ∃ a : S,
      (∀ z w : K, inner ℂ w (b.val z) = 0 →
        inner ℂ (V.symm w) (a.val (U.symm z)) = 0) ∧
      inner ℂ (V.symm z₀) (a.val (U.symm z₀)) ≠ 0 := by
  classical
  let cS := (NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)
  let cT := (NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)
  let Z : Set (normalPart T) := {J | b ∈ J.val.val}
  let D : Set (normalPart S) := e ⁻¹' Z
  have hD : cS.IsClosed D :=
    (ClosureSpace.continuous_iff_isClosed_preimage cS cT e).mp he Z
      (isClosed_normalPart_zeroIncidence T b)
  have hx₀ : U.symm z₀ ≠ 0 := by simpa only [map_zero] using U.symm.injective.ne hz₀
  have hy₀ : V.symm z₀ ≠ 0 := by simpa only [map_zero] using V.symm.injective.ne hz₀
  let I := normalPartPoint S hS (U.symm z₀) (V.symm z₀) hx₀ hy₀
  have hEI : e I = normalPartPoint T hT z₀ z₀ hz₀ hz₀ := by
    dsimp [I]
    have h := hpoint (U.symm z₀) (V.symm z₀) hx₀ hy₀
    refine h.trans ?_
    apply Subtype.ext
    apply Subtype.ext
    simp only [normalPartPoint_val_val, U.apply_symm_apply, V.apply_symm_apply]
  have hI : I ∉ cS.closure D := by
    intro hi
    have hid : I ∈ D := (ClosureSpace.isClosed_iff_closure_subset cS D).mp hD hi
    change b ∈ (e I).val.val at hid
    rw [hEI] at hid
    exact hb₀ hid
  rw [mem_normalPart_closure_iff S D I] at hI
  push_neg at hI
  obtain ⟨a, haD, haI⟩ := hI
  refine ⟨a, ?_, haI⟩
  intro z w hzw
  by_cases hz : z = 0
  · simp only [hz, map_zero, inner_zero_right]
  by_cases hw : w = 0
  · simp only [hw, map_zero, inner_zero_left]
  have hx : U.symm z ≠ 0 := by simpa only [map_zero] using U.symm.injective.ne hz
  have hy : V.symm w ≠ 0 := by simpa only [map_zero] using V.symm.injective.ne hw
  let J := normalPartPoint S hS (U.symm z) (V.symm w) hx hy
  have hJ : J ∈ D := by
    change b ∈ (e J).val.val
    dsimp [J]
    rw [hpoint]
    change inner ℂ (V (V.symm w)) (b.val (U (U.symm z))) = 0
    rw [U.apply_symm_apply, V.apply_symm_apply]
    exact hzw
  exact haD J hJ

/-- A linear source factor and a conjugate-linear target factor cannot realize
a fully continuous direct map when the target has algebraic rank at least two. -/
theorem not_continuous_normalPart_equiv_of_linear_conjugate_point_eq
    (U : H ≃L[ℂ] K) (V : H ≃SL[starRingEnd ℂ] K)
    (e : normalPart S ≃ normalPart T) (hdim : 2 ≤ Module.rank ℂ K)
    (hpoint : ∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
      e (normalPartPoint S hS x y hx hy) =
        normalPartPoint T hT (U x) (V y)
          (by simpa only [map_zero] using U.injective.ne hx)
          (by simpa only [map_zero] using V.injective.ne hy)) :
    ¬ ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e := by
  intro he
  obtain ⟨b, z₀, z₁, hb, hbn, hind, hfix₀, hfix₁, hrank, hz₀, hb₀⟩ :=
    NonUnitalCStarRepresentation.exists_selfAdjoint_norm_le_one_two_le_rank_range
      (NonUnitalStarSubalgebraClass.subtype T) hT hdim
  obtain ⟨a, hazero, hane⟩ := exists_normalPart_zero_imp_of_continuous_point_eq S T hS hT
    (σ := RingEquiv.refl ℂ) (τ := _root_.starRingAut (R := ℂ))
    U.toLinearEquiv V.toLinearEquiv e he hpoint b z₀ hz₀ hb₀
  let R : K →L⋆[ℂ] K := (InnerProductSpace.conjugateAdjoint
    V.symm.toContinuousLinearMap).comp ((a : H →L[ℂ] H).comp U.symm.toContinuousLinearMap)
  have hR (z w : K) : inner ℂ w (R z) =
      star (inner ℂ (V.symm w) (a.val (U.symm z))) :=
    InnerProductSpace.conjugateAdjoint_inner_right V.symm.toContinuousLinearMap w
      (a.val (U.symm z))
  have hzero (z w : K) (h : inner ℂ w (b.val z) = 0) : inner ℂ w (R z) = 0 := by
    have hz := hazero z w h
    change inner ℂ (V.symm w) (a.val (U.symm z)) = 0 at hz
    rw [hR, hz, star_zero]
  have hdiag : inner ℂ (R z₀) z₀ ≠ 0 := by
    intro h
    have hh := inner_eq_zero_symm.mp h
    rw [hR] at hh
    exact hane (star_eq_zero.mp hh)
  obtain ⟨hscalar, hc⟩ :=
    ContinuousLinearMap.eq_id_and_exists_ne_zero_smul_of_inner_eq_zero_imp_of_diagonal_ne_zero
      (b : K →L[ℂ] K) R hrank hzero z₀ hdiag
  have hi := congrArg (fun f : ℂ →+* ℂ => (f Complex.I).im) hscalar
  change (-1 : ℝ) = 1 at hi
  norm_num at hi

/-- The other mixed case uses the ordinary adjoint of the inverse target
factor. The resulting operator is again conjugate-linear. -/
theorem not_continuous_normalPart_equiv_of_conjugate_linear_point_eq
    (U : H ≃SL[starRingEnd ℂ] K) (V : H ≃L[ℂ] K)
    (e : normalPart S ≃ normalPart T) (hdim : 2 ≤ Module.rank ℂ K)
    (hpoint : ∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
      e (normalPartPoint S hS x y hx hy) =
        normalPartPoint T hT (U x) (V y)
          (by simpa only [map_zero] using U.injective.ne hx)
          (by simpa only [map_zero] using V.injective.ne hy)) :
    ¬ ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e := by
  intro he
  obtain ⟨b, z₀, z₁, hb, hbn, hind, hfix₀, hfix₁, hrank, hz₀, hb₀⟩ :=
    NonUnitalCStarRepresentation.exists_selfAdjoint_norm_le_one_two_le_rank_range
      (NonUnitalStarSubalgebraClass.subtype T) hT hdim
  obtain ⟨a, hazero, hane⟩ := exists_normalPart_zero_imp_of_continuous_point_eq S T hS hT
    (σ := _root_.starRingAut (R := ℂ)) (τ := RingEquiv.refl ℂ)
    U.toLinearEquiv V.toLinearEquiv e he hpoint b z₀ hz₀ hb₀
  let R : K →L⋆[ℂ] K := V.symm.toContinuousLinearMap.adjoint.comp
    ((a : H →L[ℂ] H).comp U.symm.toContinuousLinearMap)
  have hR (z w : K) : inner ℂ w (R z) = inner ℂ (V.symm w) (a.val (U.symm z)) :=
    ContinuousLinearMap.adjoint_inner_right V.symm.toContinuousLinearMap w (a.val (U.symm z))
  have hzero (z w : K) (h : inner ℂ w (b.val z) = 0) : inner ℂ w (R z) = 0 := by
    rw [hR]
    exact hazero z w h
  have hdiag : inner ℂ (R z₀) z₀ ≠ 0 := by
    intro h
    have hh := inner_eq_zero_symm.mp h
    rw [hR] at hh
    exact hane hh
  obtain ⟨hscalar, hc⟩ :=
    ContinuousLinearMap.eq_id_and_exists_ne_zero_smul_of_inner_eq_zero_imp_of_diagonal_ne_zero
      (b : K →L[ℂ] K) R hrank hzero z₀ hdiag
  have hi := congrArg (fun f : ℂ →+* ℂ => (f Complex.I).im) hscalar
  change (-1 : ℝ) = 1 at hi
  norm_num at hi

/-- Individually regular scalar maps must coincide for a fully continuous
specified direct normal-part equivalence. This is not a regularity assumption. -/
theorem ringEquiv_eq_of_continuous_normalPart_point_eq
    {σ τ : ℂ ≃+* ℂ} (U : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) H K) (V : LinearEquiv τ.toRingHom (σ' := τ.symm.toRingHom) H K)
    (hσ : σ = RingEquiv.refl ℂ ∨ σ = _root_.starRingAut (R := ℂ))
    (hτ : τ = RingEquiv.refl ℂ ∨ τ = _root_.starRingAut (R := ℂ))
    (hU : Continuous U) (hUi : Continuous U.symm)
    (hV : Continuous V) (hVi : Continuous V.symm)
    (e : normalPart S ≃ normalPart T) (hdim : 2 ≤ Module.rank ℂ K)
    (he : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e)
    (hpoint : ∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
      e (normalPartPoint S hS x y hx hy) =
        normalPartPoint T hT (U x) (V y)
          (by simpa only [map_zero] using U.injective.ne hx)
          (by simpa only [map_zero] using V.injective.ne hy)) : σ = τ := by
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl
  · rfl
  · let Uc : H ≃L[ℂ] K := { U with continuous_toFun := hU, continuous_invFun := hUi }
    let Vc : H ≃SL[starRingEnd ℂ] K :=
      { V with continuous_toFun := hV, continuous_invFun := hVi }
    exact False.elim
      (not_continuous_normalPart_equiv_of_linear_conjugate_point_eq S T hS hT
        Uc Vc e hdim hpoint he)
  · let Uc : H ≃SL[starRingEnd ℂ] K :=
      { U with continuous_toFun := hU, continuous_invFun := hUi }
    let Vc : H ≃L[ℂ] K := { V with continuous_toFun := hV, continuous_invFun := hVi }
    exact False.elim
      (not_continuous_normalPart_equiv_of_conjugate_linear_point_eq S T hS hT
        Uc Vc e hdim hpoint he)
  · rfl

/-- The scalar equality also holds in the global swapped orientation. Swap is
removed by the existing FULL star homeomorphism, not by finite continuity. -/
theorem ringEquiv_eq_of_continuous_normalPart_point_eq_or_swap
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
          (by simpa only [map_zero] using U.injective.ne hx))) : σ = τ := by
  rcases hpoint with hdirect | hswap
  · exact ringEquiv_eq_of_continuous_normalPart_point_eq S T hS hT U V hσ hτ
      hU hUi hV hVi e hdim he hdirect
  · let e' := e.trans (normalPartStarHomeomorph T hT).toEquiv
    have he' : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e' :=
      (normalPartStarHomeomorph T hT).continuous_toFun.comp he
    apply ringEquiv_eq_of_continuous_normalPart_point_eq S T hS hT U V hσ hτ
      hU hUi hV hVi e' hdim he'
    intro x y hx hy
    change (normalPartStarHomeomorph T hT).toEquiv
      (e (normalPartPoint S hS x y hx hy)) = _
    rw [hswap, normalPartStarHomeomorph_point]

end MathlibAnnex.Analysis.CStarAlgebra
