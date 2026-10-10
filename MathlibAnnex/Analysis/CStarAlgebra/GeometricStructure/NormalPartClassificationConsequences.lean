/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartClassification

/-!
# Point and kernel consequences of the selected-pair classification

The adapters first expose the forward and inverse equations in the SAME
orientation as the equality with the existing 6.9 map. Applying them to the
continuous pairs furnished by `exists_normalPart_selected_operator_inclusion`
or `exists_normalPart_selected_operator_eq` adds no classification hypothesis.
They are stated algebraically, so they do not impose the infinite-dimensional
regularity premise on the earlier rank-three realization or finite theory.

The later same-function adapters retain the existing selected lifts and their
bounds; they never choose another lift. Hilbert-basis dimension is not asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
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
variable (e : ClosureSpace.FiniteHomeomorph
  ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
  ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)))

section Evaluation
variable {ρ : ℂ →+* ℂ} [RingHomInvPair ρ ρ]

/-- The equality with the coefficient transport, or with its target-star
composite, gives point formulas and their inverses in that same global branch.
No inverse continuity is used for these algebraic inverse formulas. -/
theorem normalPart_equiv_evaluation_of_semilinear_eq_or_star
    (hρ : ∀ a : ℂ, ρ (star a) = star (ρ a)) (U V : H ≃ₛₗ[ρ] K)
    (heq : e.toEquiv = normalPartSemilinearEquiv S T hS hT hρ U V ∨
      e.toEquiv = (normalPartSemilinearEquiv S T hS hT hρ U V).trans
        (normalPartStarHomeomorph T hT).toEquiv) :
    ((e.toEquiv = normalPartSemilinearEquiv S T hS hT hρ U V) ∧
      (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
        e.toEquiv (normalPartPoint S hS x y hx hy) =
          normalPartPoint T hT (U x) (V y)
            (by simpa only [map_zero] using U.injective.ne hx)
            (by simpa only [map_zero] using V.injective.ne hy)) ∧
      (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
        e.toEquiv.symm (normalPartPoint T hT z w hz hw) =
          normalPartPoint S hS (U.symm z) (V.symm w)
            (by simpa only [map_zero] using U.symm.injective.ne hz)
            (by simpa only [map_zero] using V.symm.injective.ne hw))) ∨
    ((e.toEquiv = (normalPartSemilinearEquiv S T hS hT hρ U V).trans
        (normalPartStarHomeomorph T hT).toEquiv) ∧
      (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
        e.toEquiv (normalPartPoint S hS x y hx hy) =
          normalPartPoint T hT (V y) (U x)
            (by simpa only [map_zero] using V.injective.ne hy)
            (by simpa only [map_zero] using U.injective.ne hx)) ∧
      (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
        e.toEquiv.symm (normalPartPoint T hT z w hz hw) =
          normalPartPoint S hS (U.symm w) (V.symm z)
            (by simpa only [map_zero] using U.symm.injective.ne hw)
            (by simpa only [map_zero] using V.symm.injective.ne hz))) := by
  rcases heq with hd | hs
  · have hf (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
        e.toEquiv (normalPartPoint S hS x y hx hy) =
          normalPartPoint T hT (U x) (V y)
            (by simpa only [map_zero] using U.injective.ne hx)
            (by simpa only [map_zero] using V.injective.ne hy) := by
      rw [hd]
      exact normalPartSemilinearMap_point S T hS hT hρ U V x y hx hy
    refine Or.inl ⟨hd, hf, ?_⟩
    intro z w hz hw
    apply e.toEquiv.injective
    rw [Equiv.apply_symm_apply, hf]
    simp only [LinearEquiv.apply_symm_apply]
  · have hf (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
        e.toEquiv (normalPartPoint S hS x y hx hy) =
          normalPartPoint T hT (V y) (U x)
            (by simpa only [map_zero] using V.injective.ne hy)
            (by simpa only [map_zero] using U.injective.ne hx) := by
      rw [hs]
      change (normalPartStarHomeomorph T hT).toEquiv
        (normalPartSemilinearMap S T hT U V (normalPartPoint S hS x y hx hy)) = _
      rw [normalPartSemilinearMap_point S T hS hT hρ, normalPartStarHomeomorph_point]
    refine Or.inr ⟨hs, hf, ?_⟩
    intro z w hz hw
    apply e.toEquiv.injective
    rw [Equiv.apply_symm_apply, hf]
    simp only [LinearEquiv.apply_symm_apply]

/-- Literal kernels underlying the point classification. In the swapped
inverse formula U inverse acts on the SECOND target vector and V inverse on the
FIRST. The normal-part subtypes and the coefficient's conjugate-linear slot
are retained, rather than replacing points by informal ray labels. -/
theorem normalPart_equiv_kernel_evaluation_of_semilinear_eq_or_star
    (hρ : ∀ a : ℂ, ρ (star a) = star (ρ a)) (U V : H ≃ₛₗ[ρ] K)
    (heq : e.toEquiv = normalPartSemilinearEquiv S T hS hT hρ U V ∨
      e.toEquiv = (normalPartSemilinearEquiv S T hS hT hρ U V).trans
        (normalPartStarHomeomorph T hT).toEquiv) :
    ((e.toEquiv = normalPartSemilinearEquiv S T hS hT hρ U V) ∧
      (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
        (e.toEquiv (normalPartPoint S hS x y hx hy)).val.val =
          {b : T | inner ℂ (V y) ((b : K →L[ℂ] K) (U x)) = 0}) ∧
      (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
        (e.toEquiv.symm (normalPartPoint T hT z w hz hw)).val.val =
          {a : S | inner ℂ (V.symm w) ((a : H →L[ℂ] H) (U.symm z)) = 0})) ∨
    ((e.toEquiv = (normalPartSemilinearEquiv S T hS hT hρ U V).trans
        (normalPartStarHomeomorph T hT).toEquiv) ∧
      (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
        (e.toEquiv (normalPartPoint S hS x y hx hy)).val.val =
          {b : T | inner ℂ (U x) ((b : K →L[ℂ] K) (V y)) = 0}) ∧
      (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
        (e.toEquiv.symm (normalPartPoint T hT z w hz hw)).val.val =
          {a : S | inner ℂ (V.symm z) ((a : H →L[ℂ] H) (U.symm w)) = 0})) := by
  rcases normalPart_equiv_evaluation_of_semilinear_eq_or_star
      S T hS hT e hρ U V heq with ⟨hd, hf, hi⟩ | ⟨hs, hf, hi⟩
  · exact Or.inl ⟨hd,
      fun x y hx hy => congrArg (fun I : normalPart T => I.val.val) (hf x y hx hy),
      fun z w hz hw => congrArg (fun I : normalPart S => I.val.val) (hi z w hz hw)⟩
  · exact Or.inr ⟨hs,
      fun x y hx hy => congrArg (fun I : normalPart T => I.val.val) (hf x y hx hy),
      fun z w hz hw => congrArg (fun I : normalPart S => I.val.val) (hi z w hz hw)⟩

end Evaluation

section SameFunctions
variable {ρ : ℂ →+* ℂ} [RingHomInvPair ρ ρ]

/-- The same-function witnesses in the classification identify the pair with
the previous continuous semilinear wrappers as well, including both inverses.
The scalar parameters of those wrappers need not be definitionally equal to ρ. -/
theorem normalPart_continuous_pair_eq_selected_wrappers
    (hdim : 3 ≤ Module.rank ℂ H) (hH : ¬ FiniteDimensional ℂ H)
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (Uc Vc : H ≃SL[ρ] K)
    (hU : ∀ x, Uc x = normalPartFirstSemilinearEquiv S T hS hT e hdim x)
    (hV : ∀ x, Vc x = normalPartSecondSemilinearEquiv S T hS hT e hdim x)
    (hUi : ∀ z, Uc.symm z = (normalPartFirstSemilinearEquiv S T hS hT e hdim).symm z)
    (hVi : ∀ z, Vc.symm z = (normalPartSecondSemilinearEquiv S T hS hT e hdim).symm z) :
    (∀ x, Uc x = normalPartFirstContinuousSemilinearEquiv S T hS hT e hdim hH hcont x) ∧
    (∀ x, Vc x = normalPartSecondContinuousSemilinearEquiv S T hS hT e hdim hH hcont x) ∧
    (∀ z, Uc.symm z =
      (normalPartFirstContinuousSemilinearEquiv S T hS hT e hdim hH hcont).symm z) ∧
    (∀ z, Vc.symm z =
      (normalPartSecondContinuousSemilinearEquiv S T hS hT e hdim hH hcont).symm z) := by
  simpa only [normalPartFirstContinuousSemilinearEquiv_apply,
    normalPartSecondContinuousSemilinearEquiv_apply,
    normalPartFirstContinuousSemilinearEquiv_symm_apply,
    normalPartSecondContinuousSemilinearEquiv_symm_apply] using And.intro hU (And.intro hV (And.intro hUi hVi))

/-- The explicit positive common bound from the selected pair remains valid
for either same-type packaging. No fresh existential constants or vector maps
are chosen, and the bounds hold on zero vectors as well. -/
theorem normalPart_continuous_pair_norm_le_of_eq_selected
    (hdim : 3 ≤ Module.rank ℂ H) (hH : ¬ FiniteDimensional ℂ H)
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (Uc Vc : H ≃SL[ρ] K)
    (hU : ∀ x, Uc x = normalPartFirstSemilinearEquiv S T hS hT e hdim x)
    (hV : ∀ x, Vc x = normalPartSecondSemilinearEquiv S T hS hT e hdim x)
    (hUi : ∀ z, Uc.symm z = (normalPartFirstSemilinearEquiv S T hS hT e hdim).symm z)
    (hVi : ∀ z, Vc.symm z = (normalPartSecondSemilinearEquiv S T hS hT e hdim).symm z) :
    let C := normalPartSemilinearNormBound S T hS hT e hdim hH hcont
    0 < C ∧ (∀ x, ‖Uc x‖ ≤ C * ‖x‖) ∧ (∀ z, ‖Uc.symm z‖ ≤ C * ‖z‖) ∧
      (∀ x, ‖Vc x‖ ≤ C * ‖x‖) ∧ (∀ z, ‖Vc.symm z‖ ≤ C * ‖z‖) := by
  dsimp only
  refine ⟨normalPartSemilinearNormBound_pos S T hS hT e hdim hH hcont, ?_⟩
  simpa only [hU, hV, hUi, hVi] using
    normalPart_semilinear_factors_norm_le S T hS hT e hdim hH hcont

end SameFunctions

/-- The full selected-pair conclusion from source infinite dimensionality and
forward full continuity. Every equality below uses the SAME Uc,Vc and inverses.
The global orientation also records the actual 6.9 equivalence (with target star
in the swapped branch). Neither a regularity hypothesis nor scalar compatibility
is supplied by the caller. This does not assert the Hilbert-dimension endpoint. -/
theorem exists_normalPart_selected_classification
    (hH : ¬ FiniteDimensional ℂ H)
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv) :
    let hd := (three_le_rank_of_normalPart_finiteHomeomorph S T hS hT e hH).1
    let U := normalPartFirstSemilinearEquiv S T hS hT e hd
    let V := normalPartSecondSemilinearEquiv S T hS hT e hd
    normalPartFirstScalarEquiv S T hS hT e hd =
      normalPartSecondScalarEquiv S T hS hT e hd ∧
    (
    (∃ Uc Vc : H ≃L[ℂ] K,
      (∀ x, Uc x = U x) ∧ (∀ x, Vc x = V x) ∧
      (∀ z, Uc.symm z = U.symm z) ∧ (∀ z, Vc.symm z = V.symm z) ∧
      (((e.toEquiv = normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
            Uc.toLinearEquiv Vc.toLinearEquiv) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          e.toEquiv (normalPartPoint S hS x y hx hy) =
            normalPartPoint T hT (Uc x) (Vc y)
              (by simpa only [map_zero] using Uc.injective.ne hx)
              (by simpa only [map_zero] using Vc.injective.ne hy)) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          e.toEquiv.symm (normalPartPoint T hT z w hz hw) =
            normalPartPoint S hS (Uc.symm z) (Vc.symm w)
              (by simpa only [map_zero] using Uc.symm.injective.ne hz)
              (by simpa only [map_zero] using Vc.symm.injective.ne hw)) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          (e.toEquiv (normalPartPoint S hS x y hx hy)).val.val =
            {b : T | inner ℂ (Vc y) ((b : K →L[ℂ] K) (Uc x)) = 0}) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          (e.toEquiv.symm (normalPartPoint T hT z w hz hw)).val.val =
            {a : S | inner ℂ (Vc.symm w) ((a : H →L[ℂ] H) (Uc.symm z)) = 0})) ∨
       ((e.toEquiv = (normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
            Uc.toLinearEquiv Vc.toLinearEquiv).trans (normalPartStarHomeomorph T hT).toEquiv) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          e.toEquiv (normalPartPoint S hS x y hx hy) =
            normalPartPoint T hT (Vc y) (Uc x)
              (by simpa only [map_zero] using Vc.injective.ne hy)
              (by simpa only [map_zero] using Uc.injective.ne hx)) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          e.toEquiv.symm (normalPartPoint T hT z w hz hw) =
            normalPartPoint S hS (Uc.symm w) (Vc.symm z)
              (by simpa only [map_zero] using Uc.symm.injective.ne hw)
              (by simpa only [map_zero] using Vc.symm.injective.ne hz)) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          (e.toEquiv (normalPartPoint S hS x y hx hy)).val.val =
            {b : T | inner ℂ (Uc x) ((b : K →L[ℂ] K) (Vc y)) = 0}) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          (e.toEquiv.symm (normalPartPoint T hT z w hz hw)).val.val =
            {a : S | inner ℂ (Vc.symm z) ((a : H →L[ℂ] H) (Uc.symm w)) = 0}))) ∧
      (∀ b : T, InnerProductSpace.adjointSandwich Uc.toContinuousLinearMap
        Vc.toContinuousLinearMap (b : K →L[ℂ] K) ∈ S) ∧
      (((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
          ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)) e.toEquiv.symm →
        InnerProductSpace.adjointSandwich Uc.toContinuousLinearMap Vc.toContinuousLinearMap ''
          (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H)))) ∨
    (∃ Uc Vc : H ≃SL[starRingEnd ℂ] K,
      (∀ x, Uc x = U x) ∧ (∀ x, Vc x = V x) ∧
      (∀ z, Uc.symm z = U.symm z) ∧ (∀ z, Vc.symm z = V.symm z) ∧
      (((e.toEquiv = normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
            Uc.toLinearEquiv Vc.toLinearEquiv) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          e.toEquiv (normalPartPoint S hS x y hx hy) =
            normalPartPoint T hT (Uc x) (Vc y)
              (by simpa only [map_zero] using Uc.injective.ne hx)
              (by simpa only [map_zero] using Vc.injective.ne hy)) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          e.toEquiv.symm (normalPartPoint T hT z w hz hw) =
            normalPartPoint S hS (Uc.symm z) (Vc.symm w)
              (by simpa only [map_zero] using Uc.symm.injective.ne hz)
              (by simpa only [map_zero] using Vc.symm.injective.ne hw)) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          (e.toEquiv (normalPartPoint S hS x y hx hy)).val.val =
            {b : T | inner ℂ (Vc y) ((b : K →L[ℂ] K) (Uc x)) = 0}) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          (e.toEquiv.symm (normalPartPoint T hT z w hz hw)).val.val =
            {a : S | inner ℂ (Vc.symm w) ((a : H →L[ℂ] H) (Uc.symm z)) = 0})) ∨
       ((e.toEquiv = (normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
            Uc.toLinearEquiv Vc.toLinearEquiv).trans (normalPartStarHomeomorph T hT).toEquiv) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          e.toEquiv (normalPartPoint S hS x y hx hy) =
            normalPartPoint T hT (Vc y) (Uc x)
              (by simpa only [map_zero] using Vc.injective.ne hy)
              (by simpa only [map_zero] using Uc.injective.ne hx)) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          e.toEquiv.symm (normalPartPoint T hT z w hz hw) =
            normalPartPoint S hS (Uc.symm w) (Vc.symm z)
              (by simpa only [map_zero] using Uc.symm.injective.ne hw)
              (by simpa only [map_zero] using Vc.symm.injective.ne hz)) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          (e.toEquiv (normalPartPoint S hS x y hx hy)).val.val =
            {b : T | inner ℂ (Uc x) ((b : K →L[ℂ] K) (Vc y)) = 0}) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          (e.toEquiv.symm (normalPartPoint T hT z w hz hw)).val.val =
            {a : S | inner ℂ (Vc.symm z) ((a : H →L[ℂ] H) (Uc.symm w)) = 0}))) ∧
      (∀ b : T, InnerProductSpace.conjugateAdjointSandwich Uc.toContinuousLinearMap
        Vc.toContinuousLinearMap (b : K →L[ℂ] K) ∈ S) ∧
      (((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
          ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)) e.toEquiv.symm →
        InnerProductSpace.conjugateAdjointSandwich Uc.toContinuousLinearMap Vc.toContinuousLinearMap ''
          (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H))))) := by
  dsimp only
  obtain ⟨hsame, hpair⟩ :=
    exists_normalPart_selected_operator_inclusion S T hS hT e hH hcont
  refine ⟨hsame, ?_⟩
  rcases hpair with ⟨Uc, Vc, hU, hV, hUi, hVi, heq, hinc, hEq⟩ |
    ⟨Uc, Vc, hU, hV, hUi, hVi, heq, hinc, hEq⟩
  · refine Or.inl ⟨Uc, Vc, hU, hV, hUi, hVi, ?_, hinc, hEq⟩
    rcases normalPart_equiv_evaluation_of_semilinear_eq_or_star
        S T hS hT e (fun _ => rfl) Uc.toLinearEquiv Vc.toLinearEquiv heq with
      ⟨hd, hf, hi⟩ | ⟨hs, hf, hi⟩
    · exact Or.inl ⟨hd, hf, hi,
        fun x y hx hy => congrArg (fun I : normalPart T => I.val.val) (hf x y hx hy),
        fun z w hz hw => congrArg (fun I : normalPart S => I.val.val) (hi z w hz hw)⟩
    · exact Or.inr ⟨hs, hf, hi,
        fun x y hx hy => congrArg (fun I : normalPart T => I.val.val) (hf x y hx hy),
        fun z w hz hw => congrArg (fun I : normalPart S => I.val.val) (hi z w hz hw)⟩
  · refine Or.inr ⟨Uc, Vc, hU, hV, hUi, hVi, ?_, hinc, hEq⟩
    rcases normalPart_equiv_evaluation_of_semilinear_eq_or_star
        S T hS hT e (fun _ => rfl) Uc.toLinearEquiv Vc.toLinearEquiv heq with
      ⟨hd, hf, hi⟩ | ⟨hs, hf, hi⟩
    · exact Or.inl ⟨hd, hf, hi,
        fun x y hx hy => congrArg (fun I : normalPart T => I.val.val) (hf x y hx hy),
        fun z w hz hw => congrArg (fun I : normalPart S => I.val.val) (hi z w hz hw)⟩
    · exact Or.inr ⟨hs, hf, hi,
        fun x y hx hy => congrArg (fun I : normalPart T => I.val.val) (hf x y hx hy),
        fun z w hz hw => congrArg (fun I : normalPart S => I.val.val) (hi z w hz hw)⟩

/-- The equality terminal requires reverse full continuity in addition to the
inclusion terminal's assumptions. The selected functions, their inverses, the
point equations, the literal kernels, and the same global orientation are all
retained; there is no second choice of a lift at this last step. -/
theorem exists_normalPart_selected_classification_eq
    (hH : ¬ FiniteDimensional ℂ H)
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (hcontInv : ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)) e.toEquiv.symm) :
    let hd := (three_le_rank_of_normalPart_finiteHomeomorph S T hS hT e hH).1
    let U := normalPartFirstSemilinearEquiv S T hS hT e hd
    let V := normalPartSecondSemilinearEquiv S T hS hT e hd
    normalPartFirstScalarEquiv S T hS hT e hd =
      normalPartSecondScalarEquiv S T hS hT e hd ∧
    (
    (∃ Uc Vc : H ≃L[ℂ] K,
      (∀ x, Uc x = U x) ∧ (∀ x, Vc x = V x) ∧
      (∀ z, Uc.symm z = U.symm z) ∧ (∀ z, Vc.symm z = V.symm z) ∧
      (((e.toEquiv = normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
            Uc.toLinearEquiv Vc.toLinearEquiv) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          e.toEquiv (normalPartPoint S hS x y hx hy) =
            normalPartPoint T hT (Uc x) (Vc y)
              (by simpa only [map_zero] using Uc.injective.ne hx)
              (by simpa only [map_zero] using Vc.injective.ne hy)) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          e.toEquiv.symm (normalPartPoint T hT z w hz hw) =
            normalPartPoint S hS (Uc.symm z) (Vc.symm w)
              (by simpa only [map_zero] using Uc.symm.injective.ne hz)
              (by simpa only [map_zero] using Vc.symm.injective.ne hw)) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          (e.toEquiv (normalPartPoint S hS x y hx hy)).val.val =
            {b : T | inner ℂ (Vc y) ((b : K →L[ℂ] K) (Uc x)) = 0}) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          (e.toEquiv.symm (normalPartPoint T hT z w hz hw)).val.val =
            {a : S | inner ℂ (Vc.symm w) ((a : H →L[ℂ] H) (Uc.symm z)) = 0})) ∨
       ((e.toEquiv = (normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
            Uc.toLinearEquiv Vc.toLinearEquiv).trans (normalPartStarHomeomorph T hT).toEquiv) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          e.toEquiv (normalPartPoint S hS x y hx hy) =
            normalPartPoint T hT (Vc y) (Uc x)
              (by simpa only [map_zero] using Vc.injective.ne hy)
              (by simpa only [map_zero] using Uc.injective.ne hx)) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          e.toEquiv.symm (normalPartPoint T hT z w hz hw) =
            normalPartPoint S hS (Uc.symm w) (Vc.symm z)
              (by simpa only [map_zero] using Uc.symm.injective.ne hw)
              (by simpa only [map_zero] using Vc.symm.injective.ne hz)) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          (e.toEquiv (normalPartPoint S hS x y hx hy)).val.val =
            {b : T | inner ℂ (Uc x) ((b : K →L[ℂ] K) (Vc y)) = 0}) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          (e.toEquiv.symm (normalPartPoint T hT z w hz hw)).val.val =
            {a : S | inner ℂ (Vc.symm z) ((a : H →L[ℂ] H) (Uc.symm w)) = 0}))) ∧
      InnerProductSpace.adjointSandwich Uc.toContinuousLinearMap Vc.toContinuousLinearMap ''
        (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H))) ∨
    (∃ Uc Vc : H ≃SL[starRingEnd ℂ] K,
      (∀ x, Uc x = U x) ∧ (∀ x, Vc x = V x) ∧
      (∀ z, Uc.symm z = U.symm z) ∧ (∀ z, Vc.symm z = V.symm z) ∧
      (((e.toEquiv = normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
            Uc.toLinearEquiv Vc.toLinearEquiv) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          e.toEquiv (normalPartPoint S hS x y hx hy) =
            normalPartPoint T hT (Uc x) (Vc y)
              (by simpa only [map_zero] using Uc.injective.ne hx)
              (by simpa only [map_zero] using Vc.injective.ne hy)) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          e.toEquiv.symm (normalPartPoint T hT z w hz hw) =
            normalPartPoint S hS (Uc.symm z) (Vc.symm w)
              (by simpa only [map_zero] using Uc.symm.injective.ne hz)
              (by simpa only [map_zero] using Vc.symm.injective.ne hw)) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          (e.toEquiv (normalPartPoint S hS x y hx hy)).val.val =
            {b : T | inner ℂ (Vc y) ((b : K →L[ℂ] K) (Uc x)) = 0}) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          (e.toEquiv.symm (normalPartPoint T hT z w hz hw)).val.val =
            {a : S | inner ℂ (Vc.symm w) ((a : H →L[ℂ] H) (Uc.symm z)) = 0})) ∨
       ((e.toEquiv = (normalPartSemilinearEquiv S T hS hT (fun _ => rfl)
            Uc.toLinearEquiv Vc.toLinearEquiv).trans (normalPartStarHomeomorph T hT).toEquiv) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          e.toEquiv (normalPartPoint S hS x y hx hy) =
            normalPartPoint T hT (Vc y) (Uc x)
              (by simpa only [map_zero] using Vc.injective.ne hy)
              (by simpa only [map_zero] using Uc.injective.ne hx)) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          e.toEquiv.symm (normalPartPoint T hT z w hz hw) =
            normalPartPoint S hS (Uc.symm w) (Vc.symm z)
              (by simpa only [map_zero] using Uc.symm.injective.ne hw)
              (by simpa only [map_zero] using Vc.symm.injective.ne hz)) ∧
        (∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
          (e.toEquiv (normalPartPoint S hS x y hx hy)).val.val =
            {b : T | inner ℂ (Uc x) ((b : K →L[ℂ] K) (Vc y)) = 0}) ∧
        (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
          (e.toEquiv.symm (normalPartPoint T hT z w hz hw)).val.val =
            {a : S | inner ℂ (Vc.symm z) ((a : H →L[ℂ] H) (Uc.symm w)) = 0}))) ∧
      InnerProductSpace.conjugateAdjointSandwich Uc.toContinuousLinearMap Vc.toContinuousLinearMap ''
        (T : Set (K →L[ℂ] K)) = (S : Set (H →L[ℂ] H)))) := by
  dsimp only
  obtain ⟨hsame, hpair⟩ :=
    exists_normalPart_selected_classification S T hS hT e hH hcont
  refine ⟨hsame, ?_⟩
  rcases hpair with ⟨Uc, Vc, hU, hV, hUi, hVi, heval, _, hEq⟩ |
    ⟨Uc, Vc, hU, hV, hUi, hVi, heval, _, hEq⟩
  · exact Or.inl ⟨Uc, Vc, hU, hV, hUi, hVi, heval, hEq hcontInv⟩
  · exact Or.inr ⟨Uc, Vc, hU, hV, hUi, hVi, heval, hEq hcontInv⟩

end MathlibAnnex.Analysis.CStarAlgebra
