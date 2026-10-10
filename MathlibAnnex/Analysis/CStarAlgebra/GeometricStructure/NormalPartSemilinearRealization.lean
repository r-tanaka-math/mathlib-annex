/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartProjectiveIncidence
import MathlibAnnex.LinearAlgebra.Projectivization.Semilinear

/-!
# Semilinear realization of the actual normal-part factors

Both factors are those already selected jointly from the specified finite
homeomorphism. The finite-span iff is reversed before applying the general
field theorem. The two scalar automorphisms are chosen independently: neither
their equality nor any regularity, involutivity, or star compatibility is assumed.

The evaluation theorem is an equality in the existing normal-part subtype,
with one global orientation and its matching inverse. All nonzero vector
representatives are allowed, not just basis rays or an affine chart.
The rank condition is algebraic cardinal rank, not Hilbert dimension.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped LinearAlgebra.Projectivization

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
variable (hdim : 3 ≤ Module.rank ℂ H)

/-- Apply the all-ray field theorem to the ACTUAL first projective factor. -/
theorem exists_normalPart_first_semilinearEquiv (hdim : 3 ≤ Module.rank ℂ H) :
    ∃ σ : ℂ ≃+* ℂ, ∃ U : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) H K,
      ∀ (x : H) (hx : x ≠ 0),
        normalPartProjectiveFirstFactor S T hS hT e (Projectivization.mk ℂ x hx) =
          Projectivization.mk ℂ (U x)
            (by simpa only [map_zero] using U.injective.ne hx) :=
  Projectivization.exists_semilinearEquiv_of_finite_span
    (normalPartProjectiveFirstFactor S T hS hT e)
    (fun s hs p => ((normalPart_projective_factors_spec S T hS hT e).1 s hs p).symm)
    hdim

/-- The scalar automorphism supplied by the proved first-factor existence theorem. -/
def normalPartFirstScalarEquiv : ℂ ≃+* ℂ :=
  Classical.choose (exists_normalPart_first_semilinearEquiv S T hS hT e hdim)

/-- The selected first lift; this selection is made only after existence is proved. -/
def normalPartFirstSemilinearEquiv :
    LinearEquiv (normalPartFirstScalarEquiv S T hS hT e hdim).toRingHom (σ' := (normalPartFirstScalarEquiv S T hS hT e hdim).symm.toRingHom) H K :=
  Classical.choose (Classical.choose_spec
    (exists_normalPart_first_semilinearEquiv S T hS hT e hdim))

/-- The selected lift realizes the first factor on every nonzero ray. -/
theorem normalPartProjectiveFirstFactor_mk (x : H) (hx : x ≠ 0) :
    normalPartProjectiveFirstFactor S T hS hT e (Projectivization.mk ℂ x hx) =
      Projectivization.mk ℂ (normalPartFirstSemilinearEquiv S T hS hT e hdim x)
        (by simpa only [map_zero] using
          (normalPartFirstSemilinearEquiv S T hS hT e hdim).injective.ne hx) :=
  Classical.choose_spec (Classical.choose_spec
    (exists_normalPart_first_semilinearEquiv S T hS hT e hdim)) x hx

/-- The inverse of the same selected lift realizes the inverse first factor. -/
theorem normalPartProjectiveFirstFactor_symm_mk (z : K) (hz : z ≠ 0) :
    (normalPartProjectiveFirstFactor S T hS hT e).symm (Projectivization.mk ℂ z hz) =
      Projectivization.mk ℂ ((normalPartFirstSemilinearEquiv S T hS hT e hdim).symm z)
        (by simpa only [map_zero] using
          (normalPartFirstSemilinearEquiv S T hS hT e hdim).symm.injective.ne hz) := by
  apply (normalPartProjectiveFirstFactor S T hS hT e).injective
  rw [Equiv.apply_symm_apply, normalPartProjectiveFirstFactor_mk S T hS hT e hdim]
  simp only [LinearEquiv.apply_symm_apply]

/-- Equality on the entire projectivization, not just selected representatives. -/
theorem normalPartFirstSemilinearEquiv_projective_map :
    Projectivization.map (normalPartFirstSemilinearEquiv S T hS hT e hdim).toLinearMap
      (normalPartFirstSemilinearEquiv S T hS hT e hdim).injective =
        normalPartProjectiveFirstFactor S T hS hT e := by
  funext p
  induction p using Projectivization.ind with
  | h x hx =>
    rw [Projectivization.map_mk]
    exact (normalPartProjectiveFirstFactor_mk S T hS hT e hdim x hx).symm

/-- The all-point inverse formula uses the same automorphism and its actual inverse. -/
theorem normalPartFirstSemilinearEquiv_symm_projective_map :
    Projectivization.map
      (normalPartFirstSemilinearEquiv S T hS hT e hdim).symm.toLinearMap
      (normalPartFirstSemilinearEquiv S T hS hT e hdim).symm.injective =
        (normalPartProjectiveFirstFactor S T hS hT e).symm := by
  funext p
  induction p using Projectivization.ind with
  | h z hz =>
    rw [Projectivization.map_mk]
    exact (normalPartProjectiveFirstFactor_symm_mk S T hS hT e hdim z hz).symm

/-- Apply the all-ray field theorem to the ACTUAL second projective factor. -/
theorem exists_normalPart_second_semilinearEquiv (hdim : 3 ≤ Module.rank ℂ H) :
    ∃ σ : ℂ ≃+* ℂ, ∃ U : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) H K,
      ∀ (x : H) (hx : x ≠ 0),
        normalPartProjectiveSecondFactor S T hS hT e (Projectivization.mk ℂ x hx) =
          Projectivization.mk ℂ (U x)
            (by simpa only [map_zero] using U.injective.ne hx) :=
  Projectivization.exists_semilinearEquiv_of_finite_span
    (normalPartProjectiveSecondFactor S T hS hT e)
    (fun s hs p => ((normalPart_projective_factors_spec S T hS hT e).2.1 s hs p).symm)
    hdim

/-- The scalar automorphism supplied by the proved second-factor existence theorem. -/
def normalPartSecondScalarEquiv : ℂ ≃+* ℂ :=
  Classical.choose (exists_normalPart_second_semilinearEquiv S T hS hT e hdim)

/-- The selected second lift; this selection is made only after existence is proved. -/
def normalPartSecondSemilinearEquiv :
    LinearEquiv (normalPartSecondScalarEquiv S T hS hT e hdim).toRingHom (σ' := (normalPartSecondScalarEquiv S T hS hT e hdim).symm.toRingHom) H K :=
  Classical.choose (Classical.choose_spec
    (exists_normalPart_second_semilinearEquiv S T hS hT e hdim))

/-- The selected lift realizes the second factor on every nonzero ray. -/
theorem normalPartProjectiveSecondFactor_mk (x : H) (hx : x ≠ 0) :
    normalPartProjectiveSecondFactor S T hS hT e (Projectivization.mk ℂ x hx) =
      Projectivization.mk ℂ (normalPartSecondSemilinearEquiv S T hS hT e hdim x)
        (by simpa only [map_zero] using
          (normalPartSecondSemilinearEquiv S T hS hT e hdim).injective.ne hx) :=
  Classical.choose_spec (Classical.choose_spec
    (exists_normalPart_second_semilinearEquiv S T hS hT e hdim)) x hx

/-- The inverse of the same selected lift realizes the inverse second factor. -/
theorem normalPartProjectiveSecondFactor_symm_mk (z : K) (hz : z ≠ 0) :
    (normalPartProjectiveSecondFactor S T hS hT e).symm (Projectivization.mk ℂ z hz) =
      Projectivization.mk ℂ ((normalPartSecondSemilinearEquiv S T hS hT e hdim).symm z)
        (by simpa only [map_zero] using
          (normalPartSecondSemilinearEquiv S T hS hT e hdim).symm.injective.ne hz) := by
  apply (normalPartProjectiveSecondFactor S T hS hT e).injective
  rw [Equiv.apply_symm_apply, normalPartProjectiveSecondFactor_mk S T hS hT e hdim]
  simp only [LinearEquiv.apply_symm_apply]

/-- Equality on the entire projectivization, not just selected representatives. -/
theorem normalPartSecondSemilinearEquiv_projective_map :
    Projectivization.map (normalPartSecondSemilinearEquiv S T hS hT e hdim).toLinearMap
      (normalPartSecondSemilinearEquiv S T hS hT e hdim).injective =
        normalPartProjectiveSecondFactor S T hS hT e := by
  funext p
  induction p using Projectivization.ind with
  | h x hx =>
    rw [Projectivization.map_mk]
    exact (normalPartProjectiveSecondFactor_mk S T hS hT e hdim x hx).symm

/-- The all-point inverse formula uses the same automorphism and its actual inverse. -/
theorem normalPartSecondSemilinearEquiv_symm_projective_map :
    Projectivization.map
      (normalPartSecondSemilinearEquiv S T hS hT e hdim).symm.toLinearMap
      (normalPartSecondSemilinearEquiv S T hS hT e hdim).symm.injective =
        (normalPartProjectiveSecondFactor S T hS hT e).symm := by
  funext p
  induction p using Projectivization.ind with
  | h z hz =>
    rw [Projectivization.map_mk]
    exact (normalPartProjectiveSecondFactor_symm_mk S T hS hT e hdim z hz).symm

/-- The specified normal-part map is realized on ALL coefficient kernels.
Forward and inverse formulas lie in the SAME global orientation. The quantifier
on the choice of orientation is outside the vector quantifiers. -/
theorem normalPart_semilinear_factors_evaluation :
    let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
    let V := normalPartSecondSemilinearEquiv S T hS hT e hdim
    ((∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
      e.toEquiv (normalPartPoint S hS x y hx hy) =
        normalPartPoint T hT (U x) (V y)
          (by simpa only [map_zero] using U.injective.ne hx)
          (by simpa only [map_zero] using V.injective.ne hy)) ∧
     (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
      e.toEquiv.symm (normalPartPoint T hT z w hz hw) =
        normalPartPoint S hS (U.symm z) (V.symm w)
          (by simpa only [map_zero] using U.symm.injective.ne hz)
          (by simpa only [map_zero] using V.symm.injective.ne hw))) ∨
    ((∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
      e.toEquiv (normalPartPoint S hS x y hx hy) =
        normalPartPoint T hT (V y) (U x)
          (by simpa only [map_zero] using V.injective.ne hy)
          (by simpa only [map_zero] using U.injective.ne hx)) ∧
     (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
      e.toEquiv.symm (normalPartPoint T hT z w hz hw) =
        normalPartPoint S hS (U.symm w) (V.symm z)
          (by simpa only [map_zero] using U.symm.injective.ne hw)
          (by simpa only [map_zero] using V.symm.injective.ne hz))) := by
  dsimp only
  rcases normalPart_projective_factors_evaluation S T hS hT e with ⟨hf, hi⟩ | ⟨hf, hi⟩
  · refine Or.inl ⟨?_, ?_⟩
    · intro x y hx hy
      simpa only [normalPartProjectiveFirstFactor_mk S T hS hT e hdim,
        normalPartProjectiveSecondFactor_mk S T hS hT e hdim,
        normalPartProjectivizationEquiv_mk] using
        hf (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy)
    · intro z w hz hw
      simpa only [normalPartProjectiveFirstFactor_symm_mk S T hS hT e hdim,
        normalPartProjectiveSecondFactor_symm_mk S T hS hT e hdim,
        normalPartProjectivizationEquiv_mk] using
        hi (Projectivization.mk ℂ z hz, Projectivization.mk ℂ w hw)
  · refine Or.inr ⟨?_, ?_⟩
    · intro x y hx hy
      simpa only [normalPartProjectiveFirstFactor_mk S T hS hT e hdim,
        normalPartProjectiveSecondFactor_mk S T hS hT e hdim,
        normalPartProjectivizationEquiv_mk] using
        hf (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy)
    · intro z w hz hw
      simpa only [normalPartProjectiveFirstFactor_symm_mk S T hS hT e hdim,
        normalPartProjectiveSecondFactor_symm_mk S T hS hT e hdim,
        normalPartProjectivizationEquiv_mk] using
        hi (Projectivization.mk ℂ z hz, Projectivization.mk ℂ w hw)

/-- Literal underlying-kernel equations in both directions. The second vector
occurs in the conjugate-linear slot of the Hilbert inner product. -/
theorem normalPart_semilinear_factors_kernel_evaluation :
    let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
    let V := normalPartSecondSemilinearEquiv S T hS hT e hdim
    ((∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
      (e.toEquiv (normalPartPoint S hS x y hx hy)).val.val =
        {b : T | inner ℂ (V y) ((b : K →L[ℂ] K) (U x)) = 0}) ∧
     (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
      (e.toEquiv.symm (normalPartPoint T hT z w hz hw)).val.val =
        {a : S | inner ℂ (V.symm w) ((a : H →L[ℂ] H) (U.symm z)) = 0})) ∨
    ((∀ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0),
      (e.toEquiv (normalPartPoint S hS x y hx hy)).val.val =
        {b : T | inner ℂ (U x) ((b : K →L[ℂ] K) (V y)) = 0}) ∧
     (∀ (z w : K) (hz : z ≠ 0) (hw : w ≠ 0),
      (e.toEquiv.symm (normalPartPoint T hT z w hz hw)).val.val =
        {a : S | inner ℂ (V.symm z) ((a : H →L[ℂ] H) (U.symm w)) = 0})) := by
  dsimp only
  rcases normalPart_semilinear_factors_evaluation S T hS hT e hdim with
    ⟨hf, hi⟩ | ⟨hf, hi⟩
  · exact Or.inl ⟨fun x y hx hy =>
      congrArg (fun I : normalPart T => I.val.val) (hf x y hx hy),
      fun z w hz hw => congrArg (fun I : normalPart S => I.val.val) (hi z w hz hw)⟩
  · exact Or.inr ⟨fun x y hx hy =>
      congrArg (fun I : normalPart T => I.val.val) (hf x y hx hy),
      fun z w hz hw => congrArg (fun I : normalPart S => I.val.val) (hi z w hz hw)⟩

/-- Independent changes of nonzero representatives do not change the realized
normal kernel. The two unrelated scalar automorphisms remain visible. -/
theorem normalPart_semilinear_factors_smul_smul
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
    let V := normalPartSecondSemilinearEquiv S T hS hT e hdim
    normalPartPoint T hT (U (a • x)) (V (b • y))
        (by simpa only [map_zero] using U.injective.ne (smul_ne_zero ha hx))
        (by simpa only [map_zero] using V.injective.ne (smul_ne_zero hb hy)) =
      normalPartPoint T hT (U x) (V y)
        (by simpa only [map_zero] using U.injective.ne hx)
        (by simpa only [map_zero] using V.injective.ne hy) := by
  let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
  let V := normalPartSecondSemilinearEquiv S T hS hT e hdim
  have hUa : normalPartFirstScalarEquiv S T hS hT e hdim a ≠ 0 := by
    simpa only [map_zero] using
      (normalPartFirstScalarEquiv S T hS hT e hdim).injective.ne ha
  have hVb : normalPartSecondScalarEquiv S T hS hT e hdim b ≠ 0 := by
    simpa only [map_zero] using
      (normalPartSecondScalarEquiv S T hS hT e hdim).injective.ne hb
  simpa only [U, V, map_smulₛₗ, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom] using
    normalPartPoint_smul_smul T hT (U x) (V y)
      (by simpa only [map_zero] using U.injective.ne hx)
      (by simpa only [map_zero] using V.injective.ne hy)
      (normalPartFirstScalarEquiv S T hS hT e hdim a)
      (normalPartSecondScalarEquiv S T hS hT e hdim b) hUa hVb

end MathlibAnnex.Analysis.CStarAlgebra
