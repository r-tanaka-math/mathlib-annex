/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartSemilinearRealization
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartClosedSubspace

/-!
# The same normal-part semilinear lifts on algebraic subspaces

The chosen lifts from `NormalPartSemilinearRealization` realize the already
constructed first and second order isomorphisms on ALL algebraic submodules.
Forward images and inverse images are recorded separately. Zero belongs to
every submodule and is treated without creating a projective zero point.

Full forward continuity of the specified normal-part map is an extra hypothesis.
It implies closed inverse images for these SAME lifts, equivalently closed
forward images under their inverses. It does not give closed forward images
under the original lifts by an interchange of the two directions. No regularity
theorem, boundedness, or equality of scalar automorphisms is asserted here.
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
local instance (σ : ℂ ≃+* ℂ) : RingHomSurjective σ.toRingHom :=
  ⟨σ.surjective⟩

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

/-- Evaluation of the first order isomorphism by the inverse of its selected lift. -/
theorem mem_normalPartFirstSubmoduleOrderIso_iff_semilinearEquiv
    (M : Submodule ℂ H) (z : K) :
    z ∈ normalPartFirstSubmoduleOrderIso S T hS hT e M ↔
      (normalPartFirstSemilinearEquiv S T hS hT e hdim).symm z ∈ M := by
  by_cases hz : z = 0
  · subst z
    simp only [map_zero, Submodule.zero_mem, iff_self]
  · have h := mem_projectivization_normalPartFirstSubmoduleOrderIso_iff
      S T hS hT e M (Projectivization.mk ℂ z hz)
    rw [Submodule.mk_mem_projectivization_iff,
      normalPartProjectiveFirstFactor_symm_mk S T hS hT e hdim,
      Submodule.mk_mem_projectivization_iff] at h
    exact h

/-- The first inverse order map is the inverse image under the SAME lift. -/
theorem mem_symm_normalPartFirstSubmoduleOrderIso_iff_semilinearEquiv
    (N : Submodule ℂ K) (x : H) :
    x ∈ (normalPartFirstSubmoduleOrderIso S T hS hT e).symm N ↔
      normalPartFirstSemilinearEquiv S T hS hT e hdim x ∈ N := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, Submodule.zero_mem, iff_self]
  · rw [mem_symm_normalPartFirstSubmoduleOrderIso_iff S T hS hT e N x hx,
      normalPartProjectiveFirstFactor_mk S T hS hT e hdim,
      Submodule.mk_mem_projectivization_iff]

/-- The first order map on all algebraic submodules is the semilinear image map. -/
theorem normalPartFirstSubmoduleOrderIso_eq_map_semilinearEquiv
    (M : Submodule ℂ H) :
    normalPartFirstSubmoduleOrderIso S T hS hT e M =
      M.map (normalPartFirstSemilinearEquiv S T hS hT e hdim).toLinearMap := by
  let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
  ext z
  rw [mem_normalPartFirstSubmoduleOrderIso_iff_semilinearEquiv S T hS hT e hdim]
  constructor
  · intro hz
    exact Submodule.mem_map.mpr ⟨U.symm z, hz, U.apply_symm_apply z⟩
  · intro hz
    obtain ⟨x, hx, h⟩ := Submodule.mem_map.mp hz
    have hxz : U x = z := h
    rw [← hxz, U.symm_apply_apply]
    exact hx

/-- The first inverse order map as an actual semilinear comap. -/
theorem symm_normalPartFirstSubmoduleOrderIso_eq_comap_semilinearEquiv
    (N : Submodule ℂ K) :
    (normalPartFirstSubmoduleOrderIso S T hS hT e).symm N =
      N.comap (normalPartFirstSemilinearEquiv S T hS hT e hdim).toLinearMap := by
  ext x
  exact mem_symm_normalPartFirstSubmoduleOrderIso_iff_semilinearEquiv S T hS hT e hdim N x

/-- The same inverse order map is the forward image under the inverse lift. -/
theorem symm_normalPartFirstSubmoduleOrderIso_eq_map_symm_semilinearEquiv
    (N : Submodule ℂ K) :
    (normalPartFirstSubmoduleOrderIso S T hS hT e).symm N =
      N.map (normalPartFirstSemilinearEquiv S T hS hT e hdim).symm.toLinearMap := by
  let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
  ext x
  rw [mem_symm_normalPartFirstSubmoduleOrderIso_iff_semilinearEquiv S T hS hT e hdim]
  constructor
  · intro hx
    exact Submodule.mem_map.mpr ⟨U x, hx, U.symm_apply_apply x⟩
  · intro hx
    obtain ⟨z, hz, h⟩ := Submodule.mem_map.mp hx
    have hzx : U.symm z = x := h
    rw [← hzx, U.apply_symm_apply]
    exact hz

/-- Literal set-valued image formula; no closed-subspace restriction. -/
theorem coe_normalPartFirstSubmoduleOrderIso_eq_image
    (M : Submodule ℂ H) :
    (normalPartFirstSubmoduleOrderIso S T hS hT e M : Set K) =
      normalPartFirstSemilinearEquiv S T hS hT e hdim '' (M : Set H) := by
  let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
  ext z
  change z ∈ normalPartFirstSubmoduleOrderIso S T hS hT e M ↔ z ∈ U '' (M : Set H)
  rw [mem_normalPartFirstSubmoduleOrderIso_iff_semilinearEquiv S T hS hT e hdim]
  constructor
  · intro hz
    exact ⟨U.symm z, hz, U.apply_symm_apply z⟩
  · rintro ⟨x, hx, h⟩
    rw [← h, U.symm_apply_apply]
    exact hx

/-- Literal set-valued inverse-image formula, including zero and the whole space. -/
theorem coe_symm_normalPartFirstSubmoduleOrderIso_eq_preimage
    (N : Submodule ℂ K) :
    ((normalPartFirstSubmoduleOrderIso S T hS hT e).symm N : Set H) =
      normalPartFirstSemilinearEquiv S T hS hT e hdim ⁻¹' (N : Set K) := by
  ext x
  exact mem_symm_normalPartFirstSubmoduleOrderIso_iff_semilinearEquiv S T hS hT e hdim N x

/-- The image under the inverse lift is precisely the inverse image under the lift. -/
theorem normalPartFirstSemilinearEquiv_symm_image_eq_preimage
    (N : Set K) :
    (normalPartFirstSemilinearEquiv S T hS hT e hdim).symm '' N =
      normalPartFirstSemilinearEquiv S T hS hT e hdim ⁻¹' N := by
  let U := normalPartFirstSemilinearEquiv S T hS hT e hdim
  ext x
  constructor
  · rintro ⟨z, hz, h⟩
    change U x ∈ N
    rw [← h, U.apply_symm_apply]
    exact hz
  · intro hx
    exact ⟨U x, hx, U.symm_apply_apply x⟩

/-- Full forward continuity yields closed inverse images under the first lift.
Finite continuity alone is not used in place of this additional hypothesis. -/
theorem isClosed_preimage_normalPartFirstSemilinearEquiv
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (N : Submodule ℂ K) (hN : IsClosed (N : Set K)) :
    IsClosed (normalPartFirstSemilinearEquiv S T hS hT e hdim ⁻¹' (N : Set K)) := by
  rw [← coe_symm_normalPartFirstSubmoduleOrderIso_eq_preimage S T hS hT e hdim N]
  exact isClosed_symm_normalPartFirstSubmoduleOrderIso S hS T hT e hcont N hN

/-- Correct direction for forward-hyperplane regularity: apply it to the INVERSE
semilinear map, whose forward images of closed subspaces are now proved closed. -/
theorem isClosed_image_symm_normalPartFirstSemilinearEquiv
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (N : Submodule ℂ K) (hN : IsClosed (N : Set K)) :
    IsClosed ((normalPartFirstSemilinearEquiv S T hS hT e hdim).symm '' (N : Set K)) := by
  rw [normalPartFirstSemilinearEquiv_symm_image_eq_preimage]
  exact isClosed_preimage_normalPartFirstSemilinearEquiv S T hS hT e hdim hcont N hN

/-- Evaluation of the second order isomorphism by the inverse of its selected lift. -/
theorem mem_normalPartSecondSubmoduleOrderIso_iff_semilinearEquiv
    (M : Submodule ℂ H) (z : K) :
    z ∈ normalPartSecondSubmoduleOrderIso S T hS hT e M ↔
      (normalPartSecondSemilinearEquiv S T hS hT e hdim).symm z ∈ M := by
  by_cases hz : z = 0
  · subst z
    simp only [map_zero, Submodule.zero_mem, iff_self]
  · have h := mem_projectivization_normalPartSecondSubmoduleOrderIso_iff
      S T hS hT e M (Projectivization.mk ℂ z hz)
    rw [Submodule.mk_mem_projectivization_iff,
      normalPartProjectiveSecondFactor_symm_mk S T hS hT e hdim,
      Submodule.mk_mem_projectivization_iff] at h
    exact h

/-- The second inverse order map is the inverse image under the SAME lift. -/
theorem mem_symm_normalPartSecondSubmoduleOrderIso_iff_semilinearEquiv
    (N : Submodule ℂ K) (x : H) :
    x ∈ (normalPartSecondSubmoduleOrderIso S T hS hT e).symm N ↔
      normalPartSecondSemilinearEquiv S T hS hT e hdim x ∈ N := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, Submodule.zero_mem, iff_self]
  · rw [mem_symm_normalPartSecondSubmoduleOrderIso_iff S T hS hT e N x hx,
      normalPartProjectiveSecondFactor_mk S T hS hT e hdim,
      Submodule.mk_mem_projectivization_iff]

/-- The second order map on all algebraic submodules is the semilinear image map. -/
theorem normalPartSecondSubmoduleOrderIso_eq_map_semilinearEquiv
    (M : Submodule ℂ H) :
    normalPartSecondSubmoduleOrderIso S T hS hT e M =
      M.map (normalPartSecondSemilinearEquiv S T hS hT e hdim).toLinearMap := by
  let U := normalPartSecondSemilinearEquiv S T hS hT e hdim
  ext z
  rw [mem_normalPartSecondSubmoduleOrderIso_iff_semilinearEquiv S T hS hT e hdim]
  constructor
  · intro hz
    exact Submodule.mem_map.mpr ⟨U.symm z, hz, U.apply_symm_apply z⟩
  · intro hz
    obtain ⟨x, hx, h⟩ := Submodule.mem_map.mp hz
    have hxz : U x = z := h
    rw [← hxz, U.symm_apply_apply]
    exact hx

/-- The second inverse order map as an actual semilinear comap. -/
theorem symm_normalPartSecondSubmoduleOrderIso_eq_comap_semilinearEquiv
    (N : Submodule ℂ K) :
    (normalPartSecondSubmoduleOrderIso S T hS hT e).symm N =
      N.comap (normalPartSecondSemilinearEquiv S T hS hT e hdim).toLinearMap := by
  ext x
  exact mem_symm_normalPartSecondSubmoduleOrderIso_iff_semilinearEquiv S T hS hT e hdim N x

/-- The same inverse order map is the forward image under the inverse lift. -/
theorem symm_normalPartSecondSubmoduleOrderIso_eq_map_symm_semilinearEquiv
    (N : Submodule ℂ K) :
    (normalPartSecondSubmoduleOrderIso S T hS hT e).symm N =
      N.map (normalPartSecondSemilinearEquiv S T hS hT e hdim).symm.toLinearMap := by
  let U := normalPartSecondSemilinearEquiv S T hS hT e hdim
  ext x
  rw [mem_symm_normalPartSecondSubmoduleOrderIso_iff_semilinearEquiv S T hS hT e hdim]
  constructor
  · intro hx
    exact Submodule.mem_map.mpr ⟨U x, hx, U.symm_apply_apply x⟩
  · intro hx
    obtain ⟨z, hz, h⟩ := Submodule.mem_map.mp hx
    have hzx : U.symm z = x := h
    rw [← hzx, U.apply_symm_apply]
    exact hz

/-- Literal set-valued image formula; no closed-subspace restriction. -/
theorem coe_normalPartSecondSubmoduleOrderIso_eq_image
    (M : Submodule ℂ H) :
    (normalPartSecondSubmoduleOrderIso S T hS hT e M : Set K) =
      normalPartSecondSemilinearEquiv S T hS hT e hdim '' (M : Set H) := by
  let U := normalPartSecondSemilinearEquiv S T hS hT e hdim
  ext z
  change z ∈ normalPartSecondSubmoduleOrderIso S T hS hT e M ↔ z ∈ U '' (M : Set H)
  rw [mem_normalPartSecondSubmoduleOrderIso_iff_semilinearEquiv S T hS hT e hdim]
  constructor
  · intro hz
    exact ⟨U.symm z, hz, U.apply_symm_apply z⟩
  · rintro ⟨x, hx, h⟩
    rw [← h, U.symm_apply_apply]
    exact hx

/-- Literal set-valued inverse-image formula, including zero and the whole space. -/
theorem coe_symm_normalPartSecondSubmoduleOrderIso_eq_preimage
    (N : Submodule ℂ K) :
    ((normalPartSecondSubmoduleOrderIso S T hS hT e).symm N : Set H) =
      normalPartSecondSemilinearEquiv S T hS hT e hdim ⁻¹' (N : Set K) := by
  ext x
  exact mem_symm_normalPartSecondSubmoduleOrderIso_iff_semilinearEquiv S T hS hT e hdim N x

/-- The image under the inverse lift is precisely the inverse image under the lift. -/
theorem normalPartSecondSemilinearEquiv_symm_image_eq_preimage
    (N : Set K) :
    (normalPartSecondSemilinearEquiv S T hS hT e hdim).symm '' N =
      normalPartSecondSemilinearEquiv S T hS hT e hdim ⁻¹' N := by
  let U := normalPartSecondSemilinearEquiv S T hS hT e hdim
  ext x
  constructor
  · rintro ⟨z, hz, h⟩
    change U x ∈ N
    rw [← h, U.apply_symm_apply]
    exact hz
  · intro hx
    exact ⟨U x, hx, U.symm_apply_apply x⟩

/-- Full forward continuity yields closed inverse images under the second lift.
Finite continuity alone is not used in place of this additional hypothesis. -/
theorem isClosed_preimage_normalPartSecondSemilinearEquiv
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (N : Submodule ℂ K) (hN : IsClosed (N : Set K)) :
    IsClosed (normalPartSecondSemilinearEquiv S T hS hT e hdim ⁻¹' (N : Set K)) := by
  rw [← coe_symm_normalPartSecondSubmoduleOrderIso_eq_preimage S T hS hT e hdim N]
  exact isClosed_symm_normalPartSecondSubmoduleOrderIso S hS T hT e hcont N hN

/-- Correct direction for forward-hyperplane regularity: apply it to the INVERSE
semilinear map, whose forward images of closed subspaces are now proved closed. -/
theorem isClosed_image_symm_normalPartSecondSemilinearEquiv
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (N : Submodule ℂ K) (hN : IsClosed (N : Set K)) :
    IsClosed ((normalPartSecondSemilinearEquiv S T hS hT e hdim).symm '' (N : Set K)) := by
  rw [normalPartSecondSemilinearEquiv_symm_image_eq_preimage]
  exact isClosed_preimage_normalPartSecondSemilinearEquiv S T hS hT e hdim hcont N hN

/-- Both selected lifts have closed inverse images under the SAME original
forward continuity assumption, in either global orientation. -/
theorem normalPart_semilinear_factors_isClosed_preimage
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (N : Submodule ℂ K) (hN : IsClosed (N : Set K)) :
    IsClosed (normalPartFirstSemilinearEquiv S T hS hT e hdim ⁻¹' (N : Set K)) ∧
      IsClosed (normalPartSecondSemilinearEquiv S T hS hT e hdim ⁻¹' (N : Set K)) :=
  ⟨isClosed_preimage_normalPartFirstSemilinearEquiv S T hS hT e hdim hcont N hN,
    isClosed_preimage_normalPartSecondSemilinearEquiv S T hS hT e hdim hcont N hN⟩

/-- Readiness for a later regularity theorem on the inverse maps. This is not
an application of an unsupplied regularity theorem and claims no boundedness. -/
theorem normalPart_semilinear_factors_isClosed_image_symm
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (N : Submodule ℂ K) (hN : IsClosed (N : Set K)) :
    IsClosed ((normalPartFirstSemilinearEquiv S T hS hT e hdim).symm '' (N : Set K)) ∧
      IsClosed ((normalPartSecondSemilinearEquiv S T hS hT e hdim).symm '' (N : Set K)) :=
  ⟨isClosed_image_symm_normalPartFirstSemilinearEquiv S T hS hT e hdim hcont N hN,
    isClosed_image_symm_normalPartSecondSemilinearEquiv S T hS hT e hdim hcont N hN⟩

end MathlibAnnex.Analysis.CStarAlgebra
