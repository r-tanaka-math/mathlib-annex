/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.FilterPresentation

/-!
# Unit-scalar classes of maximal faces

The fibers of the original face-kernel map are precisely the unit-scalar
orbits of maximal faces. An actual quotient by this relation is then shown
to be equivalent to the already defined geometric structure space. The zero
space needs no special new point: both the face type and its quotient are empty.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Metric

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]

section Seminormed

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem birkhoffJamesKernel_image_smul {a : 𝕜} (ha : a ≠ 0) (C : Set E) :
    birkhoffJamesKernel 𝕜 ((fun x : E => a • x) '' C) = birkhoffJamesKernel 𝕜 C := by
  ext y
  constructor
  · intro hy x hx
    have h := hy (a • x) ⟨x, hx, rfl⟩
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using h.smul a⁻¹ 1
  · rintro hy x ⟨z, hz, rfl⟩
    simpa only [one_smul] using (hy z hz).smul a 1

end Seminormed

section Normed

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Multiplying a functional by a unit scalar rotates its value-one face by
the inverse scalar. This is an equality of actual subset carriers. -/
theorem unitBallSupportFace_smul (f : StrongDual 𝕜 E) {a : 𝕜} (ha : ‖a‖ = 1) :
    unitBallSupportFace 𝕜 (a • f) =
      (fun x : E => a⁻¹ • x) '' unitBallSupportFace 𝕜 f := by
  have ha₀ : a ≠ 0 := norm_ne_zero_iff.mp (ha.trans_ne one_ne_zero)
  ext x
  constructor
  · intro hx
    refine ⟨a • x, ⟨?_, ?_⟩, ?_⟩
    · apply mem_closedBall_zero_iff.mpr
      simpa only [norm_smul, ha, one_mul] using mem_closedBall_zero_iff.mp hx.1
    · change f (a • x) = 1
      rw [map_smul, smul_eq_mul]
      exact hx.2
    · simp only [smul_smul, inv_mul_cancel₀ ha₀, one_smul]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨mem_closedBall_zero_iff.mpr ?_, ?_⟩
    · simpa only [norm_smul, norm_inv, ha, inv_one, one_mul]
        using mem_closedBall_zero_iff.mp hy.1
    · change a * f (a⁻¹ • y) = 1
      rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha₀, one_mul, hy.2]

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- Equality of the original face kernels is exactly equality of faces up to
one scalar of modulus one. No uniqueness of supporting functionals is used. -/
theorem supportKernelUnion_eq_iff_exists_norm_eq_one_smul_image {F G : Set E}
    (hF : IsMaximalFace F) (hG : IsMaximalFace G) :
    supportKernelUnion 𝕜 F = supportKernelUnion 𝕜 G ↔
      ∃ a : 𝕜, ‖a‖ = 1 ∧ (fun x : E => a • x) '' F = G := by
  constructor
  · intro hFG
    obtain ⟨x₀, hx₀⟩ := hF.nonempty
    have hx₀ne : x₀ ≠ 0 := by
      intro heq
      have hn : ‖x₀‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hF.subset_sphere hx₀
      have h01 : (0 : ℝ) = 1 := by simpa only [heq, norm_zero] using hn
      exact zero_ne_one h01
    letI : Nontrivial E := ⟨⟨x₀, 0, hx₀ne⟩⟩
    obtain ⟨U, hFU, hU, hUI⟩ := hF.exists_isMaximalBirkhoffJamesFilter 𝕜
    obtain ⟨V, hGV, hV, hVI⟩ := hG.exists_isMaximalBirkhoffJamesFilter 𝕜
    have hUV : U = V := hU.eq_of_kernel_subset 𝕜 hV (by rw [hUI, hVI, hFG])
    subst V
    obtain ⟨f, hf⟩ := hU.1.exists_common_absoluteNormingFunctional 𝕜
    obtain ⟨a, ha, haf⟩ := exists_norm_eq_one_smul_mem_supportFunctionals 𝕜 hF.nonempty hF.convex
      hF.subset_sphere (fun x hx => hf x (hFU hx))
    obtain ⟨b, hb, hbf⟩ := exists_norm_eq_one_smul_mem_supportFunctionals 𝕜 hG.nonempty hG.convex
      hG.subset_sphere (fun x hx => hf x (hGV hx))
    have ha₀ : a ≠ 0 := norm_ne_zero_iff.mp (ha.trans_ne one_ne_zero)
    refine ⟨b⁻¹ * a, by rw [norm_mul, norm_inv, ha, hb, inv_one, one_mul], ?_⟩
    rw [hF.eq_unitBallSupportFace 𝕜 haf, hG.eq_unitBallSupportFace 𝕜 hbf,
      unitBallSupportFace_smul 𝕜 f ha, unitBallSupportFace_smul 𝕜 f hb, image_image]
    have heq : (fun x : E => (b⁻¹ * a) • (a⁻¹ • x)) = fun x : E => b⁻¹ • x := by
      funext x
      simp only [smul_smul, mul_assoc, mul_inv_cancel₀ ha₀, mul_one]
    exact congrArg (fun q : E → E => q '' unitBallSupportFace 𝕜 f) heq
  · rintro ⟨a, ha, hFG⟩
    have ha₀ : a ≠ 0 := norm_ne_zero_iff.mp (ha.trans_ne one_ne_zero)
    calc
      supportKernelUnion 𝕜 F = birkhoffJamesKernel 𝕜 F :=
        (birkhoffJamesKernel_eq_supportKernelUnion 𝕜 hF.nonempty hF.convex hF.subset_sphere).symm
      _ = birkhoffJamesKernel 𝕜 G := by rw [← hFG, birkhoffJamesKernel_image_smul 𝕜 ha₀]
      _ = supportKernelUnion 𝕜 G :=
        birkhoffJamesKernel_eq_supportKernelUnion 𝕜 hG.nonempty hG.convex hG.subset_sphere

end Normed

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Maximal faces with the same canonical real scalar restriction as the
original geometric structure space. -/
def MaximalUnitBallFace : Type u :=
  letI : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  {F : Set E // IsMaximalFace F}

namespace MaximalUnitBallFace

/-- The original union-of-kernels map on maximal faces. -/
def toGeometricStructureSpace (F : MaximalUnitBallFace 𝕜 E) : GeometricStructureSpace 𝕜 E := by
  letI : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  exact ⟨supportKernelUnion 𝕜 F.val, F.val, F.property, rfl⟩

theorem toGeometricStructureSpace_eq_iff (F G : MaximalUnitBallFace 𝕜 E) :
    toGeometricStructureSpace 𝕜 E F = toGeometricStructureSpace 𝕜 E G ↔
      ∃ a : 𝕜, ‖a‖ = 1 ∧ (fun x : E => a • x) '' F.val = G.val := by
  letI : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  constructor
  · intro h
    exact (supportKernelUnion_eq_iff_exists_norm_eq_one_smul_image 𝕜
      F.property G.property).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((supportKernelUnion_eq_iff_exists_norm_eq_one_smul_image 𝕜
      F.property G.property).mpr h)

theorem toGeometricStructureSpace_surjective :
    Function.Surjective (toGeometricStructureSpace 𝕜 E) := by
  letI : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  intro I
  obtain ⟨F, hF, hFI⟩ := I.property
  exact ⟨⟨F, hF⟩, Subtype.ext hFI⟩

/-- The relation is explicitly unit-scalar equivalence, not an opaque
assumption that two face kernels agree. The previous theorem proves that
these two descriptions coincide. -/
def unitScalarSetoid : Setoid (MaximalUnitBallFace 𝕜 E) where
  r F G := ∃ a : 𝕜, ‖a‖ = 1 ∧ (fun x : E => a • x) '' F.val = G.val
  iseqv :=
    ⟨fun F => (toGeometricStructureSpace_eq_iff 𝕜 E F F).mp rfl,
      fun {F G} h => (toGeometricStructureSpace_eq_iff 𝕜 E G F).mp
        ((toGeometricStructureSpace_eq_iff 𝕜 E F G).mpr h).symm,
      fun {F G H} hFG hGH => (toGeometricStructureSpace_eq_iff 𝕜 E F H).mp
        (((toGeometricStructureSpace_eq_iff 𝕜 E F G).mpr hFG).trans
          ((toGeometricStructureSpace_eq_iff 𝕜 E G H).mpr hGH))⟩

/-- The map from the actual unit-scalar quotient of maximal faces. -/
def quotientToGeometricStructureSpace :
    Quotient (unitScalarSetoid 𝕜 E) → GeometricStructureSpace 𝕜 E :=
  Quotient.lift (toGeometricStructureSpace 𝕜 E)
    (fun F G h => (toGeometricStructureSpace_eq_iff 𝕜 E F G).mpr h)

theorem quotientToGeometricStructureSpace_bijective :
    Function.Bijective (quotientToGeometricStructureSpace 𝕜 E) := by
  constructor
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro F G hFG
    exact Quotient.sound ((toGeometricStructureSpace_eq_iff 𝕜 E F G).mp hFG)
  · intro I
    obtain ⟨F, hF⟩ := toGeometricStructureSpace_surjective 𝕜 E I
    exact ⟨Quotient.mk (unitScalarSetoid 𝕜 E) F, hF⟩

/-- The phase quotient is equivalent to the face-defined geometric structure
space, including when both are empty. -/
def quotientEquivGeometricStructureSpace :
    Quotient (unitScalarSetoid 𝕜 E) ≃ GeometricStructureSpace 𝕜 E :=
  Equiv.ofBijective (quotientToGeometricStructureSpace 𝕜 E)
    (quotientToGeometricStructureSpace_bijective 𝕜 E)

end MaximalUnitBallFace

end NormedSpace
