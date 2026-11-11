/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.Kernel
import MathlibAnnex.Analysis.VonNeumannAlgebra.KaplanskyDensity
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Corner
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Surjectivity onto the generated von Neumann algebra

Bounded self-adjoint Kaplansky density is applied to the actual extension on
the all-state envelope. Its bounded images are WOT compact by the existing
literal-bidual compactness theorem and the proved isometric identification.
This gives self-adjoint lifts. Real and imaginary parts then give a lift of
every element of the generated algebra with a quantitative norm bound.

The argument applies to arbitrary nondegenerate representations of an
arbitrary nonunital C*-algebra. No irreducibility, separability, or atomic
representation premise is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section

open Set
open scoped CStarAlgebra ComplexStarModule
open MathlibAnnex.RepresentedBidual

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem transport_ball_image {X Y Z : Type*}
    [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y] [Module ℂ X] [Module ℂ Y]
    (e : X ≃ₗᵢ[ℂ] Y) (f : X → Z) (g : Y → Z) (h : ∀ x, g (e x) = f x) (r : ℝ) :
    g '' Metric.closedBall 0 r = f '' Metric.closedBall 0 r := by
  have hball := e.image_closedBall (0 : X) r
  rw [e.map_zero] at hball
  rw [← hball, Set.image_image]
  exact congrArg (fun k : X → Z => k '' Metric.closedBall 0 r) (funext h)

/-- The image of an envelope norm ball under the actual extended
representation is WOT compact, in the standard WOT type copy. -/
theorem isCompact_wot_envelopingRepresentationExtension_closedBall
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) (r : ℝ) :
    IsCompact ((fun T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra =>
      ContinuousLinearMapWOT.ofCLM
        (envelopingRepresentationExtension pi hnd T : H →L[ℂ] H)) ''
      Metric.closedBall 0 r) := by
  have heq : ((fun T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra =>
        ContinuousLinearMapWOT.ofCLM
          (envelopingRepresentationExtension pi hnd T : H →L[ℂ] H)) ''
        Metric.closedBall 0 r) =
      ((fun F : StrongDual ℂ (StrongDual ℂ A) =>
        ContinuousLinearMapWOT.ofCLM (extension pi F)) '' Metric.closedBall 0 r) := by
    refine transport_ball_image (X := StrongDual ℂ (StrongDual ℂ A))
      (Y := ↥(envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) (Z := H →WOT[ℂ] H)
      (bidualEnvelopingEquiv (A := A)) (fun F => ContinuousLinearMapWOT.ofCLM (extension pi F))
      (fun T => ContinuousLinearMapWOT.ofCLM (envelopingRepresentationExtension pi hnd T : H →L[ℂ] H)) ?_ r
    intro F
    exact congrArg ContinuousLinearMapWOT.ofCLM
      ((envelopingRepresentationExtension_apply_coe pi hnd (bidualEnvelopingEquiv (A := A) F)).trans
        (congrArg (extension pi) ((bidualEnvelopingEquiv (A := A)).symm_apply_apply F)))
  rw [heq]
  exact isCompact_wot_extension_closedBall pi r

/-- In particular bounded represented envelope balls are WOT closed. -/
theorem isClosed_wot_envelopingRepresentationExtension_closedBall
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) (r : ℝ) :
    IsClosed ((fun T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra =>
      ContinuousLinearMapWOT.ofCLM
        (envelopingRepresentationExtension pi hnd T : H →L[ℂ] H)) ''
      Metric.closedBall 0 r) :=
  (isCompact_wot_envelopingRepresentationExtension_closedBall pi hnd r).isClosed

/-- Every self-adjoint element of the generated von Neumann algebra has
a self-adjoint envelope preimage with the same norm budget. -/
theorem exists_selfAdjoint_envelopingRepresentationExtension_preimage_norm_le
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (T : (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra)
    (hT : IsSelfAdjoint T) :
    ∃ S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra,
      IsSelfAdjoint S ∧ envelopingRepresentationExtension pi hnd S = T ∧ ‖S‖ ≤ ‖T‖ := by
  let q := envelopingRepresentationExtension pi hnd
  let σ : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra →⋆ₐ[ℂ]
      (H →L[ℂ] H) :=
    (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra.subtype.comp q
  have hsource : Set.range pi ⊆ Set.range σ := by
    rintro _ ⟨a, rfl⟩
    exact ⟨envelopingInclusion (A := A) a,
      envelopingRepresentationExtension_inclusion pi hnd a⟩
  have hTmem : (T : H →L[ℂ] H) ∈
      Set.centralizer (Set.centralizer (Set.range σ)) := by
    have hraw := T.property
    change (T : H →L[ℂ] H) ∈
      Set.centralizer (Set.centralizer (Set.range pi.unitization)) at hraw
    rw [NonUnitalCStarRepresentation.centralizer_range_unitization] at hraw
    exact Set.centralizer_subset (Set.centralizer_subset hsource) hraw
  have hself : IsSelfAdjoint (T : H →L[ℂ] H) :=
    hT.map (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra.subtype
  have hclosure := σ.mem_wotClosure_image_closedBall_of_isSelfAdjoint
    (T : H →L[ℂ] H) hTmem hself
  have hclosed := isClosed_wot_envelopingRepresentationExtension_closedBall pi hnd ‖T‖
  change ContinuousLinearMapWOT.ofCLM (T : H →L[ℂ] H) ∈
    closure ((fun S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra =>
      ContinuousLinearMapWOT.ofCLM (q S : H →L[ℂ] H)) ''
      Metric.closedBall 0 ‖T‖) at hclosure
  rw [hclosed.closure_eq] at hclosure
  obtain ⟨S, hSnorm, hS⟩ := hclosure
  have hq : q S = T := Subtype.ext (ContinuousLinearMapWOT.ofCLM_injective hS)
  refine ⟨(realPart S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra),
    (realPart S).property, ?_, ?_⟩
  · change q (realPart S) = T
    rw [map_realPart, hq, hT.coe_realPart]
  · exact (realPart.norm_le S).trans
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hSnorm)

private theorem lift_of_selfAdjoint_lifts {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (q : X →⋆ₐ[ℂ] Y) (liftSA : ∀ y : Y, IsSelfAdjoint y →
      ∃ x : X, IsSelfAdjoint x ∧ q x = y ∧ ‖x‖ ≤ ‖y‖) (T : Y) :
    ∃ S : X, q S = T ∧ ‖S‖ ≤ 2 * ‖T‖ := by
  obtain ⟨S, _, hS, hSnorm⟩ :=
    liftSA
      (realPart T) (realPart T).property
  obtain ⟨U, _, hU, hUnorm⟩ :=
    liftSA
      (imaginaryPart T) (imaginaryPart T).property
  refine ⟨S + Complex.I • U, ?_, ?_⟩
  · rw [map_add, map_smul, hS, hU, realPart_add_I_smul_imaginaryPart]
  · calc
      ‖S + Complex.I • U‖ ≤ ‖S‖ + ‖Complex.I • U‖ := norm_add_le _ _
      _ = ‖S‖ + ‖U‖ := by rw [norm_smul, Complex.norm_I, one_mul]
      _ ≤ ‖realPart T‖ + ‖imaginaryPart T‖ := add_le_add hSnorm hUnorm
      _ ≤ ‖T‖ + ‖T‖ := add_le_add (realPart.norm_le T) (imaginaryPart.norm_le T)
      _ = 2 * ‖T‖ := (two_mul ‖T‖).symm

/-- An arbitrary generated operator has an actual envelope preimage.
The real-imaginary decomposition supplies an explicit factor-two norm bound. -/
theorem exists_envelopingRepresentationExtension_preimage_norm_le_two_mul
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (T : (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra) :
    ∃ S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra,
      envelopingRepresentationExtension pi hnd S = T ∧ ‖S‖ ≤ 2 * ‖T‖ := by
  exact lift_of_selfAdjoint_lifts (envelopingRepresentationExtension pi hnd)
    (exists_selfAdjoint_envelopingRepresentationExtension_preimage_norm_le pi hnd) T

/-- Every nondegenerate representation of the original algebra extends
onto the von Neumann algebra generated by that representation. -/
theorem surjective_envelopingRepresentationExtension
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    Function.Surjective (envelopingRepresentationExtension pi hnd) := by
  intro T
  have h := exists_envelopingRepresentationExtension_preimage_norm_le_two_mul pi hnd T
  exact ⟨h.choose, h.choose_spec.1⟩

/-- The onto result also holds on the literal original Banach bidual,
with its inherited norm and the existing represented extension. -/
theorem exists_extension_preimage_norm_le_two_mul_of_isNondegenerate
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (T : H →L[ℂ] H) (hT : T ∈ VonNeumannAlgebra.generated pi.unitization.range) :
    ∃ F : StrongDual ℂ (StrongDual ℂ A), extension pi F = T ∧ ‖F‖ ≤ 2 * ‖T‖ := by
  obtain ⟨S, hS, hSnorm⟩ :=
    exists_envelopingRepresentationExtension_preimage_norm_le_two_mul pi hnd ⟨T, hT⟩
  refine ⟨(bidualEnvelopingEquiv (A := A)).symm S, ?_, ?_⟩
  · exact congrArg (fun U : (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra =>
      (U : H →L[ℂ] H)) hS
  · change ‖S‖ ≤ 2 * ‖T‖ at hSnorm
    exact ((bidualEnvelopingEquiv (A := A)).symm.norm_map S).le.trans hSnorm

private theorem corner_norm_image {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (M : VonNeumannAlgebra K) (N : VonNeumannAlgebra H)
    (q : M.toStarSubalgebra →⋆ₐ[ℂ] N.toStarSubalgebra) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) (hc : ∀ x, p * x = x * p) (hunit : q p = 1)
    (hker : ∀ x, q x = 0 ↔ p * x = 0) (S : M.toStarSubalgebra) : ‖p * S‖ = ‖q S‖ := by
  let C := VonNeumannAlgebra.corner M p hp
  let r : C →⋆ₙₐ[ℂ]
      N.toStarSubalgebra :=
    q.toNonUnitalStarAlgHom.comp (NonUnitalStarSubalgebraClass.subtype (R := ℂ) C)
  have hr : Function.Injective r := by
    intro x y hxy
    apply Subtype.ext
    change q (x : M.toStarSubalgebra) = q (y : M.toStarSubalgebra) at hxy
    have hk : q ((x : M.toStarSubalgebra) - (y : M.toStarSubalgebra)) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hz := (hker
      ((x : M.toStarSubalgebra) - (y : M.toStarSubalgebra))).mp hk
    change p * ((x : M.toStarSubalgebra) - (y : M.toStarSubalgebra)) = 0 at hz
    rw [mul_sub, x.property.1, y.property.1, sub_eq_zero] at hz
    exact hz
  have hmem : p * S ∈ C := by
    constructor
    · change p * (p * S) = p * S
      rw [← mul_assoc, hp.isIdempotentElem.eq]
    · change p * S * p = p * S
      rw [mul_assoc, ← hc S,
        ← mul_assoc, hp.isIdempotentElem.eq]
  let U : C := ⟨p * S, hmem⟩
  have hq : r U = q S := by
    change q (p * S) = q S
    rw [map_mul, hunit, one_mul]
  calc
    ‖p * S‖ = ‖U‖ := rfl
    _ = ‖r U‖ := (NonUnitalStarAlgHom.norm_map r hr U).symm
    _ = ‖q S‖ := congrArg norm hq

/-- The extension is isometric on its central support corner. The corner
is the existing norm-closed nonunital star subalgebra, so Mathlib's
isometry result for injective star homomorphisms applies with the inherited norm. -/
theorem norm_envelopingRepresentationSupportProjection_mul
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    ‖envelopingRepresentationSupportProjection pi hnd * S‖ =
      ‖envelopingRepresentationExtension pi hnd S‖ := by
  exact corner_norm_image (envelopingVonNeumannAlgebra (A := A))
    (VonNeumannAlgebra.generated pi.unitization.range) (envelopingRepresentationExtension pi hnd)
    (envelopingRepresentationSupportProjection pi hnd)
    ⟨envelopingRepresentationSupportProjection_idem pi hnd, envelopingRepresentationSupportProjection_star pi hnd⟩
    (envelopingRepresentationSupportProjection_central pi hnd)
    (envelopingRepresentationExtension_supportProjection pi hnd)
    (envelopingRepresentationExtension_eq_zero_iff pi hnd) S

private theorem lift_on_support {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (q : X →⋆ₐ[ℂ] Y) (hq : Function.Surjective q) (p : X) (hp : q p = 1)
    (hn : ∀ x, ‖p * x‖ = ‖q x‖) (y : Y) : ∃ x, q x = y ∧ ‖x‖ = ‖y‖ := by
  obtain ⟨x, rfl⟩ := hq y
  exact ⟨p * x, by rw [map_mul, hp, one_mul], hn x⟩

/-- Each generated operator has an envelope preimage with exactly its
operator norm, obtained by removing the constructed central kernel. -/
theorem exists_envelopingRepresentationExtension_preimage_norm_eq
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (T : (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra) :
    ∃ S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra,
      envelopingRepresentationExtension pi hnd S = T ∧ ‖S‖ = ‖T‖ := by
  exact lift_on_support (envelopingRepresentationExtension pi hnd)
    (surjective_envelopingRepresentationExtension pi hnd) (envelopingRepresentationSupportProjection pi hnd)
    (envelopingRepresentationExtension_supportProjection pi hnd)
    (norm_envelopingRepresentationSupportProjection_mul pi hnd) T

/-- Sharp norm-controlled lifting on the literal double dual of the
original nonunital C*-algebra. -/
theorem exists_extension_preimage_norm_eq_of_isNondegenerate
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (T : H →L[ℂ] H) (hT : T ∈ VonNeumannAlgebra.generated pi.unitization.range) :
    ∃ F : StrongDual ℂ (StrongDual ℂ A), extension pi F = T ∧ ‖F‖ = ‖T‖ := by
  obtain ⟨S, hS, hSnorm⟩ :=
    exists_envelopingRepresentationExtension_preimage_norm_eq pi hnd ⟨T, hT⟩
  refine ⟨(bidualEnvelopingEquiv (A := A)).symm S, ?_, ?_⟩
  · exact congrArg (fun U : (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra =>
      (U : H →L[ℂ] H)) hS
  · change ‖S‖ = ‖T‖ at hSnorm
    exact ((bidualEnvelopingEquiv (A := A)).symm.norm_map S).trans hSnorm

/-- The exact range, as opposed to merely its WOT closure. -/
theorem range_extension_of_isNondegenerate
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    Set.range (extension pi) =
      (VonNeumannAlgebra.generated pi.unitization.range : Set (H →L[ℂ] H)) := by
  ext T
  constructor
  · rintro ⟨F, rfl⟩
    exact extension_mem_vonNeumannAlgebra pi
      (VonNeumannAlgebra.generated pi.unitization.range)
      (fun a => VonNeumannAlgebra.subset_generated pi.unitization.range
        ⟨Unitization.inr a, NonUnitalCStarRepresentation.unitization_inr pi a⟩) F
  · intro hT
    obtain ⟨F, hF, _⟩ := exists_extension_preimage_norm_eq_of_isNondegenerate pi hnd T hT
    exact ⟨F, hF⟩

private theorem closedBall_image_of_norm_lifts {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (q : X →⋆ₐ[ℂ] Y) (liftNorm : ∀ y, ∃ x, q x = y ∧ ‖x‖ = ‖y‖) (r : ℝ) :
    q '' Metric.closedBall 0 r = Metric.closedBall 0 r := by
  ext T
  constructor
  · rintro ⟨S, hS, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hS ⊢
    exact (NonUnitalStarAlgHom.norm_apply_le q S).trans hS
  · intro hT
    obtain ⟨S, hS, hSnorm⟩ := liftNorm T
    refine ⟨S, ?_, hS⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, hSnorm] using hT

/-- The actual extension maps every closed norm ball onto the target ball,
including zero and negative radii. -/
theorem image_envelopingRepresentationExtension_closedBall
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) (r : ℝ) :
    envelopingRepresentationExtension pi hnd '' Metric.closedBall 0 r =
      Metric.closedBall 0 r := by
  exact closedBall_image_of_norm_lifts (envelopingRepresentationExtension pi hnd)
    (exists_envelopingRepresentationExtension_preimage_norm_eq pi hnd) r

end MathlibAnnex.Analysis.CStarAlgebra
