/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.Surjectivity
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.CentralSplit

/-!
# The actual support-corner equivalence of a representation

The restriction of the proved surjective enveloping extension to its
constructed central support is bijective. Mathlib's `StarAlgEquiv.ofBijective`
bundles that restriction. The domain is precisely the existing nonunital
corner, with its inherited norm and operations. Its distinguished identity
is the support projection, and its image is the identity of the generated
von Neumann algebra.

No separate corner carrier or global unital instance is introduced. The
normality of the full quotient is supplied by `Enveloping.Normality`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 120000
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The previously constructed central support satisfies the existing
projection predicate. -/
theorem isStarProjection_envelopingRepresentationSupportProjection
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    IsStarProjection (envelopingRepresentationSupportProjection pi hnd) :=
  ⟨envelopingRepresentationSupportProjection_idem pi hnd,
    envelopingRepresentationSupportProjection_star pi hnd⟩

/-- The existing corner at the support of the actual extension. This is an
abbreviation for the supplied nonunital star subalgebra, with no new norm. -/
abbrev envelopingRepresentationCorner
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    NonUnitalStarSubalgebra ℂ (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
  VonNeumannAlgebra.corner (envelopingVonNeumannAlgebra (A := A))
    (envelopingRepresentationSupportProjection pi hnd)
    (isStarProjection_envelopingRepresentationSupportProjection pi hnd)

private abbrev RestrictedHomType {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (C : NonUnitalStarSubalgebra ℂ X) := ↥C →⋆ₙₐ[ℂ] Y

private abbrev RestrictedEquivType {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (C : NonUnitalStarSubalgebra ℂ X) := ↥C ≃⋆ₐ[ℂ] Y

private def restrictHom {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (q : X →⋆ₐ[ℂ] Y) (C : NonUnitalStarSubalgebra ℂ X) : RestrictedHomType (Y := Y) C :=
  q.toNonUnitalStarAlgHom.comp (NonUnitalStarSubalgebraClass.subtype (R := ℂ) C)

private abbrev vnCarrierAlgebra {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (M : VonNeumannAlgebra K) : CStarAlgebra M.toStarSubalgebra := inferInstance

private def equivOfRestrictedHom {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (C : NonUnitalStarSubalgebra ℂ X) (f : RestrictedHomType (Y := Y) C)
    (hf : Function.Bijective f) : RestrictedEquivType (Y := Y) C :=
  StarAlgEquiv.ofBijective f hf

/-- The actual extension, restricted to the support corner by the existing
subtype star homomorphism. -/
def envelopingRepresentationCornerHom
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    RestrictedHomType (X := ↥(envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
      (Y := ↥(VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra)
      (envelopingRepresentationCorner pi hnd) :=
  restrictHom (envelopingRepresentationExtension pi hnd) (envelopingRepresentationCorner pi hnd)

@[simp]
theorem envelopingRepresentationCornerHom_apply
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (S : envelopingRepresentationCorner pi hnd) :
    envelopingRepresentationCornerHom pi hnd S =
      envelopingRepresentationExtension pi hnd S := rfl

private theorem eq_of_support_norm {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (q : X →⋆ₐ[ℂ] Y) (p : X) (hn : ∀ x, ‖p * x‖ = ‖q x‖) (x y : X)
    (hx : p * x = x) (hy : p * y = y) (hxy : q x = q y) : x = y := by
  have h := hn (x - y)
  rw [mul_sub, hx, hy, map_sub, hxy, sub_self, norm_zero, norm_eq_zero, sub_eq_zero] at h
  exact h

/-- The previously proved support-corner norm formula makes the
restriction injective, without repeating its kernel argument. -/
theorem injective_envelopingRepresentationCornerHom
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    Function.Injective (envelopingRepresentationCornerHom pi hnd) := by
  intro S T hST
  exact Subtype.ext (eq_of_support_norm (envelopingRepresentationExtension pi hnd)
    (envelopingRepresentationSupportProjection pi hnd) (norm_envelopingRepresentationSupportProjection_mul pi hnd)
    S.val T.val S.property.1 T.property.1 hST)

/-- An existing onto lift, followed by the existing central-corner map,
is an actual preimage for the restricted homomorphism. -/
theorem surjective_envelopingRepresentationCornerHom
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    Function.Surjective (envelopingRepresentationCornerHom pi hnd) := by
  intro T
  have h := surjective_envelopingRepresentationExtension pi hnd T
  let S := h.choose
  have hS : envelopingRepresentationExtension pi hnd S = T := h.choose_spec
  refine ⟨VonNeumannAlgebra.centralCornerHom
    (envelopingVonNeumannAlgebra (A := A))
    (envelopingRepresentationSupportProjection pi hnd)
    (isStarProjection_envelopingRepresentationSupportProjection pi hnd)
    (fun U => (envelopingRepresentationSupportProjection_central pi hnd U).symm) S,
    ?_⟩
  change envelopingRepresentationExtension pi hnd
    (envelopingRepresentationSupportProjection pi hnd * S) = T
  rw [map_mul, envelopingRepresentationExtension_supportProjection, one_mul, hS]

/-- The support corner and the generated von Neumann algebra are equivalent
by the restriction of the actual normal enveloping quotient. -/
def envelopingRepresentationCornerEquiv
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    RestrictedEquivType (X := ↥(envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
      (Y := ↥(VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra)
      (envelopingRepresentationCorner pi hnd) :=
  @equivOfRestrictedHom ↥(envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra
    ↥(VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra
    (vnCarrierAlgebra (K := UniversalHilbertSpace A) (envelopingVonNeumannAlgebra (A := A)))
    (vnCarrierAlgebra (K := H) (VonNeumannAlgebra.generated pi.unitization.range))
    (envelopingRepresentationCorner pi hnd) (envelopingRepresentationCornerHom pi hnd)
    ⟨injective_envelopingRepresentationCornerHom pi hnd,
      surjective_envelopingRepresentationCornerHom pi hnd⟩

@[simp]
theorem envelopingRepresentationCornerEquiv_apply
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (S : envelopingRepresentationCorner pi hnd) :
    envelopingRepresentationCornerEquiv pi hnd S =
      envelopingRepresentationExtension pi hnd S := rfl

/-- The genuine identity of the support corner is sent to the generated
algebra's identity, even if either algebra is zero. -/
@[simp]
theorem envelopingRepresentationCornerEquiv_cornerUnit
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    envelopingRepresentationCornerEquiv pi hnd
      (VonNeumannAlgebra.cornerUnit (envelopingVonNeumannAlgebra (A := A))
        (envelopingRepresentationSupportProjection pi hnd)
        (isStarProjection_envelopingRepresentationSupportProjection pi hnd)) = 1 :=
  envelopingRepresentationExtension_supportProjection pi hnd

private theorem inverse_value_of_apply {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (C : NonUnitalStarSubalgebra ℂ X) (e : RestrictedEquivType (Y := Y) C) (x : C) (y : Y)
    (h : e x = y) : e.invFun y = x :=
  e.toEquiv.injective ((e.toEquiv.apply_symm_apply y).trans h.symm)

private theorem restricted_isometry {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (C : NonUnitalStarSubalgebra ℂ X) (hC : IsClosed (C : Set X))
    (e : RestrictedEquivType (Y := Y) C) : Isometry e := by
  letI : IsClosed (C : Set X) := hC
  exact NonUnitalStarAlgHom.isometry e.toNonUnitalStarAlgHom e.toEquiv.injective

/-- The inverse sends the target unit to the support projection inside its
own corner, rather than to the ambient envelope unit. -/
@[simp]
theorem envelopingRepresentationCornerEquiv_symm_one
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    (envelopingRepresentationCornerEquiv pi hnd).invFun 1 =
      VonNeumannAlgebra.cornerUnit (envelopingVonNeumannAlgebra (A := A))
        (envelopingRepresentationSupportProjection pi hnd)
        (isStarProjection_envelopingRepresentationSupportProjection pi hnd) := by
  exact inverse_value_of_apply (X := ↥(envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (Y := ↥(VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra)
    (envelopingRepresentationCorner pi hnd) (envelopingRepresentationCornerEquiv pi hnd) _ 1
    (envelopingRepresentationCornerEquiv_cornerUnit pi hnd)

/-- The inverse at any represented value is multiplication by the already
constructed central support, as an element of the existing corner. -/
theorem envelopingRepresentationCornerEquiv_symm_extension
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    (envelopingRepresentationCornerEquiv pi hnd).invFun
        (envelopingRepresentationExtension pi hnd S) =
      VonNeumannAlgebra.centralCornerHom (envelopingVonNeumannAlgebra (A := A))
        (envelopingRepresentationSupportProjection pi hnd)
        (isStarProjection_envelopingRepresentationSupportProjection pi hnd)
        (fun U => (envelopingRepresentationSupportProjection_central pi hnd U).symm) S := by
  apply inverse_value_of_apply (X := ↥(envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (Y := ↥(VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra)
    (envelopingRepresentationCorner pi hnd) (envelopingRepresentationCornerEquiv pi hnd)
  let q := envelopingRepresentationExtension pi hnd
  let p := envelopingRepresentationSupportProjection pi hnd
  change q (p * S) = q S
  exact (q.map_mul p S).trans
    ((congrArg (· * q S) (envelopingRepresentationExtension_supportProjection pi hnd)).trans (one_mul _))

/-- The actual corner equivalence preserves the inherited C-star norm. -/
theorem isometry_envelopingRepresentationCornerEquiv
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    Isometry (envelopingRepresentationCornerEquiv pi hnd) := by
  exact @restricted_isometry ↥(envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra
    ↥(VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra
    (vnCarrierAlgebra (envelopingVonNeumannAlgebra (A := A)))
    (vnCarrierAlgebra (VonNeumannAlgebra.generated pi.unitization.range))
    (envelopingRepresentationCorner pi hnd)
    (VonNeumannAlgebra.isClosed_corner (envelopingVonNeumannAlgebra (A := A))
      (envelopingRepresentationSupportProjection pi hnd) (isStarProjection_envelopingRepresentationSupportProjection pi hnd))
    (envelopingRepresentationCornerEquiv pi hnd)

end MathlibAnnex.Analysis.CStarAlgebra
