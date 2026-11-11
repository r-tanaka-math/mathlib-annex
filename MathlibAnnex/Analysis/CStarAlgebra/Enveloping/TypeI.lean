/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.CornerEquivalence
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.Bidual
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeDecomposition

/-!
# Type I images of the actual enveloping quotient

The constructed central support corner identifies the generated algebra
of any nondegenerate representation with a genuine corner of the all-state
envelope. The existing internal projection criterion passes through that
particular equivalence. Subsequent transport between two whole concrete
von Neumann algebras uses the provider's `VonNeumannAlgebra.IsTypeI.map`.
The absorption pullback in the first proof adapts the supplied
`isAbelianProjection_map_iff` proof to the existing nonunital corner;
the provider's whole-VN statement cannot take that corner as its domain.

The final results work on the literal double strong dual. In a type III
represented image, every abelian subprojection of its explicit bidual
support is zero. A nonzero representation makes that support nonzero, so
the literal bidual cannot be type I. No existence of a type III
representation is asserted here, and no factor or separability hypothesis
is imposed on these implications.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 120000
noncomputable section

open MathlibAnnex.RepresentedBidual
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance 100] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

private theorem map_abelian_corner {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra K) (N : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) (e : ↥(M.corner p hp) ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (S : M.corner p hp) (hS : M.IsAbelianProjection S) : N.IsAbelianProjection (e S) := by
  have hproj : IsStarProjection S :=
    (VonNeumannAlgebra.isStarProjection_corner_iff
      M
      p
      hp S).mpr hS.1
  refine ⟨hproj.map e, ?_⟩
  intro T U hST hTS hSU hUS
  have pull_left
      (V : N.toStarSubalgebra)
      (hV : e S * V = V) :
      (S : M.toStarSubalgebra) *
          (e.symm V : M.toStarSubalgebra) =
        (e.symm V : M.toStarSubalgebra) := by
    have heq : S * e.symm V = e.symm V := e.toEquiv.injective
      ((e.map_mul S (e.symm V)).trans ((congrArg (e S * ·) (e.apply_symm_apply V)).trans
        (hV.trans (e.apply_symm_apply V).symm)))
    exact congrArg Subtype.val heq
  have pull_right
      (V : N.toStarSubalgebra)
      (hV : V * e S = V) :
      (e.symm V : M.toStarSubalgebra) *
          (S : M.toStarSubalgebra) =
        (e.symm V : M.toStarSubalgebra) := by
    have heq : e.symm V * S = e.symm V := e.toEquiv.injective
      ((e.map_mul (e.symm V) S).trans ((congrArg (· * e S) (e.apply_symm_apply V)).trans
        (hV.trans (e.apply_symm_apply V).symm)))
    exact congrArg Subtype.val heq
  have hcomm : e.symm T * e.symm U = e.symm U * e.symm T := by
    apply Subtype.ext
    exact hS.mul_comm (pull_left T hST) (pull_right T hTS)
      (pull_left U hSU) (pull_right U hUS)
  simpa only [map_mul, e.apply_symm_apply] using congrArg e hcomm

/-- Abelian projections in the actual support corner remain abelian in
the represented image. The domain is the supplied nonunital corner, so
this concrete bridge does not invoke a whole-VN equivalence on that type. -/
theorem isAbelianProjection_envelopingRepresentationCornerEquiv
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (S : envelopingRepresentationCorner pi hnd)
    (hS : (envelopingVonNeumannAlgebra (A := A)).IsAbelianProjection S) :
    (VonNeumannAlgebra.generated pi.unitization.range).IsAbelianProjection
      (envelopingRepresentationCornerEquiv pi hnd S) := by
  exact map_abelian_corner (envelopingVonNeumannAlgebra (A := A))
    (VonNeumannAlgebra.generated pi.unitization.range) (envelopingRepresentationSupportProjection pi hnd)
    (isStarProjection_envelopingRepresentationSupportProjection pi hnd) (envelopingRepresentationCornerEquiv pi hnd) S hS

private theorem typeI_of_central_corner_equiv {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra K) (N : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) (e : ↥(M.corner p hp) ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (hc : ∀ x, p * x = x * p) (hM : M.IsTypeI) : N.IsTypeI := by
  have hlocal := hM.isTypeIProjection
    hp
  intro T hT hT0
  let S := e.symm T
  have hS : IsStarProjection (S : M.toStarSubalgebra) :=
    (VonNeumannAlgebra.isStarProjection_corner_iff M p
      hp S).mp
      (hT.map e.symm)
  have hS0 : (S : M.toStarSubalgebra) ≠ 0 := by
    intro hzero
    apply hT0
    have hz : S = 0 := Subtype.ext hzero
    simpa only [S, e.apply_symm_apply, map_zero] using congrArg e hz
  obtain ⟨U, hU, hU0, hUS⟩ := hlocal.2 (S : M.toStarSubalgebra) hS hS0 S.property.2
  have hUp : U * p = U := by
    calc
      U * p = (U * (S : M.toStarSubalgebra)) * p := by rw [hUS]
      _ = U * ((S : M.toStarSubalgebra) * p) := mul_assoc _ _ _
      _ = U := by rw [S.property.2, hUS]
  have hpU : p * U = U :=
    (hc U).trans hUp
  let V : M.corner p hp := ⟨U, hpU, hUp⟩
  refine ⟨e V, map_abelian_corner M N p hp e V hU,
    ?_, ?_⟩
  · intro hz
    apply hU0
    exact congrArg Subtype.val (e.injective (hz.trans (map_zero e).symm))
  · have hVS : V * S = V := Subtype.ext hUS
    simpa only [map_mul, S, e.apply_symm_apply] using congrArg e hVS

/-- Type I of the literal enveloping bidual passes through the actual
normal quotient of any nondegenerate representation. Its source corner
is the existing support corner, and its target is the generated VN. -/
theorem IsTypeIBidual.isTypeI_generated
    (hA : IsTypeIBidual A)
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    (VonNeumannAlgebra.generated pi.unitization.range).IsTypeI := by
  exact typeI_of_central_corner_equiv (envelopingVonNeumannAlgebra (A := A))
    (VonNeumannAlgebra.generated pi.unitization.range) (envelopingRepresentationSupportProjection pi hnd)
    (isStarProjection_envelopingRepresentationSupportProjection pi hnd) (envelopingRepresentationCornerEquiv pi hnd)
    (envelopingRepresentationSupportProjection_central pi hnd) hA

/-- Once the target is a whole concrete von Neumann algebra, its type I
transport is exactly the supplied `VonNeumannAlgebra.IsTypeI.map`. -/
theorem IsTypeIBidual.isTypeI_of_generatedEquiv
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (hA : IsTypeIBidual A)
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (N : VonNeumannAlgebra K)
    (e : (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra ≃⋆ₐ[ℂ]
      N.toStarSubalgebra) : N.IsTypeI :=
  (hA.isTypeI_generated pi hnd).map e

/-- A nonzero representation has a nonzero constructed support on the
literal double dual. No nontriviality instance is added to the statement. -/
theorem bidualRepresentationSupportProjection_ne_zero
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (hnz : pi.IsNonzero) : bidualRepresentationSupportProjection pi hnd ≠ 0 := by
  intro hz
  have h01 : (0 : H →L[ℂ] H) = 1 := by
    simpa only [hz, map_zero] using extension_bidualRepresentationSupportProjection pi hnd
  obtain ⟨a, ha⟩ := hnz
  apply ha
  calc
    pi a = 1 * pi a := (one_mul _).symm
    _ = 0 := by rw [← h01, zero_mul]

private theorem abelian_corner_eq_zero {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra K) (N : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) (e : ↥(M.corner p hp) ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (hIII : N.IsTypeIII) (a : M.toStarSubalgebra) (ha : M.IsAbelianProjection a)
    (hpa : p * a = a) (hap : a * p = a) : a = 0 := by
  let S : M.corner p hp := ⟨a, hpa, hap⟩
  have hf := (map_abelian_corner M N p hp e S ha).isFiniteProjection
  have hz : e S = 0 := hIII.2 (e S) hf (mul_one _)
  exact congrArg Subtype.val (e.injective (hz.trans (map_zero e).symm))

/-- Every abelian subprojection of the explicit literal-bidual support
vanishes when the actual generated image is type III. The Arens product,
involution and carrier are the original ones. -/
theorem eq_zero_of_bidualProjection_mul_support_of_isTypeIII
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (hIII : (VonNeumannAlgebra.generated pi.unitization.range).IsTypeIII)
    (Q : StrongDual ℂ (StrongDual ℂ A))
    (hQQ : arensProduct Q Q = Q) (hQstar : bidualStar Q = Q)
    (hQP : arensProduct Q (bidualRepresentationSupportProjection pi hnd) = Q)
    (hcomm : ∀ X Y : StrongDual ℂ (StrongDual ℂ A),
      arensProduct Q X = X → arensProduct X Q = X →
      arensProduct Q Y = Y → arensProduct Y Q = Y →
      arensProduct X Y = arensProduct Y X) : Q = 0 := by
  let E := bidualEnvelopingEquiv (A := A)
  let p := envelopingRepresentationSupportProjection pi hnd
  have habelian : (envelopingVonNeumannAlgebra (A := A)).IsAbelianProjection (E Q) :=
    (isAbelianProjection_bidualEnvelopingEquiv_iff (A := A) Q).mpr ⟨hQQ, hQstar, hcomm⟩
  have hp : E (bidualRepresentationSupportProjection pi hnd) = p := E.apply_symm_apply p
  have hQp : E Q * p = E Q :=
    (congrArg (E Q * ·) hp).symm.trans
      ((bidualEnvelopingEquiv_arensProduct (A := A) Q (bidualRepresentationSupportProjection pi hnd)).symm.trans
        (congrArg E hQP))
  have hpQ := (envelopingRepresentationSupportProjection_central pi hnd (E Q)).trans hQp
  have hz := abelian_corner_eq_zero (envelopingVonNeumannAlgebra (A := A))
    (VonNeumannAlgebra.generated pi.unitization.range) (envelopingRepresentationSupportProjection pi hnd)
    (isStarProjection_envelopingRepresentationSupportProjection pi hnd) (envelopingRepresentationCornerEquiv pi hnd) hIII (E Q) habelian hpQ hQp
  exact E.injective (hz.trans E.map_zero.symm)

/-- A genuine nonzero nondegenerate type III represented image obstructs
type I of the literal bidual. The representation's existence remains a
separate construction; it is not built into the type I predicate. -/
theorem not_isTypeIBidual_of_isTypeIII_generated
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (hnz : pi.IsNonzero)
    (hIII : (VonNeumannAlgebra.generated pi.unitization.range).IsTypeIII) :
    ¬ IsTypeIBidual A := by
  intro hA
  obtain ⟨Q, hQQ, hQstar, hQ0, hQP, hcomm⟩ :=
    (isTypeIBidual_iff_arensProduct (A := A)).mp hA
      (bidualRepresentationSupportProjection pi hnd)
      (bidualRepresentationSupportProjection_idem pi hnd)
      (bidualRepresentationSupportProjection_star pi hnd)
      (bidualRepresentationSupportProjection_ne_zero pi hnd hnz)
  exact hQ0 (eq_zero_of_bidualProjection_mul_support_of_isTypeIII
    pi hnd hIII Q hQQ hQstar hQP hcomm)

end MathlibAnnex.Analysis.CStarAlgebra
