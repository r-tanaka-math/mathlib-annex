/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.CornerEquivalence
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.NormalCompression
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.CentralSupport
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# The concrete central corner of an intertwining compression

The lift below is constructed from the already proved onto maps of the
all-state envelope. First take the inverse of the actual support-corner
equivalence for the small representation, then apply the other represented
envelope quotient. The existing coefficient intertwining theorem proves
that this lift is inverse to the actual isometric compression.

Its identity is a central projection in the large generated algebra. The
projection is identified with the central support of the range projection
in the commutant. Uniformly bounded strong convergence is transported by
the closed span of this commutant orbit. No representation multiplicity,
separability, or normality of an auxiliary expectation is assumed.

The algebraic section and its support are reused from
`Enveloping.CornerEquivalence`; no second bidual or kernel-support
construction is introduced. The closed convergence-locus argument adapts
the existing `Enveloping.ApproximateUnit` proof to the zero limit.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped CStarAlgebra InnerProduct

namespace VonNeumannAlgebra

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A closed subspace containing every algebraic central-support orbit
contains the range of the existing central support. This exposes a range
consequence of its actual closed-span construction, without another support. -/
theorem centralSupport_apply_mem_of_forall_mul_apply_mem
    (L : VonNeumannAlgebra K) (p : L.toStarSubalgebra)
    (V : Submodule ℂ K) (hV : IsClosed (V : Set K))
    (horbit : ∀ (a : L.toStarSubalgebra) (x : K),
      (a : K →L[ℂ] K) ((p : K →L[ℂ] K) x) ∈ V) (x : K) :
    (centralSupport L p : K →L[ℂ] K) x ∈ V := by
  let S : Submodule ℂ K :=
    ⨆ p' : ({p} : Set L.toStarSubalgebra), ⨆ a : L.toStarSubalgebra,
      ((a : K →L[ℂ] K) * (p'.1 : K →L[ℂ] K)).range
  have hS : S ≤ V := by
    refine iSup_le fun p' => iSup_le fun a => ?_
    rintro y ⟨z, rfl⟩
    have hp' : p'.1 = p := Set.mem_singleton_iff.mp p'.property
    change (a : K →L[ℂ] K) ((p'.1 : K →L[ℂ] K) z) ∈ V
    rw [hp']
    exact horbit a z
  have hclosure : S.topologicalClosure ≤ V := S.topologicalClosure_minimal hS hV
  apply hclosure
  change S.topologicalClosure.starProjection x ∈ S.topologicalClosure
  exact Submodule.coe_mem (S.topologicalClosure.orthogonalProjectionOnto x)

end VonNeumannAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.Representation

universe u v w t

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (rho : NonUnitalCStarRepresentation A K) (hrho : rho.IsNondegenerate)
variable (sigma : NonUnitalCStarRepresentation A H) (hsigma : sigma.IsNondegenerate)

private def liftFromCorner {X Y Z : Type*} [CStarAlgebra X] [CStarAlgebra Y] [CStarAlgebra Z]
    (C : NonUnitalStarSubalgebra ℂ X) (e : ↥C ≃⋆ₐ[ℂ] Y) (q : X →⋆ₐ[ℂ] Z) : Y →⋆ₙₐ[ℂ] Z :=
  q.toNonUnitalStarAlgHom.comp ((NonUnitalStarSubalgebraClass.subtype (R := ℂ) C).comp
    e.symm.toNonUnitalStarAlgHom)

private abbrev algebraOnCarrier {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (M : VonNeumannAlgebra F) : CStarAlgebra M.toStarSubalgebra := inferInstance

/-- The actual section into the other generated algebra. Its codomain
identity need not be the ambient identity, so it is bundled nonunitally. -/
def compressionLift :
    (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra →⋆ₙₐ[ℂ]
      (VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra :=
  @liftFromCorner ↥(envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra
    ↥(VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra
    ↥(VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra
    (algebraOnCarrier (F := UniversalHilbertSpace A) (envelopingVonNeumannAlgebra (A := A)))
    (algebraOnCarrier (F := H) (VonNeumannAlgebra.generated sigma.unitization.range))
    (algebraOnCarrier (F := K) (VonNeumannAlgebra.generated rho.unitization.range))
    (envelopingRepresentationCorner sigma hsigma) (envelopingRepresentationCornerEquiv sigma hsigma)
    (envelopingRepresentationExtension rho hrho)

@[simp]
theorem compressionLift_apply
    (a : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra) :
    compressionLift rho hrho sigma hsigma a =
      envelopingRepresentationExtension rho hrho
        ((envelopingRepresentationCornerEquiv sigma hsigma).invFun a :
          (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) := rfl

/-- The section's support in the concrete large representation. -/
def compressionSupport :
    (VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra :=
  envelopingRepresentationExtension rho hrho
    (envelopingRepresentationSupportProjection sigma hsigma)

/-- Removing the same central kernel is independent of the original
envelope preimage. This is the existing corner inverse formula transported
through the second actual quotient. -/
theorem compressionLift_envelopingRepresentationExtension
    (S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    compressionLift rho hrho sigma hsigma
        (envelopingRepresentationExtension sigma hsigma S) =
      compressionSupport rho hrho sigma hsigma *
        envelopingRepresentationExtension rho hrho S := by
  exact (congrArg (fun a : envelopingRepresentationCorner sigma hsigma ↦
      envelopingRepresentationExtension rho hrho a.val)
    (envelopingRepresentationCornerEquiv_symm_extension sigma hsigma S)).trans
      ((envelopingRepresentationExtension rho hrho).map_mul _ S)

@[simp]
theorem compressionLift_one :
    compressionLift rho hrho sigma hsigma 1 =
      compressionSupport rho hrho sigma hsigma := by
  let q := envelopingRepresentationExtension sigma hsigma
  let r := envelopingRepresentationExtension rho hrho
  let f := compressionLift rho hrho sigma hsigma
  let P := compressionSupport rho hrho sigma hsigma
  have h : f (q 1) = P * r 1 := compressionLift_envelopingRepresentationExtension rho hrho sigma hsigma 1
  exact ((congrArg f q.map_one).symm.trans h).trans
    ((congrArg (fun x => P * x) r.map_one).trans (mul_one P))

theorem isStarProjection_compressionSupport :
    IsStarProjection (compressionSupport rho hrho sigma hsigma) :=
  (isStarProjection_envelopingRepresentationSupportProjection sigma hsigma).map
    (envelopingRepresentationExtension rho hrho)

/-- The existing quotient is onto, so centrality in the envelope gives
centrality in the entire concrete generated algebra. -/
theorem compressionSupport_commute
    (T : (VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra) :
    compressionSupport rho hrho sigma hsigma * T =
      T * compressionSupport rho hrho sigma hsigma := by
  obtain ⟨S, rfl⟩ := surjective_envelopingRepresentationExtension rho hrho T
  change envelopingRepresentationExtension rho hrho
      (envelopingRepresentationSupportProjection sigma hsigma) *
      envelopingRepresentationExtension rho hrho S = _
  let q := envelopingRepresentationExtension rho hrho
  let p := envelopingRepresentationSupportProjection sigma hsigma
  exact ((q.map_mul p S).symm.trans (congrArg q
    (envelopingRepresentationSupportProjection_central sigma hsigma S))).trans (q.map_mul S p)

@[simp]
theorem compressionSupport_mul_compressionLift
    (a : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra) :
    compressionSupport rho hrho sigma hsigma * compressionLift rho hrho sigma hsigma a =
      compressionLift rho hrho sigma hsigma a := by
  rw [← compressionLift_one, ← map_mul, one_mul]

@[simp]
theorem compressionLift_mul_compressionSupport
    (a : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra) :
    compressionLift rho hrho sigma hsigma a * compressionSupport rho hrho sigma hsigma =
      compressionLift rho hrho sigma hsigma a := by
  rw [← compressionLift_one, ← map_mul, mul_one]

variable (U : H →ₗᵢ[ℂ] K)
variable (hU : ∀ a : A, (rho a).comp U.toContinuousLinearMap =
  U.toContinuousLinearMap.comp (sigma a))

include hrho hsigma U hU

/-- Source intertwiners extend to the exact onto envelope quotients. -/
theorem envelopingRepresentationExtension_intertwines
    (S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    (envelopingRepresentationExtension rho hrho S : K →L[ℂ] K).comp
        U.toContinuousLinearMap =
      U.toContinuousLinearMap.comp
        (envelopingRepresentationExtension sigma hsigma S : H →L[ℂ] H) :=
  MathlibAnnex.RepresentedBidual.intertwines_extension sigma rho
    U.toContinuousLinearMap hU ((bidualEnvelopingEquiv (A := A)).symm S)

theorem adjoint_envelopingRepresentationExtension_intertwines
    (S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    U.toContinuousLinearMap.adjoint.comp
        (envelopingRepresentationExtension rho hrho S : K →L[ℂ] K) =
      (envelopingRepresentationExtension sigma hsigma S : H →L[ℂ] H).comp
        U.toContinuousLinearMap.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint
    (envelopingRepresentationExtension_intertwines rho hrho sigma hsigma U hU (star S))
  simpa only [map_star, StarMemClass.coe_star, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h

/-- The constructed lift intertwines every element of the small generated
algebra, not merely the original test algebra. -/
theorem compressionLift_intertwines
    (a : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra) :
    (compressionLift rho hrho sigma hsigma a : K →L[ℂ] K).comp
        U.toContinuousLinearMap =
      U.toContinuousLinearMap.comp (a : H →L[ℂ] H) := by
  let S := (envelopingRepresentationCornerEquiv sigma hsigma).invFun a
  have hS : envelopingRepresentationExtension sigma hsigma
      (S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) = a :=
    (envelopingRepresentationCornerEquiv sigma hsigma).right_inv a
  have h := envelopingRepresentationExtension_intertwines rho hrho sigma hsigma U hU
    (S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
  exact h.trans (congrArg (fun b : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra ↦
    U.toContinuousLinearMap.comp (b : H →L[ℂ] H)) hS)

/-- The adjoint equation gives the other half of full bimodularity. -/
theorem adjoint_compressionLift_intertwines
    (a : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra) :
    U.toContinuousLinearMap.adjoint.comp
        (compressionLift rho hrho sigma hsigma a : K →L[ℂ] K) =
      (a : H →L[ℂ] H).comp U.toContinuousLinearMap.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint
    (compressionLift_intertwines rho hrho sigma hsigma U hU (star a))
  have hs : (compressionLift rho hrho sigma hsigma (star a) : K →L[ℂ] K) =
      star (compressionLift rho hrho sigma hsigma a : K →L[ℂ] K) :=
    congrArg (fun T : (VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra =>
      (T : K →L[ℂ] K)) (map_star (compressionLift rho hrho sigma hsigma) a)
  simpa only [ContinuousLinearMap.adjoint_comp, hs, StarMemClass.coe_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h

/-- The support acts identically on the original isometry's range. -/
theorem compressionSupport_comp_isometry :
    (compressionSupport rho hrho sigma hsigma : K →L[ℂ] K).comp
      U.toContinuousLinearMap = U.toContinuousLinearMap := by
  simpa only [compressionLift_one, OneMemClass.coe_one,
    ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id] using
    compressionLift_intertwines rho hrho sigma hsigma U hU 1

/-- Compressing a lifted element recovers that exact element. -/
theorem compression_compressionLift
    (a : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra) :
    U.toContinuousLinearMap.adjoint.comp
      ((compressionLift rho hrho sigma hsigma a : K →L[ℂ] K).comp
        U.toContinuousLinearMap) = (a : H →L[ℂ] H) := by
  rw [compressionLift_intertwines rho hrho sigma hsigma U hU,
    ← ContinuousLinearMap.comp_assoc, U.adjoint_comp_self, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp]

theorem injective_compressionLift :
    Function.Injective (compressionLift rho hrho sigma hsigma) := by
  intro a b hab
  apply Subtype.ext
  rw [← compression_compressionLift rho hrho sigma hsigma U hU a,
    ← compression_compressionLift rho hrho sigma hsigma U hU b, hab]

/-- Its norm is the original operator norm, with no renormed corner. -/
theorem norm_compressionLift
    (a : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra) :
    ‖compressionLift rho hrho sigma hsigma a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (compressionLift rho hrho sigma hsigma)
    (injective_compressionLift rho hrho sigma hsigma U hU) a

theorem isometry_compressionLift :
    Isometry (compressionLift rho hrho sigma hsigma) :=
  NonUnitalStarAlgHom.isometry (compressionLift rho hrho sigma hsigma)
    (injective_compressionLift rho hrho sigma hsigma U hU)

/-- Both outer factors range over the whole small generated algebra; the
middle factor can be any bounded operator on the large Hilbert space. -/
theorem compressionLift_mul_mul
    (a b : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra)
    (T : K →L[ℂ] K) :
    U.toContinuousLinearMap.adjoint.comp
        (((compressionLift rho hrho sigma hsigma a : K →L[ℂ] K) * T *
          (compressionLift rho hrho sigma hsigma b : K →L[ℂ] K)).comp
            U.toContinuousLinearMap) =
      (a : H →L[ℂ] H) *
        (U.toContinuousLinearMap.adjoint.comp (T.comp U.toContinuousLinearMap)) *
        (b : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro x
  have hl := congrArg (fun f : K →L[ℂ] H =>
      f (T ((compressionLift rho hrho sigma hsigma b : K →L[ℂ] K) (U x))))
    (adjoint_compressionLift_intertwines rho hrho sigma hsigma U hU a)
  have hr := congrArg (fun f : H →L[ℂ] K => f x)
    (compressionLift_intertwines rho hrho sigma hsigma U hU b)
  change U.toContinuousLinearMap.adjoint
      ((compressionLift rho hrho sigma hsigma a : K →L[ℂ] K)
        (T ((compressionLift rho hrho sigma hsigma b : K →L[ℂ] K) (U x)))) = _
  rw [show U.toContinuousLinearMap.adjoint
      ((compressionLift rho hrho sigma hsigma a : K →L[ℂ] K)
        (T ((compressionLift rho hrho sigma hsigma b : K →L[ℂ] K) (U x)))) =
      (a : H →L[ℂ] H) (U.toContinuousLinearMap.adjoint
        (T ((compressionLift rho hrho sigma hsigma b : K →L[ℂ] K) (U x)))) from hl]
  rw [show (compressionLift rho hrho sigma hsigma b : K →L[ℂ] K) (U x) =
    U ((b : H →L[ℂ] H) x) from hr]
  rfl

/-- Compression on the full represented envelope quotient is the other
quotient. This supplies its actual surjectivity onto the small algebra. -/
theorem compression_envelopingRepresentationExtension
    (S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    U.toContinuousLinearMap.adjoint.comp
        ((envelopingRepresentationExtension rho hrho S : K →L[ℂ] K).comp
          U.toContinuousLinearMap) =
      (envelopingRepresentationExtension sigma hsigma S : H →L[ℂ] H) := by
  let a : H →L[ℂ] H := envelopingRepresentationExtension sigma hsigma S
  exact (congrArg (fun f : H →L[ℂ] K => U.toContinuousLinearMap.adjoint.comp f)
    (envelopingRepresentationExtension_intertwines rho hrho sigma hsigma U hU S)).trans
    ((ContinuousLinearMap.comp_assoc _ _ a).symm.trans
      (congrArg (fun f : H →L[ℂ] H => f.comp a) U.adjoint_comp_self))

/-- The kernel of the actual compression is precisely the complement of
the constructed central support in the large generated algebra. -/
theorem compression_eq_zero_iff_compressionSupport_mul_eq_zero
    (T : (VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra) :
    U.toContinuousLinearMap.adjoint.comp
        ((T : K →L[ℂ] K).comp U.toContinuousLinearMap) = 0 ↔
      compressionSupport rho hrho sigma hsigma * T = 0 := by
  obtain ⟨S, rfl⟩ := surjective_envelopingRepresentationExtension rho hrho T
  have hc := compression_envelopingRepresentationExtension rho hrho sigma hsigma U hU S
  have hl := compressionLift_envelopingRepresentationExtension rho hrho sigma hsigma S
  let f := compressionLift rho hrho sigma hsigma
  constructor
  · intro h
    have hs : envelopingRepresentationExtension sigma hsigma S = 0 := Subtype.ext (hc.symm.trans h)
    exact hl.symm.trans ((congrArg f hs).trans (map_zero f))
  · intro h
    have hs : compressionLift rho hrho sigma hsigma
        (envelopingRepresentationExtension sigma hsigma S) = 0 := hl.trans h
    have hz : envelopingRepresentationExtension sigma hsigma S = 0 :=
      (injective_compressionLift rho hrho sigma hsigma U hU)
        (hs.trans (map_zero (compressionLift rho hrho sigma hsigma)).symm)
    exact hc.trans (congrArg (fun a :
      (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra =>
        (a : H →L[ℂ] H)) hz)

/-- The range projection of the actual isometry belongs to the commutant
of the full large generated algebra. -/
theorem rangeProjection_mem_commutant :
    U.toContinuousLinearMap.comp U.toContinuousLinearMap.adjoint ∈
      (VonNeumannAlgebra.generated rho.unitization.range).commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  obtain ⟨S, hS⟩ := surjective_envelopingRepresentationExtension rho hrho ⟨T, hT⟩
  have heq : (envelopingRepresentationExtension rho hrho S : K →L[ℂ] K) = T :=
    congrArg (fun a : (VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra =>
      (a : K →L[ℂ] K)) hS
  let V := U.toContinuousLinearMap
  let a : H →L[ℂ] H := envelopingRepresentationExtension sigma hsigma S
  have hi : T.comp V = V.comp a := (congrArg (fun b : K →L[ℂ] K ↦ b.comp V) heq).symm.trans
    (envelopingRepresentationExtension_intertwines rho hrho sigma hsigma U hU S)
  have hj : V.adjoint.comp T = a.comp V.adjoint :=
    (congrArg (fun b : K →L[ℂ] K ↦ V.adjoint.comp b) heq).symm.trans
      (adjoint_envelopingRepresentationExtension_intertwines rho hrho sigma hsigma U hU S)
  change T.comp (V.comp V.adjoint) = (V.comp V.adjoint).comp T
  rw [← ContinuousLinearMap.comp_assoc T, hi, ContinuousLinearMap.comp_assoc,
    ← hj, ContinuousLinearMap.comp_assoc]

/-- The concrete support is exactly the central support of the isometry's
range projection in the commutant. Thus its range is the closed commutant
orbit of the original represented Hilbert space. -/
theorem compressionSupport_eq_centralSupport :
    (compressionSupport rho hrho sigma hsigma : K →L[ℂ] K) =
      (VonNeumannAlgebra.centralSupport
        (VonNeumannAlgebra.generated rho.unitization.range).commutant
        ⟨U.toContinuousLinearMap.comp U.toContinuousLinearMap.adjoint,
          rangeProjection_mem_commutant rho hrho sigma hsigma U hU⟩ : K →L[ℂ] K) := by
  let L := VonNeumannAlgebra.generated rho.unitization.range
  let P := compressionSupport rho hrho sigma hsigma
  let q : L.commutant.toStarSubalgebra :=
    ⟨U.toContinuousLinearMap.comp U.toContinuousLinearMap.adjoint,
      rangeProjection_mem_commutant rho hrho sigma hsigma U hU⟩
  have hPcomm : (P : K →L[ℂ] K) ∈ L.commutant := by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro T hT
    exact (congrArg (fun a : L.toStarSubalgebra => (a : K →L[ℂ] K))
      (compressionSupport_commute rho hrho sigma hsigma ⟨T, hT⟩)).symm
  let p : L.commutant.toStarSubalgebra := ⟨(P : K →L[ℂ] K), hPcomm⟩
  have hp : IsStarProjection p := by
    have h := (isStarProjection_compressionSupport rho hrho sigma hsigma).map
      L.toStarSubalgebra.subtype
    exact ⟨Subtype.ext h.isIdempotentElem.eq, Subtype.ext h.isSelfAdjoint.star_eq⟩
  have hpcentral (a : L.commutant.toStarSubalgebra) : a * p = p * a := by
    apply Subtype.ext
    exact ((VonNeumannAlgebra.mem_commutant_iff.mp a.property)
      (P : K →L[ℂ] K) P.property).symm
  have hpq : p * q = q := by
    apply Subtype.ext
    change (P : K →L[ℂ] K).comp
        (U.toContinuousLinearMap.comp U.toContinuousLinearMap.adjoint) = _
    rw [← ContinuousLinearMap.comp_assoc,
      compressionSupport_comp_isometry rho hrho sigma hsigma U hU]
  let G := VonNeumannAlgebra.centralSupport L.commutant q
  have hGp : G * p = G :=
    VonNeumannAlgebra.centralSupport_le L.commutant hp hpcentral hpq
  have hGmem : (G : K →L[ℂ] K) ∈ L := by
    have h := VonNeumannAlgebra.centralHull_mem_commutant L.commutant {q}
    rw [VonNeumannAlgebra.commutant_commutant] at h
    exact h
  let g : L.toStarSubalgebra := ⟨(G : K →L[ℂ] K), hGmem⟩
  have hqU : (q : K →L[ℂ] K).comp U.toContinuousLinearMap = U.toContinuousLinearMap := by
    change (U.toContinuousLinearMap.comp U.toContinuousLinearMap.adjoint).comp
      U.toContinuousLinearMap = _
    rw [ContinuousLinearMap.comp_assoc, U.adjoint_comp_self,
      ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
  have hGU : (G : K →L[ℂ] K).comp U.toContinuousLinearMap = U.toContinuousLinearMap := by
    calc
      _ = (G : K →L[ℂ] K).comp ((q : K →L[ℂ] K).comp U.toContinuousLinearMap) :=
        congrArg (fun T => (G : K →L[ℂ] K).comp T) hqU.symm
      _ = (((G * q : L.commutant.toStarSubalgebra) : K →L[ℂ] K)).comp
          U.toContinuousLinearMap := (ContinuousLinearMap.comp_assoc _ _ _).symm
      _ = (q : K →L[ℂ] K).comp U.toContinuousLinearMap := by
        rw [VonNeumannAlgebra.centralSupport_mul_self]
      _ = U.toContinuousLinearMap := hqU
  have hzero : U.toContinuousLinearMap.adjoint.comp
      (((1 - g : L.toStarSubalgebra) : K →L[ℂ] K).comp U.toContinuousLinearMap) = 0 := by
    change U.toContinuousLinearMap.adjoint.comp
      (((1 : K →L[ℂ] K) - (G : K →L[ℂ] K)).comp U.toContinuousLinearMap) = 0
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp, hGU, sub_self, ContinuousLinearMap.comp_zero]
  have hPg : P * g = P := by
    have h := (compression_eq_zero_iff_compressionSupport_mul_eq_zero
      rho hrho sigma hsigma U hU (1 - g)).mp hzero
    change P * (1 - g) = 0 at h
    rw [mul_sub, mul_one, sub_eq_zero] at h
    exact h.symm
  change (P : K →L[ℂ] K) = (G : K →L[ℂ] K)
  calc
    _ = (P : K →L[ℂ] K) * (G : K →L[ℂ] K) :=
      (congrArg (fun a : L.toStarSubalgebra => (a : K →L[ℂ] K)) hPg).symm
    _ = (G : K →L[ℂ] K) * (P : K →L[ℂ] K) :=
      (congrArg (fun a : L.commutant.toStarSubalgebra => (a : K →L[ℂ] K))
        (hpcentral G)).symm
    _ = (G : K →L[ℂ] K) :=
      congrArg (fun a : L.commutant.toStarSubalgebra => (a : K →L[ℂ] K)) hGp

omit U hU

/-- The actual range is the concrete central summand of the large algebra. -/
theorem range_compressionLift :
    Set.range (compressionLift rho hrho sigma hsigma) =
      {T | compressionSupport rho hrho sigma hsigma * T = T} := by
  ext T
  constructor
  · rintro ⟨a, rfl⟩
    exact compressionSupport_mul_compressionLift rho hrho sigma hsigma a
  · intro hT
    obtain ⟨S, hS⟩ := surjective_envelopingRepresentationExtension rho hrho T
    refine ⟨envelopingRepresentationExtension sigma hsigma S, ?_⟩
    rw [compressionLift_envelopingRepresentationExtension, hS, hT]

/-- The lift with values in the supplied nonunital corner, preserving its
original carrier, star, multiplication and norm. -/
def compressionCornerLift :
    (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra →⋆ₙₐ[ℂ]
      VonNeumannAlgebra.corner (VonNeumannAlgebra.generated rho.unitization.range)
        (compressionSupport rho hrho sigma hsigma)
        (isStarProjection_compressionSupport rho hrho sigma hsigma) where
  toFun a := ⟨compressionLift rho hrho sigma hsigma a,
    compressionSupport_mul_compressionLift rho hrho sigma hsigma a,
    compressionLift_mul_compressionSupport rho hrho sigma hsigma a⟩
  map_zero' := Subtype.ext (map_zero (compressionLift rho hrho sigma hsigma))
  map_add' a b := Subtype.ext (map_add (compressionLift rho hrho sigma hsigma) a b)
  map_mul' a b := Subtype.ext (map_mul (compressionLift rho hrho sigma hsigma) a b)
  map_smul' c a := Subtype.ext (map_smul (compressionLift rho hrho sigma hsigma) c a)
  map_star' a := Subtype.ext (map_star (compressionLift rho hrho sigma hsigma) a)

include hrho hsigma U hU

theorem bijective_compressionCornerLift :
    Function.Bijective (compressionCornerLift rho hrho sigma hsigma) := by
  constructor
  · intro a b hab
    apply injective_compressionLift rho hrho sigma hsigma U hU
    exact congrArg Subtype.val hab
  · intro T
    have hT : (T : (VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra) ∈
        Set.range (compressionLift rho hrho sigma hsigma) := by
      rw [range_compressionLift]
      exact T.property.1
    obtain ⟨a, ha⟩ := hT
    exact ⟨a, Subtype.ext ha⟩

/-- A constructed equivalence from the small generated algebra to the
large algebra's central support corner. -/
def compressionCornerEquiv :
    (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra ≃⋆ₐ[ℂ]
      VonNeumannAlgebra.corner (VonNeumannAlgebra.generated rho.unitization.range)
        (compressionSupport rho hrho sigma hsigma)
        (isStarProjection_compressionSupport rho hrho sigma hsigma) :=
  StarAlgEquiv.ofBijective (compressionCornerLift rho hrho sigma hsigma)
    (bijective_compressionCornerLift rho hrho sigma hsigma U hU)

@[simp]
theorem compressionCornerEquiv_apply_coe
    (a : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra) :
    (compressionCornerEquiv rho hrho sigma hsigma U hU a :
      (VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra) =
        compressionLift rho hrho sigma hsigma a := rfl

/-- The inverse of the equivalence is exactly compression of the concrete
corner operator, not an unspecified isomorphic copy of the small algebra. -/
theorem compressionCornerEquiv_symm_apply_coe
    (T : VonNeumannAlgebra.corner (VonNeumannAlgebra.generated rho.unitization.range)
      (compressionSupport rho hrho sigma hsigma)
      (isStarProjection_compressionSupport rho hrho sigma hsigma)) :
    ((compressionCornerEquiv rho hrho sigma hsigma U hU).symm T : H →L[ℂ] H) =
      U.toContinuousLinearMap.adjoint.comp
        (((T : (VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra) :
          K →L[ℂ] K).comp U.toContinuousLinearMap) := by
  let a := (compressionCornerEquiv rho hrho sigma hsigma U hU).symm T
  have ha : compressionLift rho hrho sigma hsigma a =
      (T : (VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra) :=
    congrArg Subtype.val
      ((compressionCornerEquiv rho hrho sigma hsigma U hU).apply_symm_apply T)
  rw [← ha]
  exact (compression_compressionLift rho hrho sigma hsigma U hU a).symm

/-- Uniformly bounded strong convergence to zero is transported by the
actual corner lift. The proof uses the commutant orbit, not an inference
from the word `normal` or a finite-multiplicity assumption. -/
theorem stronglyConverges_compressionLift_zero
    {ι : Type t} (l : Filter ι)
    (a : ι → (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra)
    (ha : ContinuousLinearMap.StronglyConverges (fun i => (a i : H →L[ℂ] H)) l 0)
    (r : ℝ) (hr : ∀ i, ‖a i‖ ≤ r) :
    ContinuousLinearMap.StronglyConverges
      (fun i => (compressionLift rho hrho sigma hsigma (a i) : K →L[ℂ] K)) l 0 := by
  let L := VonNeumannAlgebra.generated rho.unitization.range
  let theta := compressionLift rho hrho sigma hsigma
  let P := compressionSupport rho hrho sigma hsigma
  let q : L.commutant.toStarSubalgebra :=
    ⟨U.toContinuousLinearMap.comp U.toContinuousLinearMap.adjoint,
      rangeProjection_mem_commutant rho hrho sigma hsigma U hU⟩
  have hnorm (i : ι) : ‖(theta (a i) : K →L[ℂ] K)‖ ≤ r := by
    change ‖compressionLift rho hrho sigma hsigma (a i)‖ ≤ r
    rw [norm_compressionLift rho hrho sigma hsigma U hU]
    exact hr i
  have hequi : Equicontinuous (fun i : ι => ((theta (a i) : K →L[ℂ] K) : K → K)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun d : ℝ => r * d)
      (by simpa only [mul_zero] using
        (tendsto_const_nhds.mul tendsto_id :
          Tendsto (fun d : ℝ => r * d) (𝓝 0) (𝓝 (r * 0))))
    intro x y i
    calc
      dist ((theta (a i) : K →L[ℂ] K) x) ((theta (a i) : K →L[ℂ] K) y) =
          ‖(theta (a i) : K →L[ℂ] K) (x - y)‖ := by rw [dist_eq_norm, map_sub]
      _ ≤ ‖(theta (a i) : K →L[ℂ] K)‖ * ‖x - y‖ :=
        (theta (a i) : K →L[ℂ] K).le_opNorm _
      _ ≤ r * ‖x - y‖ := mul_le_mul_of_nonneg_right (hnorm i) (norm_nonneg _)
      _ = r * dist x y := by rw [dist_eq_norm]
  let V : Submodule ℂ K :=
    { carrier := {x | Tendsto (fun i => (theta (a i) : K →L[ℂ] K) x) l (𝓝 0)}
      zero_mem' := by
        change Tendsto (fun i => (theta (a i) : K →L[ℂ] K) 0) l (𝓝 0)
        simpa only [map_zero] using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : K)) l (𝓝 0))
      add_mem' := by
        intro x y hx hy
        change Tendsto (fun i => (theta (a i) : K →L[ℂ] K) (x + y)) l (𝓝 0)
        simpa only [map_add, add_zero] using hx.add hy
      smul_mem' := by
        intro c x hx
        change Tendsto (fun i => (theta (a i) : K →L[ℂ] K) (c • x)) l (𝓝 0)
        simpa only [map_smul, smul_zero] using (tendsto_const_nhds (x := c)).smul hx }
  have hV : IsClosed (V : Set K) :=
    hequi.isClosed_setOfPred_tendsto (continuous_const : Continuous (fun _ : K => (0 : K)))
  have horbit (b : L.commutant.toStarSubalgebra) (x : K) :
      (b : K →L[ℂ] K) ((q : K →L[ℂ] K) x) ∈ V := by
    change Tendsto (fun i => (theta (a i) : K →L[ℂ] K)
      ((b : K →L[ℂ] K) ((q : K →L[ℂ] K) x))) l (𝓝 0)
    have heq :
        (fun i => (theta (a i) : K →L[ℂ] K)
          ((b : K →L[ℂ] K) ((q : K →L[ℂ] K) x))) =
        (fun i => (b : K →L[ℂ] K)
          (U ((a i : H →L[ℂ] H) (U.toContinuousLinearMap.adjoint x)))) := by
      funext i
      have hc := (VonNeumannAlgebra.mem_commutant_iff.mp b.property)
        (theta (a i) : K →L[ℂ] K) (theta (a i)).property
      have hi := congrArg (fun T : H →L[ℂ] K => T (U.toContinuousLinearMap.adjoint x))
        (compressionLift_intertwines rho hrho sigma hsigma U hU (a i))
      calc
        _ = (b : K →L[ℂ] K) ((theta (a i) : K →L[ℂ] K)
            ((q : K →L[ℂ] K) x)) := congrArg
              (fun T : K →L[ℂ] K => T ((q : K →L[ℂ] K) x)) hc
        _ = (b : K →L[ℂ] K)
            (U ((a i : H →L[ℂ] H) (U.toContinuousLinearMap.adjoint x))) :=
          congrArg (b : K →L[ℂ] K) hi
    rw [heq]
    have h := ((b : K →L[ℂ] K).comp U.toContinuousLinearMap).continuous.continuousAt.tendsto.comp
      (ha (U.toContinuousLinearMap.adjoint x))
    simpa only [Function.comp_def, ContinuousLinearMap.zero_apply, map_zero, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap] using h
  intro x
  have hPx : (P : K →L[ℂ] K) x ∈ V := by
    rw [show (P : K →L[ℂ] K) = (VonNeumannAlgebra.centralSupport L.commutant q :
      K →L[ℂ] K) from compressionSupport_eq_centralSupport rho hrho sigma hsigma U hU]
    exact VonNeumannAlgebra.centralSupport_apply_mem_of_forall_mul_apply_mem
      L.commutant q V hV horbit x
  change Tendsto (fun i => (theta (a i) : K →L[ℂ] K) x) l (𝓝 0)
  change Tendsto (fun i => (theta (a i) : K →L[ℂ] K) ((P : K →L[ℂ] K) x))
    l (𝓝 0) at hPx
  apply hPx.congr'
  exact Filter.Eventually.of_forall fun i =>
    congrArg (fun T : L.toStarSubalgebra => (T : K →L[ℂ] K) x)
      (compressionLift_mul_compressionSupport rho hrho sigma hsigma (a i))

/-- The same concrete inverse transports bounded strong convergence to
an arbitrary limit, by the proved zero-limit statement and linearity. -/
theorem stronglyConverges_compressionLift
    {ι : Type t} (l : Filter ι)
    (a : ι → (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra)
    (a0 : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra)
    (ha : ContinuousLinearMap.StronglyConverges (fun i => (a i : H →L[ℂ] H)) l
      (a0 : H →L[ℂ] H)) (r : ℝ) (hr : ∀ i, ‖a i‖ ≤ r) :
    ContinuousLinearMap.StronglyConverges
      (fun i => (compressionLift rho hrho sigma hsigma (a i) : K →L[ℂ] K)) l
      (compressionLift rho hrho sigma hsigma a0 : K →L[ℂ] K) := by
  have hsub : ContinuousLinearMap.StronglyConverges
      (fun i => ((a i - a0 :
        (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra) : H →L[ℂ] H))
      l 0 := by
    change ContinuousLinearMap.StronglyConverges (fun i => (a i : H →L[ℂ] H) - (a0 : H →L[ℂ] H)) l 0
    simpa only [sub_self] using ha.sub (ContinuousLinearMap.StronglyConverges.const
      (l := l) (a0 : H →L[ℂ] H))
  have hb (i : ι) : ‖a i - a0‖ ≤ r + ‖a0‖ :=
    (norm_sub_le (a i) a0).trans (add_le_add (hr i) (le_refl ‖a0‖))
  have hz := stronglyConverges_compressionLift_zero rho hrho sigma hsigma U hU
    l (fun i => a i - a0) hsub (r + ‖a0‖) hb
  have h := hz.add (ContinuousLinearMap.StronglyConverges.const
    (l := l) (compressionLift rho hrho sigma hsigma a0 : K →L[ℂ] K))
  have heq : (fun i =>
      (compressionLift rho hrho sigma hsigma (a i - a0) : K →L[ℂ] K) +
        (compressionLift rho hrho sigma hsigma a0 : K →L[ℂ] K)) =
      (fun i => (compressionLift rho hrho sigma hsigma (a i) : K →L[ℂ] K)) := by
    funext i
    exact congrArg
      (fun T : (VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra =>
        (T : K →L[ℂ] K))
      (show compressionLift rho hrho sigma hsigma (a i - a0) +
          compressionLift rho hrho sigma hsigma a0 =
          compressionLift rho hrho sigma hsigma (a i) by rw [map_sub, sub_add_cancel])
  rw [heq] at h
  simpa only [zero_add] using h

end MathlibAnnex.Analysis.CStarAlgebra.Representation
