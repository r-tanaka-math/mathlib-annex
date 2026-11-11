import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.Representation
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.WeakStarQuotientCorner

/-!
# The central kernel of an extended nondegenerate representation

The existing weakly closed ideal-support theorem is applied to the actual
enveloping representation extension. Its predual realization is the inverse
of the proved isometric equivalence with the literal Banach bidual. The
separate weak-star multiplication laws and the faithful WOT target carrier
are supplied here, rather than included as fields of a new structure.

The resulting complementary projection lives in the concrete envelope. Its
inverse image lives in the original `StrongDual` double dual and satisfies
the same statements for the existing explicit Arens product and involution.
No surjectivity of the represented extension is used or asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 120000
noncomputable section

open MathlibAnnex.RepresentedBidual MathlibAnnex.CentralKernelSection
open MathlibAnnex.WeakStarQuotientCorner

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every input to the pre-existing ideal-support construction is supplied
by the actual envelope, its original predual, and its represented extension. -/
private def envelopingRepresentationKernelSupport
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    KernelSupport (envelopingRepresentationExtension pi hnd) := by
  letI : PartialOrder (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
    _root_.CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
    _root_.CStarAlgebra.spectralOrderedRing _
  apply Classical.choice
  refine nonempty_kernelSupport (envelopingRepresentationExtension pi hnd)
    (bidualEnvelopingEquiv (A := A)).symm ?_ ?_
    (fun T : (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra =>
      ContinuousLinearMapWOT.ofCLM (T : H →L[ℂ] H)) ?_ ?_
  · intro T
    simpa only [weakEquiv_apply, weakEquiv_symm_apply,
      LinearIsometryEquiv.symm_symm, bidualEnvelopingEquiv_symm_mul (A := A),
      LinearIsometryEquiv.symm_apply_apply] using
      Bidual.continuous_arensProduct_right ((bidualEnvelopingEquiv (A := A)).symm T)
  · intro T
    simpa only [weakEquiv_apply, weakEquiv_symm_apply,
      LinearIsometryEquiv.symm_symm, bidualEnvelopingEquiv_symm_mul (A := A),
      LinearIsometryEquiv.symm_apply_apply] using
      MathlibAnnex.RepresentedBidual.continuous_arensProduct_left
        ((bidualEnvelopingEquiv (A := A)).symm T)
  · intro S T h
    apply Subtype.ext
    exact ContinuousLinearMapWOT.ofCLM_injective h
  · simpa only [weakEquiv_symm_apply, LinearIsometryEquiv.symm_symm] using
      envelopingRepresentationExtension_weakStar_wot pi hnd

/-- The central complementary support of the actual represented kernel,
as an element of the concrete envelope. -/
def envelopingRepresentationSupportProjection
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
  (envelopingRepresentationKernelSupport pi hnd).projection

@[simp]
theorem envelopingRepresentationSupportProjection_star
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    star (envelopingRepresentationSupportProjection pi hnd) =
      envelopingRepresentationSupportProjection pi hnd :=
  (envelopingRepresentationKernelSupport pi hnd).projection_star

@[simp]
theorem envelopingRepresentationSupportProjection_idem
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    envelopingRepresentationSupportProjection pi hnd *
        envelopingRepresentationSupportProjection pi hnd =
      envelopingRepresentationSupportProjection pi hnd :=
  (envelopingRepresentationKernelSupport pi hnd).projection_idem

theorem envelopingRepresentationSupportProjection_central
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    envelopingRepresentationSupportProjection pi hnd * T =
      T * envelopingRepresentationSupportProjection pi hnd :=
  (envelopingRepresentationKernelSupport pi hnd).projection_central T

/-- The representation sends its support projection to the target identity. -/
@[simp]
theorem envelopingRepresentationExtension_supportProjection
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    envelopingRepresentationExtension pi hnd
      (envelopingRepresentationSupportProjection pi hnd) = 1 :=
  (envelopingRepresentationKernelSupport pi hnd).q_projection

theorem norm_envelopingRepresentationSupportProjection_le
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    ‖envelopingRepresentationSupportProjection pi hnd‖ ≤ 1 :=
  (envelopingRepresentationKernelSupport pi hnd).projection_norm_le

/-- The kernel is precisely the annihilator of the constructed central
support projection. This does not require the extension to be onto. -/
theorem envelopingRepresentationExtension_eq_zero_iff
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    envelopingRepresentationExtension pi hnd T = 0 ↔
      envelopingRepresentationSupportProjection pi hnd * T = 0 := by
  constructor
  · exact (envelopingRepresentationKernelSupport pi hnd).projection_mul_kernel T
  · intro h
    have hq := congrArg (envelopingRepresentationExtension pi hnd) h
    simpa only [map_mul, envelopingRepresentationExtension_supportProjection,
      one_mul, map_zero] using hq

/-- The same constructed support projection on the literal Banach bidual,
using the inverse of the actual envelope equivalence. -/
def bidualRepresentationSupportProjection
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    StrongDual ℂ (StrongDual ℂ A) :=
  (bidualEnvelopingEquiv (A := A)).symm (envelopingRepresentationSupportProjection pi hnd)

@[simp]
theorem bidualRepresentationSupportProjection_star
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    bidualStar (bidualRepresentationSupportProjection pi hnd) =
      bidualRepresentationSupportProjection pi hnd := by
  have h := congrArg (bidualEnvelopingEquiv (A := A)).symm
    (envelopingRepresentationSupportProjection_star pi hnd)
  exact (bidualEnvelopingEquiv_symm_star (A := A)
    (envelopingRepresentationSupportProjection pi hnd)).symm.trans h

@[simp]
theorem bidualRepresentationSupportProjection_idem
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    arensProduct (bidualRepresentationSupportProjection pi hnd)
        (bidualRepresentationSupportProjection pi hnd) =
      bidualRepresentationSupportProjection pi hnd := by
  have h := congrArg (bidualEnvelopingEquiv (A := A)).symm
    (envelopingRepresentationSupportProjection_idem pi hnd)
  let p := envelopingRepresentationSupportProjection pi hnd
  exact (bidualEnvelopingEquiv_symm_mul (A := A) p p).symm.trans h

private theorem pullback_central_mul {X Y : Type*} [Mul Y]
    (e : X ≃ Y) (m : X → X → X) (hm : ∀ x y, e (m x y) = e x * e y)
    (p : Y) (hp : ∀ y, p * y = y * p) (x : X) : m (e.symm p) x = m x (e.symm p) := by
  apply e.injective
  rw [hm, hm, e.apply_symm_apply, hp]

private theorem pullback_mul_zero {X Y : Type*} [Zero X] [Zero Y] [Mul Y]
    (e : X ≃ Y) (m : X → X → X) (hm : ∀ x y, e (m x y) = e x * e y)
    (hz : e 0 = 0) (p : Y) (x : X) : m (e.symm p) x = 0 ↔ p * e x = 0 := by
  have h : e (m (e.symm p) x) = p * e x := by rw [hm, e.apply_symm_apply]
  exact ⟨fun h0 => h.symm.trans ((congrArg e h0).trans hz),
    fun h0 => e.injective (h.trans (h0.trans hz.symm))⟩

theorem bidualRepresentationSupportProjection_central
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    arensProduct (bidualRepresentationSupportProjection pi hnd) F =
      arensProduct F (bidualRepresentationSupportProjection pi hnd) := by
  exact pullback_central_mul (bidualEnvelopingEquiv (A := A)).toEquiv arensProduct
    (bidualEnvelopingEquiv_arensProduct (A := A)) (envelopingRepresentationSupportProjection pi hnd)
    (envelopingRepresentationSupportProjection_central pi hnd) F

@[simp]
theorem extension_bidualRepresentationSupportProjection
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    extension pi (bidualRepresentationSupportProjection pi hnd) = 1 := by
  have h := congrArg
    (fun T : (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra =>
      (T : H →L[ℂ] H))
    (envelopingRepresentationExtension_supportProjection pi hnd)
  unfold bidualRepresentationSupportProjection
  exact (envelopingRepresentationExtension_apply_coe pi hnd
    (envelopingRepresentationSupportProjection pi hnd)).symm.trans h

theorem norm_bidualRepresentationSupportProjection_le
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate) :
    ‖bidualRepresentationSupportProjection pi hnd‖ ≤ 1 := by
  unfold bidualRepresentationSupportProjection
  exact ((bidualEnvelopingEquiv (A := A)).symm.norm_map
    (envelopingRepresentationSupportProjection pi hnd)).le.trans
      (norm_envelopingRepresentationSupportProjection_le pi hnd)

/-- The exact represented kernel characterization for arbitrary literal
bidual elements and the already defined Arens multiplication. -/
theorem extension_eq_zero_iff_arensProduct_supportProjection
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    extension pi F = 0 ↔
      arensProduct (bidualRepresentationSupportProjection pi hnd) F = 0 := by
  constructor
  · intro hF
    have hq : envelopingRepresentationExtension pi hnd
        (bidualEnvelopingEquiv (A := A) F) = 0 := by
      apply Subtype.ext
      change extension pi ((bidualEnvelopingEquiv (A := A)).symm
        (bidualEnvelopingEquiv (A := A) F)) = 0
      rwa [LinearIsometryEquiv.symm_apply_apply]
    have hp := (envelopingRepresentationExtension_eq_zero_iff pi hnd
      (bidualEnvelopingEquiv (A := A) F)).mp hq
    let e := bidualEnvelopingEquiv (A := A)
    exact (pullback_mul_zero e.toEquiv arensProduct (bidualEnvelopingEquiv_arensProduct (A := A))
      e.map_zero (envelopingRepresentationSupportProjection pi hnd) F).mpr hp
  · intro hF
    let p := bidualRepresentationSupportProjection pi hnd
    have he := (extension_arensProduct pi p F).symm.trans
      ((congrArg (extension pi) hF).trans (extension pi).map_zero)
    exact (one_mul (extension pi F)).symm.trans
      ((congrArg (· * extension pi F) (extension_bidualRepresentationSupportProjection pi hnd)).symm.trans he)

end MathlibAnnex.Analysis.CStarAlgebra
