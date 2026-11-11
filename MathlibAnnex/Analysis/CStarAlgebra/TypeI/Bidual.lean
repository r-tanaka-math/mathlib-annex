import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.HereditarySupport
import MathlibAnnex.Analysis.CStarAlgebra.Bidual.EnvelopingEquivalence
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.ElementTransport
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.KernelAlgebra
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.CentralSplit
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.CentralPart

/-!
# Internal type I and the genuine enveloping bidual

The internal quotient condition forces every weakly generated
representation algebra to be type I. Its proof cuts the representation
at the complementary central projection of the existing type I part,
uses the actual kernel quotient, and produces an abelian support
projection in that complement.

The bidual predicate refers to the all-state enveloping algebra. The
proved isometric identification with the literal Banach bidual gives an
equivalent formulation entirely in terms of the existing Arens product
and bidual involution. No product or norm on the Banach dual is replaced.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section

open Set
open MathlibAnnex.RepresentedBidual
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance 100] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

private theorem exists_mul_ne_zero_of_wotDense
    (M : VonNeumannAlgebra H) (rho : A →⋆ₙₐ[ℂ] M.toStarSubalgebra)
    (hdense : ∀ T : M.toStarSubalgebra,
      ContinuousLinearMapWOT.ofCLM (T : H →L[ℂ] H) ∈
        closure (Set.range (fun a : A =>
          ContinuousLinearMapWOT.ofCLM (rho a : H →L[ℂ] H))))
    (p : M.toStarSubalgebra) (hp : p ≠ 0) :
    ∃ a : A, p * rho a ≠ 0 := by
  classical
  by_contra hn
  have hzero : ∀ a : A, p * rho a = 0 := by
    simpa only [not_exists, not_not] using hn
  have hlim :
      ContinuousLinearMapWOT.ofCLM (p : H →L[ℂ] H) *
        ContinuousLinearMapWOT.ofCLM ((1 : M.toStarSubalgebra) : H →L[ℂ] H) = 0 := by
    apply closure_minimal ?_ (isClosed_eq
      (show Continuous (fun T : H →WOT[ℂ] H =>
        ContinuousLinearMapWOT.ofCLM (p : H →L[ℂ] H) * T) by fun_prop)
      continuous_const) (hdense 1)
    rintro _ ⟨a, rfl⟩
    change ContinuousLinearMapWOT.ofCLM ((p * rho a : M.toStarSubalgebra) :
      H →L[ℂ] H) = 0
    rw [hzero a]
    rfl
  apply hp
  apply Subtype.ext
  have h := ContinuousLinearMapWOT.ofCLM_injective hlim
  change (p : H →L[ℂ] H) * 1 = 0 at h
  exact (mul_one (p : H →L[ℂ] H)).symm.trans h

/-- A nonzero central part of a weakly generated representation of an
internally type I algebra contains a nonzero abelian projection.
The quotient used in the proof is the genuine kernel quotient of the
central cut, with its existing quotient norm. -/
theorem IsInternalTypeI.exists_isAbelianProjection_mul_eq_of_wotDense
    (hA : IsInternalTypeI A)
    (M : VonNeumannAlgebra H) (rho : A →⋆ₙₐ[ℂ] M.toStarSubalgebra)
    (hdense : ∀ T : M.toStarSubalgebra,
      ContinuousLinearMapWOT.ofCLM (T : H →L[ℂ] H) ∈
        closure (Set.range (fun a : A =>
          ContinuousLinearMapWOT.ofCLM (rho a : H →L[ℂ] H))))
    (p : M.toStarSubalgebra) (hp : IsStarProjection p)
    (hc : ∀ x : M.toStarSubalgebra, x * p = p * x) (hp0 : p ≠ 0) :
    ∃ q : M.toStarSubalgebra, M.IsAbelianProjection q ∧ q ≠ 0 ∧ q * p = q := by
  let cut : A →⋆ₙₐ[ℂ] M.toStarSubalgebra :=
    ((NonUnitalStarSubalgebraClass.subtype (R := ℂ) (M.corner p hp)).comp
      (M.centralCornerHom p hp hc)).comp rho
  have cut_apply (a : A) : cut a = p * rho a := rfl
  have hcut : ∃ a : A, cut a ≠ 0 := by
    simpa only [cut_apply] using exists_mul_ne_zero_of_wotDense M rho hdense p hp0
  letI : NonUnitalCStarAlgebra (HomKernelQuotient cut) :=
    HomKernelQuotient.instNonUnitalCStarAlgebra cut
  letI : Nontrivial (HomKernelQuotient cut) :=
    HomKernelQuotient.nontrivial_of_exists_apply_ne_zero cut hcut
  obtain ⟨b, hb0, hb⟩ := hA.exists_of_surjective (B := HomKernelQuotient cut)
    (HomKernelQuotient.mkHom cut) (HomKernelQuotient.mkHom_surjective cut)
  let psi : HomKernelQuotient cut →⋆ₙₐ[ℂ] M.toStarSubalgebra :=
    HomKernelQuotient.toCodomainHom cut
  let s : M.toStarSubalgebra := psi b
  have hpsi (a : A) : psi (HomKernelQuotient.mkHom cut a) = p * rho a := rfl
  have hs0 : s ≠ 0 := by
    intro hz
    apply hb0
    apply HomKernelQuotient.toCodomainHom_injective cut
    simpa only [map_zero] using hz
  have hps : p * s = s := by
    obtain ⟨a, ha⟩ := HomKernelQuotient.mkHom_surjective cut b
    change p * psi b = psi b
    rw [← ha, hpsi, ← mul_assoc, hp.isIdempotentElem.eq]
  have hsp : s * p = s := (hc s).trans hps
  have hs : IsSelfAdjoint s := hb.nonneg.isSelfAdjoint.map psi
  have hsandwich (a : A) :
      s * rho a * s = psi (b * HomKernelQuotient.mkHom cut a * b) := by
    rw [map_mul, map_mul, hpsi]
    change s * rho a * s = s * (p * rho a) * s
    rw [← mul_assoc s p (rho a), hsp]
  have hsource (a c : A) :
      (s * rho a * s) * (s * rho c * s) =
        (s * rho c * s) * (s * rho a * s) := by
    have ha : b * HomKernelQuotient.mkHom cut a * b ∈ hereditarySubalgebra b := by
      simpa only [hb.nonneg.isSelfAdjoint.star_eq] using
        sandwich_mem_hereditarySubalgebra b (HomKernelQuotient.mkHom cut a)
    have hc' : b * HomKernelQuotient.mkHom cut c * b ∈ hereditarySubalgebra b := by
      simpa only [hb.nonneg.isSelfAdjoint.star_eq] using
        sandwich_mem_hereditarySubalgebra b (HomKernelQuotient.mkHom cut c)
    rw [hsandwich a, hsandwich c]
    simpa only [map_mul] using congrArg psi (hb.mul_comm ha hc')
  have hfull (T U : M.toStarSubalgebra) :
      (s * T * s) * (s * U * s) = (s * U * s) * (s * T * s) := by
    apply Subtype.ext
    exact sandwiches_commute_of_mem_wotClosure_range
      (fun a : A => (rho a : H →L[ℂ] H)) s
      (fun a c => congrArg Subtype.val (hsource a c)) (hdense T) (hdense U)
  have hab : M.IsAbelianProjection (M.leftSupport s) :=
    isAbelianProjection_leftSupport_of_sandwiches_commute M s hs hfull
  refine ⟨M.leftSupport s, hab, ?_, ?_⟩
  · exact fun hz => hs0 ((M.leftSupport_eq_zero_iff s).mp hz)
  · exact ((M.isStarProjection_leftSupport s).le_iff_mul_eq_left hp).mp
      ((M.leftSupport_le_iff s hp).mpr hps)

/-- Internal type I implies type I for any weakly generated representation
algebra. The argument uses only the existing abelian central support and
does not assume a factor representation or separability. -/
theorem IsInternalTypeI.isTypeI_of_wotDense (hA : IsInternalTypeI A)
    (M : VonNeumannAlgebra H) (rho : A →⋆ₙₐ[ℂ] M.toStarSubalgebra)
    (hdense : ∀ T : M.toStarSubalgebra,
      ContinuousLinearMapWOT.ofCLM (T : H →L[ℂ] H) ∈
        closure (Set.range (fun a : A =>
          ContinuousLinearMapWOT.ofCLM (rho a : H →L[ℂ] H)))) :
    M.IsTypeI := by
  have hcomplement : 1 - M.abelianCentralSupport = 0 := by
    by_contra hn
    obtain ⟨q, hq, hq0, hqp⟩ :=
      hA.exists_isAbelianProjection_mul_eq_of_wotDense M rho hdense
        (1 - M.abelianCentralSupport) M.isStarProjection_abelianCentralSupport.one_sub
        (M.one_sub_commutes M.abelianCentralSupport M.abelianCentralSupport_commute) hn
    exact hq0 (VonNeumannAlgebra.eq_zero_of_abelian_of_mul_complement_eq hq hqp)
  have hz : M.abelianCentralSupport = 1 := (sub_eq_zero.mp hcomplement).symm
  apply (M.isTypeI_iff_one).mpr
  simpa only [hz] using M.isTypeIProjection_abelianCentralSupport

/-- The all-state universal envelope of an internally type I algebra is type I. -/
theorem IsInternalTypeI.isTypeI_envelopingVonNeumannAlgebra
    (hA : IsInternalTypeI A) :
    (envelopingVonNeumannAlgebra (A := A)).IsTypeI := by
  apply hA.isTypeI_of_wotDense (envelopingVonNeumannAlgebra (A := A))
    (envelopingInclusion (A := A))
  intro T
  simpa only [← Set.range_comp, Function.comp_def, envelopingInclusion_apply_coe (A := A)] using
    (mem_envelopingVonNeumannAlgebra_iff_mem_wotClosure T.val).mp T.property

/-- Type I of the genuine Banach bidual, represented by its proved all-state
enveloping realization. The raw Arens formulation below proves that this
predicate refers to the literal double strong dual and its existing operations. -/
def IsTypeIBidual (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  (envelopingVonNeumannAlgebra (A := A)).IsTypeI

/-- Projection equations in the concrete envelope are precisely the
existing product and involution equations in the literal Banach bidual. -/
theorem isStarProjection_bidualEnvelopingEquiv_iff
    (P : StrongDual ℂ (StrongDual ℂ A)) :
    IsStarProjection (bidualEnvelopingEquiv (A := A) P) ↔
      arensProduct P P = P ∧ bidualStar P = P := by
  let E := bidualEnvelopingEquiv (A := A)
  have hmul (F G : StrongDual ℂ (StrongDual ℂ A)) :
      E (arensProduct F G) = E F * E G :=
    bidualEnvelopingEquiv_arensProduct (A := A) F G
  have hstar (F : StrongDual ℂ (StrongDual ℂ A)) :
      E (bidualStar F) = star (E F) := bidualEnvelopingEquiv_bidualStar (A := A) F
  constructor
  · intro h
    exact ⟨E.injective ((hmul P P).trans h.isIdempotentElem.eq),
      E.injective ((hstar P).trans h.isSelfAdjoint.star_eq)⟩
  · rintro ⟨hm, hs⟩
    exact ⟨(hmul P P).symm.trans (congrArg E hm),
      (hstar P).symm.trans (congrArg E hs)⟩

/-- Abelian support corners can be expressed without changing the carrier,
multiplication, involution or norm of the double strong dual. -/
theorem isAbelianProjection_bidualEnvelopingEquiv_iff
    (P : StrongDual ℂ (StrongDual ℂ A)) :
    (envelopingVonNeumannAlgebra (A := A)).IsAbelianProjection
        (bidualEnvelopingEquiv (A := A) P) ↔
      arensProduct P P = P ∧ bidualStar P = P ∧
        ∀ X Y : StrongDual ℂ (StrongDual ℂ A),
          arensProduct P X = X → arensProduct X P = X →
          arensProduct P Y = Y → arensProduct Y P = Y →
          arensProduct X Y = arensProduct Y X := by
  let E := bidualEnvelopingEquiv (A := A)
  have hmul (F G : StrongDual ℂ (StrongDual ℂ A)) :
      E (arensProduct F G) = E F * E G :=
    bidualEnvelopingEquiv_arensProduct (A := A) F G
  have hfix (F G Z : StrongDual ℂ (StrongDual ℂ A)) :
      arensProduct F G = Z ↔ E F * E G = E Z :=
    ⟨fun h => (hmul F G).symm.trans (congrArg E h),
      fun h => E.injective ((hmul F G).trans h)⟩
  constructor
  · intro hp
    have hproj := (isStarProjection_bidualEnvelopingEquiv_iff (A := A) P).mp hp.1
    refine ⟨hproj.1, hproj.2, ?_⟩
    intro X Y hPX hXP hPY hYP
    have h := hp.mul_comm ((hfix P X X).mp hPX) ((hfix X P X).mp hXP)
      ((hfix P Y Y).mp hPY) ((hfix Y P Y).mp hYP)
    exact E.injective ((hmul X Y).trans (h.trans (hmul Y X).symm))
  · rintro ⟨hm, hs, hcomm⟩
    refine ⟨(isStarProjection_bidualEnvelopingEquiv_iff (A := A) P).mpr ⟨hm, hs⟩, ?_⟩
    apply (E.surjective.forall₂ (p := fun x y => E P * x = x → x * E P = x →
      E P * y = y → y * E P = y → x * y = y * x)).mpr
    intro X Y hPX hXP hPY hYP
    have h := hcomm X Y ((hfix P X X).mpr hPX) ((hfix X P X).mpr hXP)
      ((hfix P Y Y).mpr hPY) ((hfix Y P Y).mpr hYP)
    exact (hmul X Y).symm.trans ((congrArg E h).trans (hmul Y X))

private theorem transfer_projection_criterion {X Y : Type*} [Zero X] [Zero Y] [Mul Y]
    (e : X ≃ Y) (m : X → X → X) (inv : X → X) (proj abel : Y → Prop)
    (ez : e 0 = 0) (em : ∀ x y, e (m x y) = e x * e y)
    (pr : ∀ p, proj (e p) ↔ m p p = p ∧ inv p = p)
    (ab : ∀ p, abel (e p) ↔ m p p = p ∧ inv p = p ∧
      ∀ x y, m p x = x → m x p = x → m p y = y → m y p = y → m x y = m y x) :
    (∀ p, proj p → p ≠ 0 → ∃ q, abel q ∧ q ≠ 0 ∧ q * p = q) ↔
      ∀ p, m p p = p → inv p = p → p ≠ 0 → ∃ q,
        m q q = q ∧ inv q = q ∧ q ≠ 0 ∧ m q p = q ∧
        ∀ x y, m q x = x → m x q = x → m q y = y → m y q = y → m x y = m y x := by
  have nz (x : X) : e x ≠ 0 ↔ x ≠ 0 :=
    ⟨fun h hx => h ((congrArg e hx).trans ez),
      fun h hx => h (e.injective (hx.trans ez.symm))⟩
  constructor
  · intro h p hpp hs hp
    obtain ⟨q, hq, hn, hqp⟩ := h (e p) ((pr p).mpr ⟨hpp, hs⟩) ((nz p).mpr hp)
    obtain ⟨b, rfl⟩ := e.surjective q
    have hb := (ab b).mp hq
    exact ⟨b, hb.1, hb.2.1, (nz b).mp hn, e.injective ((em b p).trans hqp), hb.2.2⟩
  · intro h p
    obtain ⟨a, rfl⟩ := e.surjective p
    intro hp hn
    have ha := (pr a).mp hp
    obtain ⟨q, hqq, hs, hq, hqa, hc⟩ := h a ha.1 ha.2 ((nz a).mp hn)
    exact ⟨e q, (ab q).mpr ⟨hqq, hs, hc⟩, (nz q).mpr hq,
      (em q a).symm.trans (congrArg e hqa)⟩

set_option maxHeartbeats 3500000 in
/-- The bidual type I predicate is exactly the projection/corner criterion
written on literal `StrongDual ℂ (StrongDual ℂ A)`, using the original
scalar-valued Arens operations. -/
theorem isTypeIBidual_iff_arensProduct :
    IsTypeIBidual A ↔
      ∀ P : StrongDual ℂ (StrongDual ℂ A),
        arensProduct P P = P → bidualStar P = P → P ≠ 0 →
        ∃ Q : StrongDual ℂ (StrongDual ℂ A),
          arensProduct Q Q = Q ∧ bidualStar Q = Q ∧ Q ≠ 0 ∧
          arensProduct Q P = Q ∧
          ∀ X Y : StrongDual ℂ (StrongDual ℂ A),
            arensProduct Q X = X → arensProduct X Q = X →
            arensProduct Q Y = Y → arensProduct Y Q = Y →
            arensProduct X Y = arensProduct Y X := by
  let E := bidualEnvelopingEquiv (A := A)
  exact transfer_projection_criterion E.toEquiv arensProduct bidualStar IsStarProjection
    (envelopingVonNeumannAlgebra (A := A)).IsAbelianProjection E.map_zero
    (bidualEnvelopingEquiv_arensProduct (A := A))
    (isStarProjection_bidualEnvelopingEquiv_iff (A := A))
    (isAbelianProjection_bidualEnvelopingEquiv_iff (A := A))

theorem IsInternalTypeI.isTypeIBidual (hA : IsInternalTypeI A) : IsTypeIBidual A :=
  hA.isTypeI_envelopingVonNeumannAlgebra

end MathlibAnnex.Analysis.CStarAlgebra
