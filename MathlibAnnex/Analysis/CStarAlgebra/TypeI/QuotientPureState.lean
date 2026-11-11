/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import Mathlib.RingTheory.Ideal.Maps
import MathlibAnnex.Analysis.CStarAlgebra.PureStateGNS.IrreduciblePure
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.Image
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.SurjectiveRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.State.Ideal
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.PureStateExtension
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.UnitalQuotient

/-!
# Pure state extensions compatible with a closed ideal

A pure state whose GNS action kills the kernel of a surjective star
homomorphism descends to a genuine norm-one pure state on its codomain.
The descended functional is a unit-vector coefficient of the factored GNS
representation. Thus its positivity and continuity concern the existing
C-star norm, rather than an assumed quotient-functional norm.

For a closed same-unit subalgebra, the codomain is the literal closed range
inside the actual closed-ideal quotient. Extend there, pull the state back,
and apply the existing ideal-annihilation theorem to its whole GNS action.
No separability, faithful representation, or compactness assumption is used.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

section SurjectiveRepresentation

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A representation factors through an actual surjective star homomorphism
when it kills that map's kernel. Ring addition, multiplication, and the unit
are supplied by Mathlib's existing surjective ring-homomorphism lift. -/
theorem Representation.exists_factor_of_surjective
    (pi : Representation A H) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (hker : ∀ a : A, q a = 0 → pi a = 0) :
    ∃ sigma : Representation B H, ∀ a : A, sigma (q a) = pi a := by
  have hle : RingHom.ker q.toAlgHom.toRingHom ≤ RingHom.ker pi.toAlgHom.toRingHom := by
    intro a ha
    exact RingHom.mem_ker.mpr (hker a (RingHom.mem_ker.mp ha))
  let f : B →+* (H →L[ℂ] H) := q.toAlgHom.toRingHom.liftOfSurjective hq
    ⟨pi.toAlgHom.toRingHom, hle⟩
  have hf (a : A) : f (q a) = pi a :=
    RingHom.liftOfSurjective_comp_apply q.toAlgHom.toRingHom hq
      ⟨pi.toAlgHom.toRingHom, hle⟩ a
  let sigma : Representation B H :=
    { toAlgHom :=
        { f with
          commutes' := fun c => by
            change f (algebraMap ℂ B c) = algebraMap ℂ (H →L[ℂ] H) c
            exact (congrArg f (q.commutes c).symm).trans ((hf _).trans (pi.commutes c)) }
      map_star' := fun b => by
        obtain ⟨a, rfl⟩ := hq b
        change f (star (q a)) = star (f (q a))
        rw [← map_star q, hf, map_star pi, hf] }
  exact ⟨sigma, hf⟩

end SurjectiveRepresentation

section States

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A normalized positive continuous functional has norm one. Its
normalization itself rules out the zero algebra. -/
theorem norm_eq_one_of_mem_stateSpace
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) : ‖phi‖ = 1 := by
  have hone : (1 : A) ≠ 0 := by
    intro hzero
    have h := hphi.2
    rw [hzero, map_zero] at h
    exact zero_ne_one h
  letI : Nontrivial A := nontrivial_of_ne (1 : A) 0 hone
  apply le_antisymm
  · exact norm_le_one_of_mem_weakStateSpace (phi := StrongDual.toWeakDual phi) hphi
  · have h := phi.le_opNorm (1 : A)
    simpa only [hphi.2, norm_one, mul_one] using h

/-- Descend a pure state through a surjective star homomorphism by factoring
its concrete GNS representation. The original kernel hypothesis concerns
the whole represented operator, not merely one vector coefficient. -/
theorem exists_pure_state_descent_of_surjective
    (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (phi : A →L[ℂ] ℂ) (hphi : IsPureState A phi)
    (hker : ∀ a : A, q a = 0 →
      (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom a = 0) :
    ∃ theta : B →L[ℂ] ℂ,
      theta ∈ stateSpace B ∧ IsPureState B theta ∧ ‖theta‖ = 1 ∧
      ∀ a : A, theta (q a) = phi a := by
  let pi := (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom
  let xi := stateGNSVector phi hphi.1
  have hxi : ‖xi‖ = 1 := norm_stateGNSVector phi hphi.1
  have hxi_ne : xi ≠ 0 := by
    intro hzero
    simpa [hzero] using hxi
  letI : Nontrivial (positiveLinearMapOfMemStateSpace phi hphi.1).GNS :=
    nontrivial_of_ne xi 0 hxi_ne
  have hpi : Representation.IsIrreducible pi :=
    (Representation.isIrreducible_iff_starAlgHom pi).2
      (MathlibAnnex.CStarAlgebra.isIrreducible_pureState_gnsStarAlgHom phi hphi.1 hphi)
  obtain ⟨sigma, hsigma⟩ := Representation.exists_factor_of_surjective pi q hq hker
  have hcomp : sigma.toNonUnitalStarAlgHom.comp q.toNonUnitalStarAlgHom =
      pi.toNonUnitalStarAlgHom := by
    exact NonUnitalStarAlgHom.ext hsigma
  have hirr : Representation.IsIrreducible sigma := by
    apply (NonUnitalCStarRepresentation.isIrreducible_comp_iff_of_surjective
      sigma.toNonUnitalStarAlgHom q.toNonUnitalStarAlgHom hq).1
    rw [hcomp]
    exact hpi
  let theta : B →L[ℂ] ℂ := Representation.vectorFunctional sigma xi
  have htheta : theta ∈ stateSpace B := vectorFunctional_mem_stateSpace sigma xi hxi
  have hpure : IsPureState B theta :=
    MathlibAnnex.CStarAlgebra.isPureState_vectorFunctional_of_isIrreducible sigma hirr xi hxi
  refine ⟨theta, htheta, hpure, norm_eq_one_of_mem_stateSpace theta htheta, ?_⟩
  intro a
  change inner ℂ xi (sigma (q a) xi) = phi a
  rw [hsigma]
  exact inner_gnsStarAlgHom_stateGNSVector phi hphi.1 a

/-- Surjective pullback of a pure state is pure. It is constructed as a
vector coefficient of the pulled-back irreducible GNS representation, and
the displayed formula is literal equality of values on every source element. -/
theorem exists_pure_state_pullback_of_surjective
    (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (theta : B →L[ℂ] ℂ) (htheta : IsPureState B theta) :
    ∃ psi : A →L[ℂ] ℂ,
      psi ∈ stateSpace A ∧ IsPureState A psi ∧ ‖psi‖ = 1 ∧
      ∀ a : A, psi a = theta (q a) := by
  let sigma := (positiveLinearMapOfMemStateSpace theta htheta.1).gnsStarAlgHom
  let xi := stateGNSVector theta htheta.1
  have hxi : ‖xi‖ = 1 := norm_stateGNSVector theta htheta.1
  have hxi_ne : xi ≠ 0 := by
    intro hzero
    simpa [hzero] using hxi
  letI : Nontrivial (positiveLinearMapOfMemStateSpace theta htheta.1).GNS :=
    nontrivial_of_ne xi 0 hxi_ne
  have hsigma : Representation.IsIrreducible sigma :=
    (Representation.isIrreducible_iff_starAlgHom sigma).2
      (MathlibAnnex.CStarAlgebra.isIrreducible_pureState_gnsStarAlgHom
        theta htheta.1 htheta)
  let pi : Representation A (positiveLinearMapOfMemStateSpace theta htheta.1).GNS :=
    sigma.comp q
  have hpi : Representation.IsIrreducible pi :=
    (NonUnitalCStarRepresentation.isIrreducible_comp_iff_of_surjective
      sigma.toNonUnitalStarAlgHom q.toNonUnitalStarAlgHom hq).2 hsigma
  let psi : A →L[ℂ] ℂ := Representation.vectorFunctional pi xi
  have hpsi : psi ∈ stateSpace A := vectorFunctional_mem_stateSpace pi xi hxi
  have hpure : IsPureState A psi :=
    MathlibAnnex.CStarAlgebra.isPureState_vectorFunctional_of_isIrreducible pi hpi xi hxi
  refine ⟨psi, hpsi, hpure, norm_eq_one_of_mem_stateSpace psi hpsi, ?_⟩
  intro a
  exact inner_gnsStarAlgHom_stateGNSVector theta htheta.1 (q a)

end States

section SubalgebraExtension

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
variable [PartialOrder D] [StarOrderedRing D]

/-- Extend a prescribed pure state through the literal image of a closed
same-unit subalgebra under a star homomorphism. The resulting
state on the codomain has norm one and the prescribed pullback on `D`. -/
theorem exists_pure_state_extension_through_hom
    (q : A →⋆ₐ[ℂ] B)
    (phi : D →L[ℂ] ℂ) (hphi : IsPureState D phi)
    (hker : ∀ d : D, q (d : A) = 0 →
      (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d = 0) :
    ∃ theta : B →L[ℂ] ℂ,
      theta ∈ stateSpace B ∧ IsPureState B theta ∧ ‖theta‖ = 1 ∧
      ∀ d : D, theta (q (d : A)) = phi d := by
  let r : D →⋆ₐ[ℂ] B := q.comp D.subtype
  let E : StarSubalgebra ℂ B := r.range
  have hE : IsClosed (E : Set B) :=
    HomKernelQuotient.isClosed_image r.toNonUnitalStarAlgHom
  letI : IsClosed (E : Set B) := hE
  let orderE : PartialOrder E := _root_.CStarAlgebra.spectralOrder E
  letI : LE E := orderE.toLE
  letI : LT E := orderE.toLT
  letI : PartialOrder E := orderE
  letI : StarOrderedRing E := _root_.CStarAlgebra.spectralOrderedRing E
  have hr : Function.Surjective r.rangeRestrict := by
    intro b
    obtain ⟨d, hd⟩ := b.property
    exact ⟨d, Subtype.ext hd⟩
  have hfactor : ∀ d : D, r.rangeRestrict d = 0 →
      (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d = 0 := by
    intro d hd
    apply hker d
    exact congrArg Subtype.val hd
  obtain ⟨eta, heta, heta_pure, heta_norm, heta_pull⟩ :=
    exists_pure_state_descent_of_surjective r.rangeRestrict hr phi hphi hfactor
  have hone : (1 : B) ≠ 0 := by
    intro hzero
    have hzeroE : (1 : E) = 0 := Subtype.ext hzero
    have h := heta.2
    rw [hzeroE, map_zero] at h
    exact zero_ne_one h
  letI : Nontrivial B := nontrivial_of_ne (1 : B) 0 hone
  obtain ⟨theta, htheta, hpure, hext⟩ := exists_pure_state_extension E eta heta_pure
  refine ⟨theta, htheta, hpure, norm_eq_one_of_mem_stateSpace theta htheta, ?_⟩
  intro d
  exact (hext (r.rangeRestrict d)).trans (heta_pull d)

/-- A closed ideal compatible with the original pure GNS kernel admits a
pure ambient extension annihilating it in its whole GNS representation.
The actual closed-ideal quotient and its original Banach norm are used. -/
theorem exists_pure_state_extension_annihilating_ideal
    (phi : D →L[ℂ] ℂ) (hphi : IsPureState D phi)
    (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (hker : ∀ d : D, (d : A) ∈ J →
      (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d = 0) :
    ∃ (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ stateSpace A),
      IsPureState A psi ∧ (∀ d : D, psi d = phi d) ∧
      ∀ a : A, a ∈ J →
        (positiveLinearMapOfMemStateSpace psi hpsi).gnsStarAlgHom a = 0 := by
  letI := ClosedIdealQuotient.quotientCStarAlgebra J hJ
  let orderQ : PartialOrder (ClosedIdealQuotient.Quotient J hJ) :=
    _root_.CStarAlgebra.spectralOrder (ClosedIdealQuotient.Quotient J hJ)
  letI : LE (ClosedIdealQuotient.Quotient J hJ) := orderQ.toLE
  letI : LT (ClosedIdealQuotient.Quotient J hJ) := orderQ.toLT
  letI : PartialOrder (ClosedIdealQuotient.Quotient J hJ) := orderQ
  letI : StarOrderedRing (ClosedIdealQuotient.Quotient J hJ) :=
    _root_.CStarAlgebra.spectralOrderedRing (ClosedIdealQuotient.Quotient J hJ)
  let q := ClosedIdealQuotient.mkStarAlgHom J hJ
  have hq : Function.Surjective q := ClosedIdealQuotient.mkStarAlgHom_surjective J hJ
  have hcompat : ∀ d : D, q (d : A) = 0 →
      (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d = 0 := by
    intro d hd
    exact hker d ((ClosedIdealQuotient.mkStarAlgHom_eq_zero_iff J hJ (d : A)).1 hd)
  obtain ⟨theta, htheta, htheta_pure, htheta_norm, hext⟩ :=
    exists_pure_state_extension_through_hom D q phi hphi hcompat
  obtain ⟨psi, hpsi, hpsi_pure, hpsi_norm, hpull⟩ :=
    exists_pure_state_pullback_of_surjective q hq theta htheta_pure
  have hann : ∀ a : A, a ∈ J → psi a = 0 := by
    intro a ha
    have hz : q a = 0 := (ClosedIdealQuotient.mkStarAlgHom_eq_zero_iff J hJ a).2 ha
    exact (hpull a).trans ((congrArg theta hz).trans (map_zero theta))
  refine ⟨psi, hpsi, hpsi_pure, fun d => (hpull d).trans (hext d), ?_⟩
  intro a ha
  exact gnsStarAlgHom_eq_zero_of_mem psi hpsi J hann ha

end SubalgebraExtension

end MathlibAnnex.Analysis.CStarAlgebra
