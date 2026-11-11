/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.Ideal.PrimitiveSeparation
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Atomic
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.KernelAlgebra

/-!
# C-star quotients by arbitrary norm-closed two-sided ideals

For each point outside the ideal, the existing primitive-separation theorem
supplies a pure state of the unitization whose restricted representation kills
the ideal and detects that point. Their set-indexed Hilbert sum has precisely
the prescribed kernel. The existing `HomKernelQuotient` then gives the genuine
Banach quotient, with its original quotient norm, multiplication and star.

The sum here is only a separating representation for one ideal. No universal
representation or bidual identification is asserted. The ideal may be the
whole algebra, and no separability or unit is required of the original algebra.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra ComplexOrder ENNReal lp
open MathlibAnnex.Analysis.InnerProductSpace

namespace MathlibAnnex.Analysis.CStarAlgebra.ClosedIdealQuotient

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

private def separatingState (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (i : {a : A // a ∉ J}) : StrongDual ℂ (Unitization ℂ A) :=
  (exists_pureState_unitization_annihilating_ideal J hJ i.1 i.2).choose

private theorem separatingState_spec (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) (i : {a : A // a ∉ J}) :
    separatingState J hJ i ∈ stateSpace (Unitization ℂ A) ∧
      IsPureState (Unitization ℂ A) (separatingState J hJ i) ∧
      (∀ z : Unitization ℂ A, z ∈ unitizationIdeal J hJ →
        separatingState J hJ i z = 0) ∧
      0 < (separatingState J hJ i
        (star (Unitization.inr i.1) * Unitization.inr i.1)).re :=
  (exists_pureState_unitization_annihilating_ideal J hJ i.1 i.2).choose_spec

private abbrev SeparatingSpace (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) (i : {a : A // a ∉ J}) :=
  (positiveLinearMapOfMemStateSpace (separatingState J hJ i)
    (separatingState_spec J hJ i).1).GNS

private def separatingRepresentationAt (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) (i : {a : A // a ∉ J}) :
    Representation (Unitization ℂ A) (SeparatingSpace J hJ i) :=
  (positiveLinearMapOfMemStateSpace (separatingState J hJ i)
    (separatingState_spec J hJ i).1).gnsStarAlgHom

private theorem separatingRepresentationAt_annihilates (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) (i : {a : A // a ∉ J})
    {a : A} (ha : a ∈ J) :
    separatingRepresentationAt J hJ i (Unitization.inr a) = 0 := by
  have hs := separatingState_spec J hJ i
  exact (pureState_restriction_separator J hJ i.1
    (separatingState J hJ i) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2).2.2 a ha

private theorem separatingRepresentationAt_detects (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) (i : {a : A // a ∉ J}) :
    separatingRepresentationAt J hJ i (Unitization.inr i.1) ≠ 0 := by
  have hs := separatingState_spec J hJ i
  exact (pureState_restriction_separator J hJ i.1
    (separatingState J hJ i) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2).2.1

/-- A concrete representation with exactly the specified closed ideal as kernel. -/
def representation (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    NonUnitalCStarRepresentation A
      (HilbertSum (fun i : {a : A // a ∉ J} => SeparatingSpace J hJ i)) :=
  (atomicRepresentation (separatingRepresentationAt J hJ)).toNonUnitalStarAlgHom.comp
    (Unitization.inrNonUnitalStarAlgHom ℂ A)

/-- Every nonzero quotient class is detected in its own summand. -/
theorem representation_eq_zero_iff (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) (a : A) :
    representation J hJ a = 0 ↔ a ∈ J := by
  classical
  constructor
  · intro hz
    by_contra ha
    let i : {a : A // a ∉ J} := ⟨a, ha⟩
    apply separatingRepresentationAt_detects J hJ i
    apply ContinuousLinearMap.ext
    intro x
    have hc := congrArg
      (fun T : HilbertSum (fun j : {a : A // a ∉ J} => SeparatingSpace J hJ j) →L[ℂ]
          HilbertSum (fun j : {a : A // a ∉ J} => SeparatingSpace J hJ j) =>
        (T (lp.single 2 i x)) i) hz
    simpa [representation] using hc
  · intro ha
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    change separatingRepresentationAt J hJ i (Unitization.inr a) (x i) = 0
    rw [separatingRepresentationAt_annihilates J hJ i ha]
    rfl

theorem ker_representation (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    TwoSidedIdeal.ker (representation J hJ) = J := by
  apply TwoSidedIdeal.ext
  intro a
  simpa only [TwoSidedIdeal.mem_ker] using representation_eq_zero_iff J hJ a

/-- The ordinary Banach quotient by the closed linear kernel, which has just
been proved to be exactly `J`. Its C-star structure is inherited from the
existing kernel-quotient construction, without changing its norm. -/
abbrev Quotient (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :=
  HomKernelQuotient (representation J hJ)

/-- The actual quotient homomorphism. -/
def mkHom (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    A →⋆ₙₐ[ℂ] Quotient J hJ :=
  HomKernelQuotient.mkHom (representation J hJ)

theorem mkHom_surjective (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    Function.Surjective (mkHom J hJ) :=
  HomKernelQuotient.mkHom_surjective (representation J hJ)

@[simp]
theorem mkHom_eq_zero_iff (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (a : A) : mkHom J hJ a = 0 ↔ a ∈ J := by
  exact (HomKernelQuotient.mkHom_eq_zero_iff (representation J hJ) a).trans
    (representation_eq_zero_iff J hJ a)

theorem ker_mkHom (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)) :
    TwoSidedIdeal.ker (mkHom J hJ) = J := by
  apply TwoSidedIdeal.ext
  intro a
  simpa only [TwoSidedIdeal.mem_ker] using mkHom_eq_zero_iff J hJ a

theorem mkHom_eq_mkHom_iff (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (a b : A) : mkHom J hJ a = mkHom J hJ b ↔ a - b ∈ J := by
  rw [← sub_eq_zero, ← map_sub, mkHom_eq_zero_iff]

/-- Properness alone supplies a nonzero quotient class. -/
theorem nontrivial_quotient (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (hproper : J ≠ ⊤) : Nontrivial (Quotient J hJ) := by
  classical
  have hex : ∃ a : A, a ∉ J := by
    by_contra! hall
    apply hproper
    apply top_unique
    intro a _
    exact hall a
  obtain ⟨a, ha⟩ := hex
  exact nontrivial_of_ne (mkHom J hJ a) 0
    (fun hz => ha ((mkHom_eq_zero_iff J hJ a).1 hz))

/-- The zero quotient is allowed and has no artificial nonzero witness. -/
theorem subsingleton_quotient_of_eq_top (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) (hJtop : J = ⊤) :
    Subsingleton (Quotient J hJ) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := mkHom_surjective J hJ x
  obtain ⟨b, rfl⟩ := mkHom_surjective J hJ y
  apply (mkHom_eq_mkHom_iff J hJ a b).2
  rw [hJtop]
  trivial

/-- Contractivity refers to the original Banach quotient norm. -/
theorem norm_mkHom_le (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (a : A) : ‖mkHom J hJ a‖ ≤ ‖a‖ :=
  HomKernelQuotient.norm_mk_le (representation J hJ) a

section Lift

variable {B : Type v} [NonUnitalCStarAlgebra B]

private def representative (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (x : Quotient J hJ) : A := (mkHom_surjective J hJ x).choose

private theorem mkHom_representative (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) (x : Quotient J hJ) :
    mkHom J hJ (representative J hJ x) = x :=
  (mkHom_surjective J hJ x).choose_spec

private theorem map_eq_of_mkHom_eq (J : TwoSidedIdeal A)
    (hJ : IsClosed (J : Set A)) (q : A →⋆ₙₐ[ℂ] B)
    (hq : ∀ a : A, a ∈ J → q a = 0) {a b : A}
    (hab : mkHom J hJ a = mkHom J hJ b) : q a = q b := by
  have hz := hq (a - b) ((mkHom_eq_mkHom_iff J hJ a b).1 hab)
  simpa only [map_sub, sub_eq_zero] using hz

/-- The descended homomorphism for any homomorphism annihilating `J`.
The codomain may live in an independent universe. -/
def liftHom (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (q : A →⋆ₙₐ[ℂ] B) (hq : ∀ a : A, a ∈ J → q a = 0) :
    Quotient J hJ →⋆ₙₐ[ℂ] B where
  toFun x := q (representative J hJ x)
  map_zero' := by
    have h := map_eq_of_mkHom_eq J hJ q hq
      (a := representative J hJ 0) (b := 0) (by
        rw [mkHom_representative, map_zero])
    simpa only [map_zero] using h
  map_add' x y := by
    calc
      q (representative J hJ (x + y)) =
          q (representative J hJ x + representative J hJ y) :=
        map_eq_of_mkHom_eq J hJ q hq (by
          rw [mkHom_representative, map_add, mkHom_representative,
            mkHom_representative])
      _ = _ := map_add q _ _
  map_mul' x y := by
    calc
      q (representative J hJ (x * y)) =
          q (representative J hJ x * representative J hJ y) :=
        map_eq_of_mkHom_eq J hJ q hq (by
          rw [mkHom_representative, map_mul, mkHom_representative,
            mkHom_representative])
      _ = _ := map_mul q _ _
  map_smul' c x := by
    calc
      q (representative J hJ (c • x)) = q (c • representative J hJ x) :=
        map_eq_of_mkHom_eq J hJ q hq (by
          rw [mkHom_representative, map_smul, mkHom_representative])
      _ = _ := map_smul q _ _
  map_star' x := by
    calc
      q (representative J hJ (star x)) = q (star (representative J hJ x)) :=
        map_eq_of_mkHom_eq J hJ q hq (by
          rw [mkHom_representative, map_star, mkHom_representative])
      _ = _ := map_star q _

@[simp]
theorem liftHom_mkHom (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (q : A →⋆ₙₐ[ℂ] B) (hq : ∀ a : A, a ∈ J → q a = 0) (a : A) :
    liftHom J hJ q hq (mkHom J hJ a) = q a := by
  exact map_eq_of_mkHom_eq J hJ q hq
    (mkHom_representative J hJ (mkHom J hJ a))

theorem liftHom_comp_mkHom (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (q : A →⋆ₙₐ[ℂ] B) (hq : ∀ a : A, a ∈ J → q a = 0) :
    (liftHom J hJ q hq).comp (mkHom J hJ) = q := by
  ext a
  exact liftHom_mkHom J hJ q hq a

theorem liftHom_unique (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (q : A →⋆ₙₐ[ℂ] B) (hq : ∀ a : A, a ∈ J → q a = 0)
    (f : Quotient J hJ →⋆ₙₐ[ℂ] B) (hf : f.comp (mkHom J hJ) = q) :
    f = liftHom J hJ q hq := by
  ext x
  obtain ⟨a, rfl⟩ := mkHom_surjective J hJ x
  rw [liftHom_mkHom]
  exact congrArg (fun g : A →⋆ₙₐ[ℂ] B => g a) hf

theorem liftHom_surjective (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (q : A →⋆ₙₐ[ℂ] B) (hq : ∀ a : A, a ∈ J → q a = 0)
    (hsurj : Function.Surjective q) : Function.Surjective (liftHom J hJ q hq) := by
  intro b
  obtain ⟨a, rfl⟩ := hsurj b
  exact ⟨mkHom J hJ a, liftHom_mkHom J hJ q hq a⟩

theorem liftHom_injective (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (q : A →⋆ₙₐ[ℂ] B) (hq : ∀ a : A, a ∈ J → q a = 0)
    (hreflect : ∀ a : A, q a = 0 → a ∈ J) :
    Function.Injective (liftHom J hJ q hq) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := mkHom_surjective J hJ x
  obtain ⟨b, rfl⟩ := mkHom_surjective J hJ y
  apply (mkHom_eq_mkHom_iff J hJ a b).2
  apply hreflect (a - b)
  rw [map_sub, sub_eq_zero]
  simpa only [liftHom_mkHom] using hxy

/-- Any surjective C-star homomorphism with kernel `J` identifies this actual
quotient with its codomain. The equivalence preserves all algebra operations. -/
def equivOfSurjective (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (q : A →⋆ₙₐ[ℂ] B) (hsurj : Function.Surjective q)
    (hker : ∀ a : A, q a = 0 ↔ a ∈ J) : Quotient J hJ ≃⋆ₐ[ℂ] B := by
  let f := liftHom J hJ q (fun a ha => (hker a).2 ha)
  have hf : Function.Bijective f :=
    ⟨liftHom_injective J hJ q _ (fun a ha => (hker a).1 ha),
      liftHom_surjective J hJ q _ hsurj⟩
  exact
    { Equiv.ofBijective f hf with
      map_add' := map_add f
      map_mul' := map_mul f
      map_smul' := map_smul f
      map_star' := map_star f }

@[simp]
theorem equivOfSurjective_mkHom (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (q : A →⋆ₙₐ[ℂ] B) (hsurj : Function.Surjective q)
    (hker : ∀ a : A, q a = 0 ↔ a ∈ J) (a : A) :
    equivOfSurjective J hJ q hsurj hker (mkHom J hJ a) = q a :=
  liftHom_mkHom J hJ q (fun a ha => (hker a).2 ha) a

end Lift

end MathlibAnnex.Analysis.CStarAlgebra.ClosedIdealQuotient
