/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.EssentialProjection
import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.TypeI
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.SurjectiveRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.ClosedIdealQuotient
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.Factor
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeDecomposition

/-!
# Restricting a type III factor representation of a unitization

The essential projection of the canonical ideal action is central in the
same generated algebra. In a factor it is zero or one. A zero ideal action
would generate a commutative algebra, whose identity is a finite projection;
this contradicts the nonzero factor and type III hypotheses. Consequently
the actual restriction is both nonzero and nondegenerate.

The restriction is the existing inverse of `Unitization.starLift`. Composition
with a surjective nonunital star homomorphism preserves the represented
range after unitization. The final theorem uses the actual Banach quotient
map of an arbitrary norm-closed two-sided ideal. No separability, unitality
of the original algebra, or nondegeneracy of the restriction is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {Q : Type w} [NonUnitalCStarAlgebra Q]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- The essential projection is a central projection in the specified
factor, so the existing factor dichotomy applies to this actual operator. -/
theorem essentialProjection_eq_zero_or_eq_one_of_isFactor
    (pi : NonUnitalCStarRepresentation A H)
    (hfactor : VonNeumannAlgebra.IsFactor
      (VonNeumannAlgebra.generated pi.unitization.range)) :
    pi.essentialProjection = 0 ∨ pi.essentialProjection = 1 := by
  let M := VonNeumannAlgebra.generated pi.unitization.range
  let p : M.toStarSubalgebra := ⟨pi.essentialProjection,
    essentialProjection_mem_generated pi⟩
  have hp : IsStarProjection p := by
    have h := isStarProjection_essentialProjection pi
    exact ⟨Subtype.ext h.isIdempotentElem.eq, Subtype.ext h.isSelfAdjoint.star_eq⟩
  have hc : ∀ a : M.toStarSubalgebra, a * p = p * a := by
    intro a
    exact Subtype.ext (essentialProjection_commute pi a a.property)
  rcases hfactor.eq_zero_or_eq_one_of_central_projection hp hc with h | h
  · exact Or.inl (congrArg (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H)) h)
  · exact Or.inr (congrArg (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H)) h)

/-- A nonzero original-algebra action that generates a factor after
unitization must already act nondegenerately on the same Hilbert space. -/
theorem isNondegenerate_of_isFactor_of_isNonzero
    (pi : NonUnitalCStarRepresentation A H)
    (hfactor : VonNeumannAlgebra.IsFactor
      (VonNeumannAlgebra.generated pi.unitization.range)) (hnz : pi.IsNonzero) :
    pi.IsNondegenerate := by
  rcases essentialProjection_eq_zero_or_eq_one_of_isFactor pi hfactor with h | h
  · obtain ⟨a, ha⟩ := hnz
    exact (ha ((essentialProjection_eq_zero_iff pi).mp h a)).elim
  · exact (essentialProjection_eq_one_iff pi).mp h

/-- A vanishing canonical-ideal action would leave a commutative generated
algebra. Its finite identity contradicts a nonzero type III factor. -/
theorem isNonzero_of_isFactor_of_isTypeIII
    (pi : NonUnitalCStarRepresentation A H)
    (hfactor : VonNeumannAlgebra.IsFactor
      (VonNeumannAlgebra.generated pi.unitization.range))
    (hIII : (VonNeumannAlgebra.generated pi.unitization.range).IsTypeIII) :
    pi.IsNonzero := by
  classical
  by_contra hnz
  have hzero : ∀ a : A, pi a = 0 := by
    intro a
    by_contra ha
    exact hnz ⟨a, ha⟩
  let M := VonNeumannAlgebra.generated pi.unitization.range
  have hc (T : H →L[ℂ] H) : T ∈ Set.centralizer (Set.range pi.unitization) := by
    rw [centralizer_range_unitization]
    rintro _ ⟨a, rfl⟩
    simp only [hzero a, zero_mul, mul_zero]
  have hcomm : ∀ S T : M.toStarSubalgebra, S * T = T * S := by
    intro S T
    apply Subtype.ext
    exact ((VonNeumannAlgebra.mem_generated_iff pi.unitization.range
      (S : H →L[ℂ] H)).mp S.property (T : H →L[ℂ] H) (hc T)).symm
  have hfinite : IsFiniteProjection (1 : M.toStarSubalgebra) :=
    (VonNeumannAlgebra.isAbelianProjection_of_commutative M hcomm
      (IsStarProjection.one _)).isFiniteProjection
  have hzeroone : (1 : M.toStarSubalgebra) = 0 := hIII.2 1 hfinite (mul_one _)
  exact hfactor.1
    (congrArg (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H)) hzeroone)

/-- Both conclusions are derived from the factor and type III conditions;
nondegeneracy is not an additional premise. -/
theorem isNondegenerate_of_isFactor_of_isTypeIII
    (pi : NonUnitalCStarRepresentation A H)
    (hfactor : VonNeumannAlgebra.IsFactor
      (VonNeumannAlgebra.generated pi.unitization.range))
    (hIII : (VonNeumannAlgebra.generated pi.unitization.range).IsTypeIII) :
    pi.IsNondegenerate :=
  isNondegenerate_of_isFactor_of_isNonzero pi hfactor
    (isNonzero_of_isFactor_of_isTypeIII pi hfactor hIII)

/-- Unitization commutes with composition through the existing functorial
map on unitizations. -/
theorem unitization_comp (pi : NonUnitalCStarRepresentation Q H)
    (q : A →⋆ₙₐ[ℂ] Q) :
    unitization (pi.comp q) = pi.unitization.comp (Unitization.starMap q) := by
  apply Unitization.starAlgHom_ext
  apply DFunLike.ext
  intro a
  change unitization (pi.comp q) (Unitization.inr a) =
    pi.unitization (Unitization.starMap q (Unitization.inr a))
  simp only [Unitization.starMap_inr, unitization_inr, NonUnitalStarAlgHom.comp_apply]

/-- A surjective quotient map leaves the unitized represented range
unchanged. Surjectivity of its unitization is reused from Mathlib. -/
theorem unitization_range_comp_of_surjective
    (pi : NonUnitalCStarRepresentation Q H) (q : A →⋆ₙₐ[ℂ] Q)
    (hq : Function.Surjective q) :
    (unitization (pi.comp q)).range = pi.unitization.range := by
  rw [unitization_comp]
  apply SetLike.coe_injective
  exact (Unitization.starMap_surjective hq).range_comp pi.unitization

/-- Consequently the concrete generated von Neumann algebra is literally
the same subalgebra of the same bounded-operator algebra. -/
theorem generated_unitization_comp_of_surjective
    (pi : NonUnitalCStarRepresentation Q H) (q : A →⋆ₙₐ[ℂ] Q)
    (hq : Function.Surjective q) :
    VonNeumannAlgebra.generated (unitization (pi.comp q)).range =
      VonNeumannAlgebra.generated pi.unitization.range := by
  rw [unitization_range_comp_of_surjective pi q hq]

theorem isNondegenerate_comp_iff_of_surjective
    (pi : NonUnitalCStarRepresentation Q H) (q : A →⋆ₙₐ[ℂ] Q)
    (hq : Function.Surjective q) :
    IsNondegenerate (pi.comp q) ↔ pi.IsNondegenerate := by
  constructor
  · intro h x hx
    apply h x
    intro a
    exact hx (q a)
  · intro h x hx
    apply h x
    intro b
    obtain ⟨a, rfl⟩ := hq b
    exact hx a

/-- Restrict the actual unitized representation, using the inverse of
Mathlib's universal property. Type III and factor conditions force this
canonical ideal action to be nonzero. -/
theorem isNonzero_restriction_of_isTypeIII
    (rho : Representation (Unitization ℂ A) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hIII : (VonNeumannAlgebra.generated rho.range).IsTypeIII) :
    IsNonzero (Unitization.starLift.symm rho : NonUnitalCStarRepresentation A H) := by
  apply isNonzero_of_isFactor_of_isTypeIII
  · simpa only [unitization, Equiv.apply_symm_apply] using hfactor
  · simpa only [unitization, Equiv.apply_symm_apply] using hIII

/-- The same restriction acts nondegenerately on the original represented
Hilbert space. No essential-space replacement is made. -/
theorem isNondegenerate_restriction_of_isTypeIII
    (rho : Representation (Unitization ℂ A) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hIII : (VonNeumannAlgebra.generated rho.range).IsTypeIII) :
    IsNondegenerate (Unitization.starLift.symm rho : NonUnitalCStarRepresentation A H) := by
  apply isNondegenerate_of_isFactor_of_isTypeIII
  · simpa only [unitization, Equiv.apply_symm_apply] using hfactor
  · simpa only [unitization, Equiv.apply_symm_apply] using hIII

/-- Restriction followed by a surjective original-algebra quotient has
the proved nonzero and nondegenerate action, the same generated algebra,
and the exact commuting diagram on every original element. -/
theorem restriction_comp_spec (q : A →⋆ₙₐ[ℂ] Q) (hq : Function.Surjective q)
    (rho : Representation (Unitization ℂ Q) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hIII : (VonNeumannAlgebra.generated rho.range).IsTypeIII) :
    let pi : NonUnitalCStarRepresentation A H := (Unitization.starLift.symm rho).comp q
    pi.IsNonzero ∧ pi.IsNondegenerate ∧
      VonNeumannAlgebra.generated pi.unitization.range =
        VonNeumannAlgebra.generated rho.range ∧
      ∀ a : A, pi a = rho (Unitization.inr (q a)) := by
  dsimp only
  refine ⟨(isNonzero_comp_iff_of_surjective (Unitization.starLift.symm rho : NonUnitalCStarRepresentation Q H) q hq).mpr
      (isNonzero_restriction_of_isTypeIII rho hfactor hIII),
    (isNondegenerate_comp_iff_of_surjective (Unitization.starLift.symm rho : NonUnitalCStarRepresentation Q H) q hq).mpr
      (isNondegenerate_restriction_of_isTypeIII rho hfactor hIII), ?_, fun _ => rfl⟩
  simpa only [unitization, Equiv.apply_symm_apply] using
    generated_unitization_comp_of_surjective
      (Unitization.starLift.symm rho : NonUnitalCStarRepresentation Q H) q hq

/-- The previous diagram for the existing genuine Banach quotient by a
norm-closed two-sided ideal. The ideal may be arbitrary; all nonzero
information comes from the stated type III factor representation. -/
theorem restriction_mkHom_spec (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (rho : Representation (Unitization ℂ (ClosedIdealQuotient.Quotient J hJ)) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hIII : (VonNeumannAlgebra.generated rho.range).IsTypeIII) :
    let pi : NonUnitalCStarRepresentation A H :=
      (Unitization.starLift.symm rho).comp (ClosedIdealQuotient.mkHom J hJ)
    pi.IsNonzero ∧ pi.IsNondegenerate ∧
      VonNeumannAlgebra.generated pi.unitization.range =
        VonNeumannAlgebra.generated rho.range ∧
      ∀ a : A, pi a = rho (Unitization.inr (ClosedIdealQuotient.mkHom J hJ a)) :=
  restriction_comp_spec (ClosedIdealQuotient.mkHom J hJ)
    (ClosedIdealQuotient.mkHom_surjective J hJ) rho hfactor hIII

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {Q : Type w} [NonUnitalCStarAlgebra Q]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A type III factor representation of the unitization of an actual
surjective quotient obstructs type I of the literal original bidual.
Existence of that representation is a separate mathematical construction. -/
theorem not_isTypeIBidual_of_isTypeIII_quotient
    (q : A →⋆ₙₐ[ℂ] Q) (hq : Function.Surjective q)
    (rho : Representation (Unitization ℂ Q) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hIII : (VonNeumannAlgebra.generated rho.range).IsTypeIII) :
    ¬ IsTypeIBidual A := by
  let pi : NonUnitalCStarRepresentation A H := (Unitization.starLift.symm rho).comp q
  obtain ⟨hnz, hnd, hgen, _hdiag⟩ :=
    NonUnitalCStarRepresentation.restriction_comp_spec q hq rho hfactor hIII
  apply not_isTypeIBidual_of_isTypeIII_generated pi hnd hnz
  rw [hgen]
  exact hIII

end MathlibAnnex.Analysis.CStarAlgebra
