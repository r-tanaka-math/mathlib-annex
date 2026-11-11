/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.AbelianElement
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.GCRPermanence
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.ImageRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactIntersection

/-!
# From internal type I to actual irreducible compact containment

The argument takes an abelian positive element in the genuine quotient by the
representation kernel. The descended representation is proved faithful and
irreducible. Its abelian element is compact by exact interpolation; a nonzero
compact in the original closed irreducible image then supplies every compact.

No abelian element is asserted to lift to an abelian element of the original
algebra. No bidual or von Neumann type-I equivalence enters this implication.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- An actual nonzero compact image is obtained from an abelian element of the
kernel quotient, even if no abelian lift exists in the source algebra. -/
theorem IsInternalTypeI.exists_nonzero_compact_image (hA : IsInternalTypeI A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    ∃ a : A, pi a ≠ 0 ∧ IsCompactOperator (pi a) := by
  let J : TwoSidedIdeal A := TwoSidedIdeal.ker pi
  have hJ : IsClosed (J : Set A) := by
    have hset : (J : Set A) = {a : A | pi a = 0} := by
      ext a
      exact TwoSidedIdeal.mem_ker pi
    rw [hset]
    exact isClosed_eq (map_continuous pi) continuous_const
  have hproper : J ≠ ⊤ := by
    intro htop
    obtain ⟨a, ha⟩ := hpi.1
    apply ha
    have haJ : a ∈ J := by rw [htop]; trivial
    exact (TwoSidedIdeal.mem_ker pi).1 haJ
  let q := ClosedIdealQuotient.mkHom J hJ
  have hq : Function.Surjective q := ClosedIdealQuotient.mkHom_surjective J hJ
  have hvan : ∀ a : A, a ∈ J → pi a = 0 :=
    fun _ ha => (TwoSidedIdeal.mem_ker pi).1 ha
  let rho : NonUnitalCStarRepresentation (ClosedIdealQuotient.Quotient J hJ) H :=
    ClosedIdealQuotient.liftHom J hJ pi hvan
  have hcomp : rho.comp q = pi := ClosedIdealQuotient.liftHom_comp_mkHom J hJ pi hvan
  have hrho : rho.IsIrreducible := by
    apply (NonUnitalCStarRepresentation.isIrreducible_comp_iff_of_surjective
      rho q hq).1
    rw [hcomp]
    exact hpi
  have hinj : Function.Injective rho :=
    ClosedIdealQuotient.liftHom_injective J hJ pi hvan
      (fun _ ha => (TwoSidedIdeal.mem_ker pi).2 ha)
  obtain ⟨b, hb, habel⟩ := hA J hJ hproper
  have hnonzero : rho b ≠ 0 := by
    intro hz
    apply hb
    apply hinj
    simpa only [map_zero] using hz
  have hcompact : IsCompactOperator (rho b) := habel.isCompactOperator rho hrho
  obtain ⟨a, ha⟩ := hq b
  have hvalue : pi a = rho b := by
    have hv := ClosedIdealQuotient.liftHom_mkHom J hJ pi hvan a
    change rho (q a) = pi a at hv
    rw [ha] at hv
    exact hv.symm
  refine ⟨a, ?_, ?_⟩
  · simpa only [hvalue] using hnonzero
  · simpa only [hvalue] using hcompact

/-- Internal type I implies compact containment for every independently
specified Hilbert universe, for arbitrary nonunital C-star algebras. -/
theorem IsInternalTypeI.compact_le_range (hA : IsInternalTypeI A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤
      NonUnitalStarAlgHom.range pi := by
  obtain ⟨a, ha, hcompact⟩ := hA.exists_nonzero_compact_image pi hpi
  letI := HomKernelQuotient.imageCStarAlgebra pi
  exact compactOperatorStarSubalgebra_le_of_exists_nonzero_compact
    (NonUnitalStarAlgHom.range pi) (HomKernelQuotient.isClosed_image pi)
    ((NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff pi).2 hpi)
    ⟨pi a, (NonUnitalStarAlgHom.mem_range pi).2 ⟨a, rfl⟩, hcompact, ha⟩

/-- The pure-GNS specialization of the preceding arbitrary-universe theorem. -/
theorem IsInternalTypeI.isGCR (hA : IsInternalTypeI A) : IsGCR A := by
  intro phi
  exact hA.compact_le_range phi.gnsRepresentation phi.isIrreducible_gnsRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
