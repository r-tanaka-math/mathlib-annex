/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.Generated
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.ClosedIdealQuotient
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Basic
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorAlgebra

/-!
# Independent C-star predicates for the type I problem

The internal predicate quantifies over actual C-star quotients by norm-closed
two-sided ideals. The representation predicate tests actual pure-state GNS
images for containment of compact operators. Neither definition mentions the
other, a weak closure, a bidual, or a classification conclusion.

All positivity uses the canonical spectral order; no order instance is an
extra argument of these predicates. The zero algebra is included. A nonzero
abelian positive element means a positive element whose closed sandwich
algebra is commutative; nonzeroness is kept separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- Positivity and commutativity of the genuine norm-closed sandwich algebra. -/
def IsAbelianPositiveElement (a : A) : Prop :=
  0 ≤ a ∧ ∀ x ∈ hereditarySubalgebra a, ∀ y ∈ hereditarySubalgebra a, x * y = y * x

/-- Every proper closed two-sided ideal has a nonzero abelian positive element
in its actual C-star quotient. -/
def IsInternalTypeI (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)), J ≠ ⊤ →
    ∃ a : ClosedIdealQuotient.Quotient J hJ, a ≠ 0 ∧ IsAbelianPositiveElement a

/-- The small pure-GNS compact-containment condition. Transport to any separately
specified Hilbert universe is supplied by `IsGCR.compact_le_range`. -/
def IsGCR (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ phi : NonUnitalPureState A,
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS ≤
      NonUnitalStarAlgHom.range phi.gnsRepresentation

/-- There is no nonzero abelian positive element. This makes no assertion about
compact intersections of representations by definition. -/
def IsAntiliminal (A : Type u) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ a : A, IsAbelianPositiveElement a → a = 0

theorem IsAbelianPositiveElement.nonneg {a : A}
    (ha : IsAbelianPositiveElement a) : 0 ≤ a := ha.1

theorem IsAbelianPositiveElement.mul_comm {a x y : A}
    (ha : IsAbelianPositiveElement a) (hx : x ∈ hereditarySubalgebra a)
    (hy : y ∈ hereditarySubalgebra a) : x * y = y * x :=
  ha.2 x hx y hy

@[simp]
theorem isAbelianPositiveElement_zero : IsAbelianPositiveElement (0 : A) := by
  refine ⟨le_rfl, ?_⟩
  intro x hx y hy
  have hx0 : x = 0 := by simpa only [hereditarySubalgebra_zero, NonUnitalStarAlgebra.mem_bot] using hx
  simp [hx0]

/-- A positive element in an abelian hereditary algebra has a smaller abelian
hereditary algebra. This uses the proved inner-ideal property, not a generated
commutative one-element algebra. -/
theorem IsAbelianPositiveElement.of_mem {a b : A}
    (ha : IsAbelianPositiveElement a) (hb : 0 ≤ b)
    (hba : b ∈ hereditarySubalgebra a) : IsAbelianPositiveElement b := by
  refine ⟨hb, ?_⟩
  intro x hx y hy
  exact ha.mul_comm (hereditarySubalgebra_le_of_mem hba hx)
    (hereditarySubalgebra_le_of_mem hba hy)

theorem isAbelianPositiveElement_of_nonneg_of_commutative
    (hcomm : ∀ x y : A, x * y = y * x) {a : A} (ha : 0 ≤ a) :
    IsAbelianPositiveElement a :=
  ⟨ha, fun x _ y _ => hcomm x y⟩

theorem isAntiliminal_iff_not_exists :
    IsAntiliminal A ↔ ¬ ∃ a : A, a ≠ 0 ∧ IsAbelianPositiveElement a := by
  constructor
  · rintro h ⟨a, ha, hab⟩
    exact ha (h a hab)
  · intro h a ha
    by_contra hn
    exact h ⟨a, hn, ha⟩

/-- Failure of the internal condition produces precisely the nonzero
antiliminal quotient needed by the CAR-subquotient direction. -/
theorem not_isInternalTypeI_iff :
    ¬ IsInternalTypeI A ↔
      ∃ (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A)),
        J ≠ ⊤ ∧ IsAntiliminal (ClosedIdealQuotient.Quotient J hJ) := by
  classical
  constructor
  · intro h
    simp only [IsInternalTypeI, not_forall, not_imp] at h
    obtain ⟨J, hJ, hproper, hnone⟩ := h
    exact ⟨J, hJ, hproper, isAntiliminal_iff_not_exists.mpr hnone⟩
  · rintro ⟨J, hJ, hproper, hanti⟩ htype
    exact (isAntiliminal_iff_not_exists.mp hanti) (htype J hJ hproper)

theorem isInternalTypeI_of_subsingleton [Subsingleton A] : IsInternalTypeI A := by
  intro J hJ hproper
  exfalso
  apply hproper
  apply top_unique
  intro a _
  have ha : a = 0 := Subsingleton.elim a 0
  rw [ha]
  exact J.zero_mem

theorem isAntiliminal_of_subsingleton [Subsingleton A] : IsAntiliminal A := by
  intro a _
  exact Subsingleton.elim a 0

theorem isGCR_of_subsingleton [Subsingleton A] : IsGCR A := by
  intro phi
  obtain ⟨a, ha⟩ := phi.isIrreducible_gnsRepresentation.1
  exact False.elim (ha (by rw [Subsingleton.elim a 0, map_zero]))

end MathlibAnnex.Analysis.CStarAlgebra
