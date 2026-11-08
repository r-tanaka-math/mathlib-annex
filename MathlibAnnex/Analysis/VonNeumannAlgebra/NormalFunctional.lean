import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional
import MathlibAnnex.Analysis.VonNeumannAlgebra.Generated
import MathlibAnnex.Analysis.VonNeumannAlgebra.MonotoneConvergence

/-!
# Normal positive functionals and monotone vector coefficients

Normality is preservation of least upper bounds of arbitrary nonempty,
upwards-directed, order-bounded sets of positive elements. The order is the
inherited Loewner order. The functional is defined on the algebra itself.

The operator results below construct upper bounds before proving the
least-upper-bound identity for vector coefficients. No countability
assumption is made on the index set or the Hilbert space.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped CStarAlgebra ComplexOrder InnerProduct

universe u v

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A positive functional is normal if it preserves bounded directed suprema
of positive elements. Complex values are compared through their real parts.
Monotone completeness of the algebra is a separate existence theorem. -/
def IsNormalPositiveFunctional (M : VonNeumannAlgebra H)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) : Prop :=
  (∀ a, 0 ≤ a → 0 ≤ φ a) ∧
    ∀ (s : Set M.toStarSubalgebra), s.Nonempty → DirectedOn (· ≤ ·) s →
      (∀ a ∈ s, 0 ≤ a) → BddAbove s →
      ∀ a, IsLUB s a → IsLUB ((fun b ↦ (φ b).re) '' s) (φ a).re

end VonNeumannAlgebra

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A monotone strongly convergent operator net has the expected supremum
after evaluation by any vector coefficient. Positivity of individual terms
is unnecessary for this implication. -/
theorem isLUB_re_inner_of_monotone_of_stronglyConverges
    {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {f : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hmono : Monotone f) (hlim : StronglyConverges f atTop T) (ξ : H) :
    IsLUB (Set.range (fun i ↦ (inner ℂ ξ (f i ξ)).re)) (inner ℂ ξ (T ξ)).re := by
  have hscalar : Monotone (fun i ↦ (inner ℂ ξ (f i ξ)).re) := by
    intro i j hij
    have h := (nonneg_iff_isPositive.mp (sub_nonneg.mpr (hmono hij))).re_inner_nonneg_right ξ
    change 0 ≤ (inner ℂ ξ ((f j - f i) ξ)).re at h
    simpa only [sub_apply, inner_sub_right, Complex.sub_re, sub_nonneg] using h
  exact isLUB_of_tendsto_atTop hscalar <|
    Complex.continuous_re.continuousAt.tendsto.comp (tendsto_const_nhds.inner (hlim ξ))

/-- An arbitrary directed positive order-bounded set in `B(H)` has an
ambient least upper bound, approached strongly by its inclusion net. -/
theorem exists_isLUB_stronglyConverges_of_directedOn
    (s : Set (H →L[ℂ] H)) (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ a ∈ s, 0 ≤ a) (hbdd : BddAbove s) :
    ∃ T : H →L[ℂ] H, 0 ≤ T ∧ IsLUB s T ∧
      StronglyConverges (fun a : s ↦ (a : H →L[ℂ] H)) atTop T := by
  letI : Nonempty s := hne.to_subtype
  letI : IsDirected s (· ≤ ·) := hdir.isDirectedOrder
  have hrange : Set.range (fun a : s ↦ (a : H →L[ℂ] H)) = s := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      exact b.property
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨T, hTpos, hTlub, hTlim⟩ :=
    exists_isLUB_stronglyConverges_of_monotone_of_bddAbove
      (fun a : s ↦ (a : H →L[ℂ] H)) (fun _ _ h ↦ h) (fun a ↦ hpos a a.property)
      (by simpa only [hrange] using hbdd)
  exact ⟨T, hTpos, hrange ▸ hTlub, hTlim⟩

end ContinuousLinearMap

namespace VonNeumannAlgebra

open MathlibAnnex.Analysis.CStarAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Monotone completeness for arbitrary directed positive sets. The witness
is simultaneously their ambient strong operator limit. -/
theorem exists_isLUB_stronglyConverges (M : VonNeumannAlgebra H)
    (s : Set M.toStarSubalgebra) (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ a ∈ s, 0 ≤ a) (hbdd : BddAbove s) :
    ∃ T : M.toStarSubalgebra, 0 ≤ T ∧ IsLUB s T ∧
      ContinuousLinearMap.StronglyConverges
        (fun a : s ↦ ((a : M.toStarSubalgebra) : H →L[ℂ] H)) atTop (T : H →L[ℂ] H) := by
  letI : Nonempty s := hne.to_subtype
  letI : IsDirected s (· ≤ ·) := hdir.isDirectedOrder
  let f : s → H →L[ℂ] H := fun a ↦ ((a : M.toStarSubalgebra) : H →L[ℂ] H)
  have hmono : Monotone f := fun _ _ h ↦ h
  have hfpos : ∀ a, 0 ≤ f a := fun a ↦ hpos a a.property
  obtain ⟨B, hB⟩ := hbdd
  have hfbounded : BddAbove (Set.range f) := by
    refine ⟨(B : H →L[ℂ] H), ?_⟩
    rintro _ ⟨a, rfl⟩
    exact hB a.property
  obtain ⟨T, hTpos, hTlub, hTlim⟩ :=
    ContinuousLinearMap.exists_isLUB_stronglyConverges_of_monotone_of_bddAbove
      f hmono hfpos hfbounded
  have hTM : T ∈ M := M.mem_of_stronglyConverges (fun a : s ↦ a.val.property) hTlim
  refine ⟨⟨T, hTM⟩, hTpos, ?_, hTlim⟩
  constructor
  · intro a ha
    exact hTlub.1 ⟨⟨a, ha⟩, rfl⟩
  · intro B hB
    apply hTlub.2
    rintro _ ⟨a, rfl⟩
    exact hB a.property

/-- The restriction of the existing ambient vector functional is normal.
The proof constructs the directed supremum before using its uniqueness;
it does not rely on a vacuous conditional preservation property. -/
private theorem isNormalPositiveFunctional_restrict_vectorFunctional
    (M : VonNeumannAlgebra H) (ξ : H) :
    IsNormalPositiveFunctional M
      ((Representation.vectorFunctional (StarAlgHom.id ℂ (H →L[ℂ] H)) ξ).comp
        M.toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL) := by
  constructor
  · intro a ha
    exact Representation.vectorFunctional_nonnegative
      (StarAlgHom.id ℂ (H →L[ℂ] H)) ξ ha
  · intro s hne hdir hpos hbdd T hT
    letI : Nonempty s := hne.to_subtype
    letI : IsDirected s (· ≤ ·) := hdir.isDirectedOrder
    obtain ⟨U, hUpos, hUlub, hUlim⟩ :=
      M.exists_isLUB_stronglyConverges s hne hdir hpos hbdd
    have hUT : U = T := hUlub.unique hT
    subst U
    have hscalar := ContinuousLinearMap.isLUB_re_inner_of_monotone_of_stronglyConverges
      (show Monotone (fun a : s ↦ ((a : M.toStarSubalgebra) : H →L[ℂ] H)) from
        fun _ _ h ↦ h) hUlim ξ
    change IsLUB ((fun a : M.toStarSubalgebra ↦
      (inner ℂ ξ ((a : H →L[ℂ] H) ξ)).re) '' s)
      (inner ℂ ξ ((T : H →L[ℂ] H) ξ)).re
    convert hscalar using 1
    ext c
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, rfl⟩

/-- The existing vector-functional provider on the algebra subtype is
normal. Norm closedness supplies its standard C⋆-algebra structure; strong
closedness supplies the directed supremum used in the proof. -/
theorem isNormalPositiveFunctional_vectorFunctional (M : VonNeumannAlgebra H)
    [IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H))] (ξ : H) :
    IsNormalPositiveFunctional M
      (Representation.vectorFunctional M.toStarSubalgebra.subtype ξ) := by
  have h := isNormalPositiveFunctional_restrict_vectorFunctional M ξ
  have heq : Representation.vectorFunctional M.toStarSubalgebra.subtype ξ =
      (Representation.vectorFunctional (StarAlgHom.id ℂ (H →L[ℂ] H)) ξ).comp
        M.toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL := by
    ext a
    rfl
  rw [heq]
  exact h

end VonNeumannAlgebra
