/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorIdeal
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Algebra.Star.NonUnitalSubalgebra
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.Representation

/-!
# The concrete C-star algebra of compact Hilbert-space operators

The carrier is Mathlib's `IsCompactOperator`; the norm is the ambient operator norm.
Adjoint stability follows from finite-rank norm approximation, not from a second
compactness predicate. Only the C-star algebra and representation packaging uses
complex scalars; adjoint stability and the star subalgebra are stated over RCLike.
No classification of irreducible representations or singleton spectrum is asserted.
-/

set_option autoImplicit false
noncomputable section
open Set InnerProductSpace

namespace IsCompactOperator

variable {𝕜 H K : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- Adjoint stability of compact operators between arbitrary Hilbert spaces. -/
theorem adjoint {T : H →L[𝕜] K} (hT : IsCompactOperator T) :
    IsCompactOperator (ContinuousLinearMap.adjoint T) := by
  classical
  have hclosed : IsClosed {A : H →L[𝕜] K |
      IsCompactOperator (ContinuousLinearMap.adjoint A)} :=
    (show IsClosed {S : K →L[𝕜] H | IsCompactOperator S} from
      isClosed_setOf_isCompactOperator).preimage ContinuousLinearMap.adjoint.continuous
  apply closure_minimal (t := {A : H →L[𝕜] K |
    IsCompactOperator (ContinuousLinearMap.adjoint A)}) _ hclosed
      hT.mem_closure_setOf_finiteDimensional_range
  intro A hA
  change FiniteDimensional 𝕜 A.toLinearMap.range at hA
  letI : FiniteDimensional 𝕜 A.toLinearMap.range := hA
  obtain ⟨n, u, v, hsum⟩ := A.exists_sum_rankOne_eq_of_finiteDimensional_range
  have hc : (∑ i : Fin n, rankOne 𝕜 (v i) (u i)) ∈
      compactOperator (RingHom.id 𝕜) K H :=
    sum_mem fun i _ => isCompactOperator_rankOne (v i) (u i)
  change IsCompactOperator ((∑ i : Fin n, rankOne 𝕜 (v i) (u i)) : K →L[𝕜] H) at hc
  change IsCompactOperator (ContinuousLinearMap.adjoint A)
  simpa only [← hsum, map_sum, adjoint_rankOne] using hc

/-- For endomorphisms, adjoint stability is precisely star stability. -/
theorem star {T : H →L[𝕜] H} (hT : IsCompactOperator T) :
    IsCompactOperator (star T : H →L[𝕜] H) := by
  simpa only [ContinuousLinearMap.star_eq_adjoint] using hT.adjoint

end IsCompactOperator

namespace ContinuousLinearMap

variable {𝕜 H K : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- Compactness is reflected as well as preserved by taking the adjoint. -/
theorem isCompactOperator_adjoint_iff (T : H →L[𝕜] K) :
    IsCompactOperator T.adjoint ↔ IsCompactOperator T :=
  ⟨fun h => by simpa only [adjoint_adjoint] using h.adjoint, fun h => h.adjoint⟩

/-- The actual compact operators, with the star subalgebra structure. -/
def compactOperatorStarSubalgebra (𝕜 H : Type*) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] :
    NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H) where
  carrier := {T | IsCompactOperator T}
  zero_mem' := isCompactOperator_zero
  add_mem' := fun hT hS => hT.add hS
  mul_mem' := fun hT hS => hT.comp_clm _
  smul_mem' := fun c T hT => hT.smul c
  star_mem' := fun hT => hT.star

@[simp]
theorem mem_compactOperatorStarSubalgebra (T : H →L[𝕜] H) :
    T ∈ compactOperatorStarSubalgebra 𝕜 H ↔ IsCompactOperator T := Iff.rfl

/-- No carrier is changed when passing from the ideal to the star subalgebra. -/
theorem coe_compactOperatorStarSubalgebra :
    (compactOperatorStarSubalgebra 𝕜 H : Set (H →L[𝕜] H)) =
      (compactOperatorIdeal 𝕜 H : Set (H →L[𝕜] H)) := by
  ext T
  exact (mem_compactOperatorIdeal T).symm

theorem isClosed_compactOperatorStarSubalgebra :
    IsClosed (compactOperatorStarSubalgebra 𝕜 H : Set (H →L[𝕜] H)) :=
  isClosed_setOf_isCompactOperator

/-- The inherited subtype norm is literally the ambient operator norm. -/
@[simp]
theorem norm_coe_compactOperatorStarSubalgebra
    (T : compactOperatorStarSubalgebra 𝕜 H) : ‖(T : H →L[𝕜] H)‖ = ‖T‖ := rfl

/-- Compact operators form a complete subspace, including on the zero Hilbert space. -/
instance compactOperatorStarSubalgebraCompleteSpace :
    CompleteSpace (compactOperatorStarSubalgebra 𝕜 H) :=
  isClosed_compactOperatorStarSubalgebra.completeSpace_coe

/-- In finite dimension the concrete compact star subalgebra is the whole algebra. -/
theorem compactOperatorStarSubalgebra_eq_top [FiniteDimensional 𝕜 H] :
    compactOperatorStarSubalgebra 𝕜 H = ⊤ := by
  ext T
  change IsCompactOperator T ↔ True
  exact ⟨fun _ => trivial, fun _ => T.isCompactOperator_of_finiteDimensional_range⟩

/-- On the zero space its carrier is the singleton zero operator. -/
theorem coe_compactOperatorStarSubalgebra_of_subsingleton [Subsingleton H] :
    (compactOperatorStarSubalgebra 𝕜 H : Set (H →L[𝕜] H)) = {0} := by
  rw [coe_compactOperatorStarSubalgebra,
    compactOperatorIdeal_eq_bot_of_subsingleton, TwoSidedIdeal.coe_bot]

end ContinuousLinearMap

namespace MathlibAnnex.Analysis.CStarAlgebra

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- C-star structure on the existing compact carrier, without a new norm. -/
instance compactOperatorCStarAlgebra :
    NonUnitalCStarAlgebra (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra _
    (h_closed := ContinuousLinearMap.isClosed_compactOperatorStarSubalgebra)

/-- Inclusion of the actual compact operators, not an abstractly transported action. -/
def compactOperatorRepresentation :
    NonUnitalCStarRepresentation (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) H :=
  NonUnitalStarSubalgebraClass.subtype (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)

@[simp]
theorem compactOperatorRepresentation_apply
    (T : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) (x : H) :
    compactOperatorRepresentation H T x = (T : H →L[ℂ] H) x := rfl

/-- Faithfulness is just the injectivity of the concrete subtype inclusion. -/
theorem compactOperatorRepresentation_injective :
    Function.Injective (compactOperatorRepresentation H) := Subtype.val_injective

/-- Nonzero compact action is equivalent to the Hilbert space being nonzero. -/
theorem isNonzero_compactOperatorRepresentation_iff :
    (compactOperatorRepresentation H).IsNonzero ↔ Nontrivial H := by
  constructor
  · exact NonUnitalCStarRepresentation.nontrivial_of_isNonzero _
  · intro hn
    letI := hn
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    refine ⟨⟨rankOne ℂ x x, isCompactOperator_rankOne x x⟩, ?_⟩
    exact rankOne_ne_zero (𝕜 := ℂ) hx hx

/-- All rank-one operators in the carrier force every nonzero reducing space to be full. -/
theorem isIrreducible_compactOperatorRepresentation [Nontrivial H] :
    (compactOperatorRepresentation H).IsIrreducible := by
  classical
  refine ⟨(isNonzero_compactOperatorRepresentation_iff H).2 inferInstance, ?_⟩
  intro L hL
  by_cases hbot : L = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hx, hx0⟩ : ∃ x : H, x ∈ L ∧ x ≠ 0 := by
    by_contra! h
    exact hbot ((Submodule.eq_bot_iff L).mpr h)
  have hc : inner ℂ x x ≠ 0 := by simpa only [ne_eq, inner_self_eq_zero] using hx0
  apply top_unique
  intro y _
  let a : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H :=
    ⟨rankOne ℂ ((inner ℂ x x)⁻¹ • y) x,
      isCompactOperator_rankOne ((inner ℂ x x)⁻¹ • y) x⟩
  have hm := (hL.2 a x hx).1
  simpa only [compactOperatorRepresentation_apply, a, rankOne_apply, smul_smul,
    mul_inv_cancel₀ hc, one_smul] using hm

/-- The zero case is excluded from irreducibility by the existing definition, not by convention. -/
theorem isIrreducible_compactOperatorRepresentation_iff :
    (compactOperatorRepresentation H).IsIrreducible ↔ Nontrivial H := by
  constructor
  · intro h
    exact (isNonzero_compactOperatorRepresentation_iff H).1 h.1
  · intro h
    letI := h
    exact isIrreducible_compactOperatorRepresentation H

end MathlibAnnex.Analysis.CStarAlgebra
