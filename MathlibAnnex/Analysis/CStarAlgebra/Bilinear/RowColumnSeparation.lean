import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.FiniteSequenceBridge
import MathlibAnnex.Analysis.CStarAlgebra.State.Extension

/-!
# Row/column sequence estimates and state separation

This file formalizes the positive-functional selection step in Haagerup's
finite sequence argument.  Its only analytic premise is a state-free
row/column norm inequality.  Four norm-attaining states turn that inequality
into `HasFiniteSummedAdditiveEstimate`, after which the phase, weight,
minimax, compactness, and rescaling modules apply.
-/

set_option autoImplicit false

open Finset Set
open scoped ComplexOrder

namespace MathlibAnnex.CStarBilinear

open MathlibAnnex.Analysis.CStarAlgebra
open StarAlgebra elemental

universe uA uD

noncomputable section

variable {A : Type uA} [CStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
variable {D : Type uD} [CStarAlgebra D]
  [PartialOrder D] [StarOrderedRing D]

/-- A positive element has a norm-attaining state.  The construction uses a
character of the singly generated commutative C-star subalgebra at the top
spectral value, followed by norm-preserving state extension. -/
theorem exists_weakState_apply_eq_norm_of_nonneg [Nontrivial A]
    (a : A) (ha : 0 ≤ a) :
    ∃ phi ∈ weakStateSpace A, phi a = (‖a‖ : ℂ) := by
  letI : IsStarNormal a := ha.isSelfAdjoint.isStarNormal
  let lam : spectrum ℂ a :=
    ⟨(‖a‖ : ℂ), CStarAlgebra.norm_mem_spectrum_of_nonneg ha⟩
  let chi : WeakDual.characterSpace ℂ (elemental ℂ a) :=
    (characterSpaceHomeo a).symm lam
  letI : IsClosed ((elemental ℂ a : StarSubalgebra ℂ A) : Set A) :=
    StarAlgebra.elemental.isClosed ℂ a
  obtain ⟨phi, hphi, hext⟩ := exists_state_extension (elemental ℂ a) chi
  refine ⟨StrongDual.toWeakDual phi, hphi, ?_⟩
  have hchi : chi ⟨a, self_mem ℂ a⟩ = (‖a‖ : ℂ) := by
    have hhomeo : characterSpaceToSpectrum a chi = lam :=
      (characterSpaceHomeo a).apply_symm_apply lam
    exact congrArg Subtype.val hhomeo
  exact (hext ⟨a, self_mem ℂ a⟩).trans hchi

/-- The positive column square sum. -/
def starMulSum {ι : Type*} [Fintype ι] (x : ι → A) : A :=
  ∑ i, star (x i) * x i

/-- The positive row square sum. -/
def mulStarSum {ι : Type*} [Fintype ι] (x : ι → A) : A :=
  ∑ i, x i * star (x i)

theorem starMulSum_nonneg {ι : Type*} [Fintype ι] (x : ι → A) :
    0 ≤ starMulSum x := by
  exact sum_nonneg fun i _ ↦ star_mul_self_nonneg (x i)

theorem mulStarSum_nonneg {ι : Type*} [Fintype ι] (x : ι → A) :
    0 ≤ mulStarSum x := by
  apply sum_nonneg
  intro i _
  simpa only [star_star] using star_mul_self_nonneg (star (x i))

/-- The state-free analytic inequality at the remaining supplier boundary.
It is the row/column norm hypothesis used by Haagerup's finite sequence
separation lemma. -/
def HasFiniteRowColumnEstimate
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) : Prop :=
  ∀ {ι : Type (max uA uD)} [Fintype ι] [Nonempty ι]
    (x : ι → A) (y : ι → D),
      ‖∑ i, B (x i) (y i)‖ ≤
        (C / 2) *
          (‖starMulSum x‖ + ‖mulStarSum x‖ +
            ‖starMulSum y‖ + ‖mulStarSum y‖)

/-- The zero bilinear form satisfies the analytic supplier with constant
zero.  This is separate from the zero-algebra branches below: on nontrivial
algebras it can still be passed through the common-state selection API. -/
theorem hasFiniteRowColumnEstimate_zero :
    HasFiniteRowColumnEstimate
      (0 : A →L[ℂ] D →L[ℂ] ℂ) 0 := by
  intro ι _ _ x y
  simp

private theorem sum_leftSquare_eq
    (z : StateControl A D)
    {ι : Type*} [Fintype ι] (x : ι → A)
    (hp : z.1.1 (starMulSum x) = (‖starMulSum x‖ : ℂ))
    (hq : z.1.2 (mulStarSum x) = (‖mulStarSum x‖ : ℂ)) :
    ∑ i, leftSquare z (x i) =
      ‖starMulSum x‖ + ‖mulStarSum x‖ := by
  simp only [leftSquare, sum_add_distrib, ← Complex.re_sum,
    ← map_sum]
  change (z.1.1 (starMulSum x)).re + (z.1.2 (mulStarSum x)).re = _
  rw [hp, hq]
  simp

private theorem sum_rightSquare_eq
    (z : StateControl A D)
    {ι : Type*} [Fintype ι] (y : ι → D)
    (hr : z.2.1 (starMulSum y) = (‖starMulSum y‖ : ℂ))
    (ht : z.2.2 (mulStarSum y) = (‖mulStarSum y‖ : ℂ)) :
    ∑ i, rightSquare z (y i) =
      ‖starMulSum y‖ + ‖mulStarSum y‖ := by
  simp only [rightSquare, sum_add_distrib, ← Complex.re_sum,
    ← map_sum]
  change (z.2.1 (starMulSum y)).re + (z.2.2 (mulStarSum y)).re = _
  rw [hr, ht]
  simp

/-- Four norm-attaining states convert the state-free row/column estimate
into the summed additive estimate. -/
theorem hasFiniteSummedAdditiveEstimate_of_rowColumn
    [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ)
    (hrow : HasFiniteRowColumnEstimate B C) :
    HasFiniteSummedAdditiveEstimate B C := by
  intro ι _ _ x y
  obtain ⟨p, hp, hpval⟩ :=
    exists_weakState_apply_eq_norm_of_nonneg
      (starMulSum x) (starMulSum_nonneg x)
  obtain ⟨q, hq, hqval⟩ :=
    exists_weakState_apply_eq_norm_of_nonneg
      (mulStarSum x) (mulStarSum_nonneg x)
  obtain ⟨r, hr, hrval⟩ :=
    exists_weakState_apply_eq_norm_of_nonneg
      (starMulSum y) (starMulSum_nonneg y)
  obtain ⟨t, ht, htval⟩ :=
    exists_weakState_apply_eq_norm_of_nonneg
      (mulStarSum y) (mulStarSum_nonneg y)
  let z : StateControl A D := ((p, q), (r, t))
  have hz : z ∈ stateControls (A := A) (D := D) :=
    ⟨⟨hp, hq⟩, ⟨hr, ht⟩⟩
  refine ⟨z, hz, ?_⟩
  have hleft : ∑ i, leftSquare z (x i) =
      ‖starMulSum x‖ + ‖mulStarSum x‖ :=
    sum_leftSquare_eq z x (by simpa [z] using hpval)
      (by simpa [z] using hqval)
  have hright : ∑ i, rightSquare z (y i) =
      ‖starMulSum y‖ + ‖mulStarSum y‖ :=
    sum_rightSquare_eq z y (by simpa [z] using hrval)
      (by simpa [z] using htval)
  calc
    ‖∑ i, B (x i) (y i)‖ ≤
        (C / 2) *
          (‖starMulSum x‖ + ‖mulStarSum x‖ +
            ‖starMulSum y‖ + ‖mulStarSum y‖) := hrow x y
    _ = (C / 2) * ∑ i,
        (leftSquare z (x i) + rightSquare z (y i)) := by
      rw [sum_add_distrib, hleft, hright]
      ring

/-- The state-free row/column estimate now reaches the exact finite common
product premise W1. -/
theorem finite_stateControl_of_rowColumn
    [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hrow : HasFiniteRowColumnEstimate B C) :
    ∀ s : Finset (A × D),
      ∃ z ∈ stateControls (A := A) (D := D),
        ∀ xy ∈ s, z ∈ controlSet B C xy :=
  finite_stateControl_of_finiteSummedAdditive B C hC
    (hasFiniteSummedAdditiveEstimate_of_rowColumn B C hrow)

/-- The same supplier reaches the concrete two-sided positive-functional
domination W2. -/
theorem exists_twoSidedDomination_of_rowColumn
    [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hrow : HasFiniteRowColumnEstimate B C) :
    ∃ (p q : A →ₚ[ℂ] ℂ) (r t : D →ₚ[ℂ] ℂ),
      IsTwoSidedDominated B p q r t C :=
  exists_twoSidedDomination_of_finiteSummedAdditive B C hC
    (hasFiniteSummedAdditiveEstimate_of_rowColumn B C hrow)

theorem isWeaklyCompact_of_rowColumn
    [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hrow : HasFiniteRowColumnEstimate B C) :
    MathlibAnnex.WeakCompact.IsWeaklyCompact B :=
  isWeaklyCompact_of_finiteSummedAdditive B C hC
    (hasFiniteSummedAdditiveEstimate_of_rowColumn B C hrow)

/-- Total weak-compactness consumer with the zero-algebra cases made
explicit.  No normalized state is requested from a subsingleton algebra;
only the genuinely nontrivial branch invokes state selection. -/
theorem isWeaklyCompact_of_rowColumn_total
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hrow : HasFiniteRowColumnEstimate B C) :
    MathlibAnnex.WeakCompact.IsWeaklyCompact B := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · letI : Subsingleton A := hA
    exact isWeaklyCompact_of_subsingleton_left B
  · letI : Nontrivial A := hA
    rcases subsingleton_or_nontrivial D with hD | hD
    · letI : Subsingleton D := hD
      exact isWeaklyCompact_of_subsingleton_right B
    · letI : Nontrivial D := hD
      exact isWeaklyCompact_of_rowColumn B C hC hrow

end

end MathlibAnnex.CStarBilinear
