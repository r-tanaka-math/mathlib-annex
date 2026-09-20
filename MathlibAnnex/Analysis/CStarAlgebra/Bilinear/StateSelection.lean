import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Factorization
import MathlibAnnex.Analysis.CStarAlgebra.State.VectorApproximation

/-!
# Compact selection of controlling states

This file isolates the compactness step in positive-functional domination.
If every finite family of pairs admits one common quadruple of states with
the squared product estimate, weak-star compactness selects a single
quadruple working for every pair.  The selected states are then converted to
the concrete two-sided Hilbert factorization used by `Factorization.lean`.

The finite-family estimate is intentionally a premise: proving it for every
bounded C-star bilinear form is the remaining noncommutative Grothendieck
inequality, not a topological compactness argument.
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder

namespace MathlibAnnex.CStarBilinear

open MathlibAnnex.Analysis.CStarAlgebra

universe uA uD

noncomputable section

variable {A : Type uA} [CStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
variable {D : Type uD} [CStarAlgebra D]
  [PartialOrder D] [StarOrderedRing D]

/-- Four weak-star states, two for each C-star algebra. -/
abbrev StateControl (A : Type uA) (D : Type uD)
    [CStarAlgebra A] [CStarAlgebra D] :=
  (WeakDual ℂ A × WeakDual ℂ A) × (WeakDual ℂ D × WeakDual ℂ D)

/-- The compact set of quadruples of states. -/
def stateControls : Set (StateControl A D) :=
  (weakStateSpace A ×ˢ weakStateSpace A) ×ˢ
    (weakStateSpace D ×ˢ weakStateSpace D)

theorem isCompact_stateControls : IsCompact (stateControls (A := A) (D := D)) :=
  (isCompact_weakStateSpace.prod isCompact_weakStateSpace).prod
    (isCompact_weakStateSpace.prod isCompact_weakStateSpace)

/-- The left two-state quadratic expression. -/
def leftSquare (z : StateControl A D) (x : A) : ℝ :=
  (z.1.1 (star x * x)).re + (z.1.2 (x * star x)).re

/-- The right two-state quadratic expression. -/
def rightSquare (z : StateControl A D) (y : D) : ℝ :=
  (z.2.1 (star y * y)).re + (z.2.2 (y * star y)).re

theorem continuous_leftSquare (x : A) :
    Continuous (fun z : StateControl A D ↦ leftSquare z x) := by
  apply Continuous.add
  · exact Complex.continuous_re.comp
      ((WeakDual.eval_continuous (star x * x)).comp
        (continuous_fst.comp continuous_fst))
  · exact Complex.continuous_re.comp
      ((WeakDual.eval_continuous (x * star x)).comp
        (continuous_snd.comp continuous_fst))

theorem continuous_rightSquare (y : D) :
    Continuous (fun z : StateControl A D ↦ rightSquare z y) := by
  apply Continuous.add
  · exact Complex.continuous_re.comp
      ((WeakDual.eval_continuous (star y * y)).comp
        (continuous_fst.comp continuous_snd))
  · exact Complex.continuous_re.comp
      ((WeakDual.eval_continuous (y * star y)).comp
        (continuous_snd.comp continuous_snd))

/-- Closed constraint associated to one input pair. -/
def controlSet (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (xy : A × D) :
    Set (StateControl A D) :=
  {z | ‖B xy.1 xy.2‖ ^ 2 ≤
    C ^ 2 * leftSquare z xy.1 * rightSquare z xy.2}

theorem isClosed_controlSet
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (xy : A × D) :
    IsClosed (controlSet B C xy) := by
  apply isClosed_le continuous_const
  exact (continuous_const.mul (continuous_leftSquare xy.1)).mul
    (continuous_rightSquare xy.2)

/-- Compactness upgrades common finite state controls to one common global
state control.  In particular, it does not choose a different convex
combination or state quadruple for each final constraint. -/
theorem exists_global_stateControl
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ)
    (hfinite : ∀ s : Finset (A × D),
      ∃ z ∈ stateControls (A := A) (D := D),
        ∀ xy ∈ s, z ∈ controlSet B C xy) :
    ∃ z ∈ stateControls (A := A) (D := D),
      ∀ x y, ‖B x y‖ ^ 2 ≤
        C ^ 2 * leftSquare z x * rightSquare z y := by
  have hne :
      ((stateControls (A := A) (D := D)) ∩
        ⋂ xy : A × D, controlSet B C xy).Nonempty := by
    apply isCompact_stateControls.inter_iInter_nonempty
    · exact fun xy ↦ isClosed_controlSet B C xy
    · intro s
      obtain ⟨z, hz, hzs⟩ := hfinite s
      refine ⟨z, hz, ?_⟩
      simp only [mem_iInter]
      intro xy hxy
      exact hzs xy hxy
  obtain ⟨z, hz, hall⟩ := hne
  refine ⟨z, hz, fun x y ↦ ?_⟩
  exact (mem_iInter.mp hall) (x, y)

/-- The finite-state form of noncommutative Grothendieck domination produces
the actual positive maps and the product Hilbert-seminorm estimate. -/
theorem exists_twoSidedDomination_of_finite_stateControl
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hfinite : ∀ s : Finset (A × D),
      ∃ z ∈ stateControls (A := A) (D := D),
        ∀ xy ∈ s, z ∈ controlSet B C xy) :
    ∃ (p q : A →ₚ[ℂ] ℂ) (r t : D →ₚ[ℂ] ℂ),
      IsTwoSidedDominated B p q r t C := by
  obtain ⟨z, hz, hsq⟩ := exists_global_stateControl B C hfinite
  let p : A →ₚ[ℂ] ℂ :=
    PositiveLinearMap.mk₀ z.1.1.toStrongDual.toLinearMap hz.1.1.1
  let q : A →ₚ[ℂ] ℂ :=
    PositiveLinearMap.mk₀ z.1.2.toStrongDual.toLinearMap hz.1.2.1
  let r : D →ₚ[ℂ] ℂ :=
    PositiveLinearMap.mk₀ z.2.1.toStrongDual.toLinearMap hz.2.1.1
  let t : D →ₚ[ℂ] ℂ :=
    PositiveLinearMap.mk₀ z.2.2.toStrongDual.toLinearMap hz.2.2.1
  refine ⟨p, q, r, t, ?_⟩
  intro x y
  apply (sq_le_sq₀ (norm_nonneg (B x y))
    (mul_nonneg (mul_nonneg hC
      (norm_nonneg (toTwoSidedPreGNS p q x)))
      (norm_nonneg (toTwoSidedPreGNS r t y)))).mp
  calc
    ‖B x y‖ ^ 2 ≤
        C ^ 2 * leftSquare z x * rightSquare z y := hsq x y
    _ = C ^ 2 * ‖toTwoSidedPreGNS p q x‖ ^ 2 *
        ‖toTwoSidedPreGNS r t y‖ ^ 2 := by
      rw [norm_toTwoSidedPreGNS_sq, norm_toTwoSidedPreGNS_sq]
      rfl
    _ = (C * ‖toTwoSidedPreGNS p q x‖ *
        ‖toTwoSidedPreGNS r t y‖) ^ 2 := by ring

/-- Consequently the finite common-state estimate already implies weak
compactness; the only missing universal input is the finite analytic
Grothendieck estimate itself. -/
theorem isWeaklyCompact_of_finite_stateControl
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hfinite : ∀ s : Finset (A × D),
      ∃ z ∈ stateControls (A := A) (D := D),
        ∀ xy ∈ s, z ∈ controlSet B C xy) :
    MathlibAnnex.WeakCompact.IsWeaklyCompact B := by
  obtain ⟨p, q, r, t, hdom⟩ :=
    exists_twoSidedDomination_of_finite_stateControl B C hC hfinite
  exact isWeaklyCompact_of_twoSidedDominated B p q r t C hC hdom

end

end MathlibAnnex.CStarBilinear
