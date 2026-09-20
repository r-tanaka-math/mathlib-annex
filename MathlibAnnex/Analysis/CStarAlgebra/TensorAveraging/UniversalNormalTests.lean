import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.UniversalExtension
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.StateControlGauge
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedCornerForms

/-!
# Received universal bilinear estimates in the actual represented corner

The estimate supplier is the exact source-author-A RET2 declaration, rather
than a universally quantified premise.  The inherited RET2 and C01--C03
proofs are source candidates and have NOT been kernel checked here.

The positive controls below are corner substates: they need not take 1 to 1.
The same controls work for all X,Y, and 292*norm(B) is chosen before them.
-/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace MathlibAnnex.RepresentedBidual
open MathlibAnnex.CStarBilinear MathlibAnnex.CStarAlgebra.TensorAveraging
open MathlibAnnex.FiniteApproximation
universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {D : Type v} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- Actual source controls, not an analytic inequality in a theorem premise. -/
theorem exists_universal_stateGauge_domination [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) :
    ∃ (phi : StateIndex A) (psi : StateIndex D),
      IsStrongStarDominated B phi.val psi.val (292 * ‖B‖) := by
  have hC : 0 ≤ (146 : ℝ) * ‖B‖ := mul_nonneg (by norm_num) (norm_nonneg B)
  obtain ⟨phi, psi, h⟩ := exists_stateGauge_domination_of_rowColumn B
    (146 * ‖B‖) hC (hasFiniteRowColumnEstimate_146_norm B)
  refine ⟨phi, psi, ?_⟩
  convert h using 1 <;> ring

/-- All tensor tests, including the zero algebra branch, now use the supplied
universal estimate.  The conclusion is closure of a diagonal point, NOT
existence of a central averaging point. -/
theorem diagonalTensorPoint_rowClosure
    (F : StrongDual ℂ (StrongDual ℂ A)) (hF : ‖F‖ ≤ 1) :
    InWeakStarClosure (diagonalTensorPoint F) (rowConvexSet A) :=
  diagonalTensorPoint_rowClosure_of_estimates F hF
    (fun B => exists_rowColumnEstimate B)

end MathlibAnnex.RepresentedBidual

namespace MathlibAnnex.RepresentedCentralCorner
open MathlibAnnex.RepresentedBidual MathlibAnnex.CStarBilinear
open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra.TensorAveraging
open MathlibAnnex.ProjectiveTensorProduct
universe u v t
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]
variable (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)

/-- A unital representation on a nonzero Hilbert space rules out the zero
source algebra.  No faithfulness or simplicity is required. -/
private theorem nontrivial_source (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : Nontrivial A := by
  apply nontrivial_of_ne (0 : A) 1
  intro h
  have h' := congrArg (fun a : A => pi a) h
  have : (0 : H →L[ℂ] H) = 1 := by simpa only [map_zero, map_one] using h'
  exact zero_ne_one this

/-- Actual positive corner controls for every represented form.  The
source states, and hence all positivity and bounded normality proofs, are
kept as witnesses rather than forgotten at the API boundary. -/
theorem exists_represented_state_controls (B : A →L[ℂ] A →L[ℂ] ℂ) :
    ∃ phi psi : StateIndex A,
      IsStrongStarDominated (representedForm pi hpi B)
        (cornerFunctional pi hpi phi.val) (cornerFunctional pi hpi psi.val)
        (292 * ‖B‖) := by
  letI : Nontrivial A := nontrivial_source pi
  obtain ⟨phi, psi, hB⟩ := exists_universal_stateGauge_domination B
  refine ⟨phi, psi, fun X Y => ?_⟩
  rw [representedForm_apply]
  have h := firstArens_normalState_bound B phi psi (292 * ‖B‖) hB
    (rawSection pi hpi X) (rawSection pi hpi Y)
  simpa only [normalStateGauge_rawSection] using h

/-- Canonical E for an arbitrary projective-tensor-dual test has actual
positive substate controls with a constant depending only on that test. -/
theorem exists_tensor_state_controls (f : StrongDual ℂ (Tensor A)) :
    ∃ phi psi : StateIndex A,
      IsStrongStarDominated (tensorAssignment pi hpi f)
        (cornerFunctional pi hpi phi.val) (cornerFunctional pi hpi psi.val)
        (292 * ‖f‖) := by
  obtain ⟨phi, psi, h⟩ := exists_represented_state_controls pi hpi (tensorDualIsometry f)
  refine ⟨phi, psi, fun X Y => ?_⟩
  simpa only [tensorAssignment_apply,
    (tensorDualIsometry (𝕜 := ℂ) (E := A) (F := A)).norm_map] using h X Y

/-- Remove the source-domination premise from the C03 normality consumer.
The proof uses the same two operator nets, their adjoints and actual bounds. -/
theorem tendsto_representedForm_universal (B : A →L[ℂ] A →L[ℂ] ℂ)
    {ι : Type t} (l : Filter ι) (X Y : ι → H →L[ℂ] H) (X0 Y0 : H →L[ℂ] H)
    (hX : ∀ xi, Tendsto (fun i => X i xi) l (𝓝 (X0 xi)))
    (hXs : ∀ xi, Tendsto (fun i => star (X i) xi) l (𝓝 (star X0 xi)))
    (hY : ∀ xi, Tendsto (fun i => Y i xi) l (𝓝 (Y0 xi)))
    (hYs : ∀ xi, Tendsto (fun i => star (Y i) xi) l (𝓝 (star Y0 xi)))
    (r s : ℝ) (hr : ∀ᶠ i in l, ‖X i‖ ≤ r) (hs : ∀ᶠ i in l, ‖Y i‖ ≤ s) :
    Tendsto (fun i => representedForm pi hpi B (X i) (Y i)) l
      (𝓝 (representedForm pi hpi B X0 Y0)) := by
  letI : Nontrivial A := nontrivial_source pi
  obtain ⟨phi, psi, hB⟩ := exists_universal_stateGauge_domination B
  exact tendsto_representedForm pi hpi B phi psi (292 * ‖B‖)
    (mul_nonneg (by norm_num) (norm_nonneg B)) hB l X Y X0 Y0
    hX hXs hY hYs r s hr hs

end MathlibAnnex.RepresentedCentralCorner
