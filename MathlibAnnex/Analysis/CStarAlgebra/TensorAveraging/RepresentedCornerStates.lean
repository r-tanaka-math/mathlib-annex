import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedCentralCorner
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.StateBidualNormal
import MathlibAnnex.Analysis.CStarAlgebra.PureState
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Source states on the actual represented central corner

A source state extends as evaluation on the fixed predual of the actual
C*-bidual. Its restriction along the constructed section is positive and
contractive. It need not have mass one: its value at 1 is phi-bar(p), not
phi-bar(1). Continuity is stated for bounded WOT-convergent nets; arbitrary
bounded functionals on B(H) are not declared normal. C03, unbuilt.
-/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

namespace MathlibAnnex.RepresentedCentralCorner
open MathlibAnnex.CStarBidual MathlibAnnex.RepresentedBidual
open MathlibAnnex.Analysis.CStarAlgebra
universe u v t
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- Positivity is deduced on the full positive cone by the actual defining
closure of star squares, not by assuming a square-root API. -/
private theorem positive_of_star_squares
    {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    (f : M →L[ℂ] ℂ) (hs : ∀ x : M, 0 ≤ f (star x * x)) :
    ∀ x : M, 0 ≤ x → 0 ≤ f x := by
  intro x hx
  have hx' := StarOrderedRing.nonneg_iff.mp hx
  refine AddSubmonoid.closure_induction ?_ ?_ ?_ hx'
  · rintro y ⟨z, rfl⟩
    exact hs z
  · simp only [map_zero, le_refl]
  · intro x y _ _ hfx hfy
    simpa only [map_add] using add_nonneg hfx hfy

/-- A state's actual extension on the constructed carrier. -/
def liftedState (phi : StrongDual ℂ A) : Model A →L[ℂ] ℂ := Model.evaluation A phi

@[simp] theorem liftedState_apply (phi : StrongDual ℂ A) (F : Model A) :
    liftedState phi F = Model.toRaw A F phi := rfl

@[simp] theorem norm_liftedState (phi : StrongDual ℂ A) :
    ‖liftedState phi‖ = ‖phi‖ :=
  (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℂ) (E := StrongDual ℂ A)).norm_map phi

theorem liftedState_positive (phi : StrongDual ℂ A) (hphi : phi ∈ stateSpace A) :
    ∀ F : Model A, 0 ≤ F → 0 ≤ liftedState phi F := by
  apply positive_of_star_squares
  intro F
  exact stateExtension_star_square_nonneg phi hphi (Model.toRaw A F)

@[simp] theorem liftedState_one (phi : StrongDual ℂ A) (hphi : phi ∈ stateSpace A) :
    liftedState phi 1 = 1 := hphi.2

theorem liftedState_mem (phi : StrongDual ℂ A) (hphi : phi ∈ stateSpace A) :
    liftedState phi ∈ stateSpace (Model A) :=
  ⟨liftedState_positive phi hphi, liftedState_one phi hphi⟩

variable (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)

/-- This is a positive substate on B(H), not automatically normalized. -/
def cornerFunctional (phi : StrongDual ℂ A) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (liftedState phi).comp (sectionMap pi hpi)

@[simp] theorem cornerFunctional_apply (phi : StrongDual ℂ A) (T : H →L[ℂ] H) :
    cornerFunctional pi hpi phi T = rawSection pi hpi T phi := rfl

@[simp] theorem cornerFunctional_one (phi : StrongDual ℂ A) :
    cornerFunctional pi hpi phi 1 = liftedState phi (projection pi) := by
  change liftedState phi (sectionMap pi hpi 1) = _
  rw [section_one]

theorem cornerFunctional_positive (phi : StrongDual ℂ A) (hphi : phi ∈ stateSpace A) :
    ∀ T : H →L[ℂ] H, 0 ≤ T → 0 ≤ cornerFunctional pi hpi phi T := by
  apply positive_of_star_squares
  intro T
  change 0 ≤ liftedState phi (sectionMap pi hpi (star T * T))
  rw [section_mul, section_star]
  exact liftedState_positive phi hphi _ (star_mul_self_nonneg _)

/-- Positivity bundled on the actual operator algebra. -/
def cornerPositive (phi : StrongDual ℂ A) (hphi : phi ∈ stateSpace A) :
    (H →L[ℂ] H) →ₚ[ℂ] ℂ where
  toLinearMap := (cornerFunctional pi hpi phi).toLinearMap
  monotone' := by
    intro T U hTU
    apply sub_nonneg.mp
    have h := cornerFunctional_positive pi hpi phi hphi (U - T)
      (sub_nonneg.mpr hTU)
    have heq : cornerFunctional pi hpi phi (U - T) =
        cornerFunctional pi hpi phi U - cornerFunctional pi hpi phi T :=
      map_sub (cornerFunctional pi hpi phi) U T
    rw [heq] at h
    exact h

/-- The estimate holds for every source functional, not only states. -/
theorem norm_cornerFunctional_le (phi : StrongDual ℂ A) :
    ‖cornerFunctional pi hpi phi‖ ≤ ‖phi‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg phi)
  intro T
  calc
    ‖cornerFunctional pi hpi phi T‖ ≤ ‖liftedState phi‖ * ‖sectionMap pi hpi T‖ :=
      (liftedState phi).le_opNorm _
    _ = ‖phi‖ * ‖T‖ := by rw [norm_liftedState, norm_section]

theorem norm_cornerFunctional_le_one (phi : StrongDual ℂ A) (hphi : phi ∈ stateSpace A) :
    ‖cornerFunctional pi hpi phi‖ ≤ 1 := by
  apply (norm_cornerFunctional_le pi hpi phi).trans
  exact norm_le_one_of_mem_weakStateSpace (phi := StrongDual.toWeakDual phi) hphi

/-- The same section, on the same bounded net, for every predual test. -/
theorem tendsto_cornerFunctional {ι : Type t} (l : Filter ι)
    (T : ι → H →L[ℂ] H) (U : H →L[ℂ] H)
    (hT : Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (T i)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM U)))
    (r : ℝ) (hr : ∀ᶠ i in l, ‖T i‖ ≤ r) (phi : StrongDual ℂ A) :
    Tendsto (fun i => cornerFunctional pi hpi phi (T i)) l
      (𝓝 (cornerFunctional pi hpi phi U)) :=
  tendsto_evaluation_section pi hpi l T U hT r hr phi

end MathlibAnnex.RepresentedCentralCorner
