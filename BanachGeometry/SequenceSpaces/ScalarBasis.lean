import BanachGeometry.SequenceSpaces.C0Adapters
import BanachGeometry.SequenceSpaces.C0Banach

/-! The existing scalar c0 basis, finite heads and decay predicate, separated
from graph/dual obstruction proofs. Their qualified names and bodies are retained. -/
noncomputable section
open Filter
namespace BanachGeometry
namespace CanonicalSequences

def scalarBasis (n : ℕ) : ScalarC0 :=
  (C0Sum.homogeneousLinearIsometryEquiv ℝ) (C0Sum.single n (1 : ℝ))
@[simp] theorem norm_scalarBasis (n : ℕ) : ‖scalarBasis n‖ = 1 := by
  rw [scalarBasis, LinearIsometryEquiv.norm_map, C0Sum.norm_single]; norm_num

def scalarHead (n : ℕ) (a : ScalarC0) : ScalarC0 :=
  (C0Sum.homogeneousLinearIsometryEquiv ℝ)
    (C0Sum.head (fun _ : ℕ => ℝ) n ((C0Sum.homogeneousLinearIsometryEquiv ℝ).symm a))

theorem tendsto_scalarHead (a : ScalarC0) : Tendsto (fun n => scalarHead n a) atTop (nhds a) := by
  have ht := ((C0Sum.homogeneousLinearIsometryEquiv ℝ).continuous.tendsto _).comp
    (C0Sum.tendsto_head (fun _ : ℕ => ℝ) ((C0Sum.homogeneousLinearIsometryEquiv ℝ).symm a))
  simpa only [Function.comp_def, scalarHead, LinearIsometryEquiv.apply_symm_apply] using ht

theorem norm_apply_scalar_le (a : ScalarC0) (j : ℕ) : ‖a j‖ ≤ ‖a‖ := by
  calc
    ‖a j‖ = ‖((C0Sum.homogeneousLinearIsometryEquiv ℝ).symm a) j‖ := rfl
    _ ≤ ‖(C0Sum.homogeneousLinearIsometryEquiv ℝ).symm a‖ :=
      ((C0Sum.homogeneousLinearIsometryEquiv ℝ).symm a).norm_apply_le j
    _ = ‖a‖ := (C0Sum.homogeneousLinearIsometryEquiv ℝ).symm.norm_map a

end CanonicalSequences

def BasisDecay (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ T : ScalarC0 →L[ℝ] E,
    Tendsto (fun n => ‖T (CanonicalSequences.scalarBasis n)‖) atTop (nhds 0)

end BanachGeometry
