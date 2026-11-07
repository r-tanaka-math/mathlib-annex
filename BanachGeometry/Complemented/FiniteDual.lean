import BanachGeometry.SequenceSpaces.C0FiniteHead
import BanachGeometry.Complemented.ConcreteDual

/-! Concrete finite C0L2 products have separable dual, including the empty
product. Hahn-Banach restriction is constructed in ConcreteDual, not assumed. -/
noncomputable section
open TopologicalSpace
namespace BanachGeometry

theorem separableSpace_dual_pi (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W]
    (hW : SeparableSpace (W →L[ℝ] ℝ)) (n : ℕ) : SeparableSpace ((Fin n → W) →L[ℝ] ℝ) := by
  letI : SeparableSpace (W →L[ℝ] ℝ) := hW
  letI : SeparableSpace (C0Dual.Dual (fun _ : ℕ => W)) := C0Dual.separableSpace_dual _
  letI : SeparableSpace ((C0Sum.FiniteHead (fun _ : ℕ => W) n) →L[ℝ] ℝ) :=
    DualTransport.separableSpace_dual_submodule _
  exact DualTransport.separable_of_equiv
    (C0Sum.finiteHeadEquivPi (fun _ : ℕ => W) n).toContinuousLinearEquiv

theorem separableSpace_dual_pi_c0L2 (n : ℕ) : SeparableSpace ((Fin n → C0L2) →L[ℝ] ℝ) :=
  separableSpace_dual_pi C0L2 separableSpace_dual_c0L2 n

end BanachGeometry
