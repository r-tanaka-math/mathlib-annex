import BanachGeometry.Basic
import BanachGeometry.OperatorGraphs.GraphSupport
import BanachGeometry.OperatorGraphs.GraphSplitting

/-! Full two-constant data of R6 Proposition 6.8, independent of the
stronger norm-preserving QuantitativeHilbertData specialization. No separability,
completeness, no-c₀ or complete-continuity assumption is needed here.
The two constants are arbitrary positive reals.
Execution evidence is recorded in the external receipts. -/
noncomputable section
namespace BanachGeometry

structure QuantitativeGraphData (A H : Type)
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup H] [NormedSpace ℝ H] where
  lowerConstant : ℝ
  upperConstant : ℝ
  lower_pos : 0 < lowerConstant
  upper_pos : 0 < upperConstant
  d : HilbertPair H → A
  d_isometry : Isometry d
  d_zero : d 0 = 0
  linearMap : A →L[ℝ] H
  h : HilbertPair H ≃ H
  h_zero : h 0 = 0
  lower : ∀ z z', lowerConstant * ‖z-z'‖ ≤ ‖h z-h z'‖
  upper : ∀ z z', ‖h z-h z'‖ ≤ upperConstant * ‖z-z'‖
  linearization : ∀ z, linearMap (d z) = h z-(WithLp.ofLp z).1

namespace QuantitativeGraphData
variable {A H : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (a : QuantitativeGraphData A H)

theorem norm_h_le (z : HilbertPair H) : ‖a.h z‖ ≤ a.upperConstant * ‖z‖ := by
  simpa only [a.h_zero,sub_zero] using a.upper z 0

theorem norm_h_symm_le (z : H) : ‖a.h.symm z‖ ≤ a.lowerConstant⁻¹ * ‖z‖ := by
  have hl := a.lower (a.h.symm z) 0
  rw [a.h.apply_symm_apply,a.h_zero,sub_zero,sub_zero] at hl
  have he : ‖a.h.symm z‖ ≤ ‖z‖/a.lowerConstant :=
    (le_div_iff₀ a.lower_pos).mpr (by nlinarith)
  simpa only [div_eq_mul_inv,mul_comm] using he

def ofQuantitativeHilbertData {c : ℝ} {A : SeparableRealBanach} {H : SeparableRealHilbert}
    (a : QuantitativeHilbertData c A H) (hl : 0 < 1-4*c) (hu : 0 < 1+4*c) :
    QuantitativeGraphData A.Carrier H.Carrier where
  lowerConstant := 1-4*c
  upperConstant := 1+4*c
  lower_pos := hl
  upper_pos := hu
  d := a.d
  d_isometry := a.d_isometry
  d_zero := a.d_zero
  linearMap := a.linearMap
  h := a.h
  h_zero := a.h_zero
  lower := a.lower
  upper := a.upper
  linearization := a.linearization

end QuantitativeGraphData
end BanachGeometry
