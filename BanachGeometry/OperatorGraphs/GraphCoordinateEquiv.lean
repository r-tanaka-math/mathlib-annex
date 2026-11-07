import BanachGeometry.Basic
import Mathlib.Tactic

/-! R6 Proposition 6.8: the triangular bijection at a single coordinate,
using QuantitativeHilbertData c A H. The raw product below is used as a set
of pairs only; no maximum-norm estimate is substituted for its eventual ℓ₁
source norm in the graph construction. -/

noncomputable section
namespace BanachGeometry
namespace GraphCoordinate

variable {c : ℝ} {A : SeparableRealBanach} {H : SeparableRealHilbert}
    (a : QuantitativeHilbertData c A H)

def pair (z : A.Carrier × ScalarL2) : HilbertPair H.Carrier :=
  WithLp.toLp 2 (a.linearMap z.1, z.2)

def forward (z : A.Carrier × ScalarL2) : A.Carrier := z.1 + a.d (pair a z)

def backward (ν : A.Carrier) : A.Carrier × ScalarL2 :=
  let w := a.h.symm (a.linearMap ν)
  (ν - a.d w, (WithLp.ofLp w).2)

theorem linearMap_forward (z : A.Carrier × ScalarL2) : a.linearMap (forward a z) = a.h (pair a z) := by
  change a.linearMap (z.1 + a.d (pair a z)) = _
  rw [map_add, a.linearization]
  change a.linearMap z.1 + (a.h (pair a z) - a.linearMap z.1) = _
  abel

theorem linearMap_backward_fst (ν : A.Carrier) :
    a.linearMap (backward a ν).1 = (WithLp.ofLp (a.h.symm (a.linearMap ν))).1 := by
  change a.linearMap (ν - a.d (a.h.symm (a.linearMap ν))) = _
  rw [map_sub, a.linearization, a.h.apply_symm_apply]
  abel

theorem pair_backward (ν : A.Carrier) : pair a (backward a ν) = a.h.symm (a.linearMap ν) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact linearMap_backward_fst a ν
  · rfl

theorem forward_backward (ν : A.Carrier) : forward a (backward a ν) = ν := by
  change (backward a ν).1 + a.d (pair a (backward a ν)) = ν
  rw [pair_backward]
  change ν - a.d (a.h.symm (a.linearMap ν)) + a.d (a.h.symm (a.linearMap ν)) = ν
  exact sub_add_cancel _ _

theorem backward_forward (z : A.Carrier × ScalarL2) : backward a (forward a z) = z := by
  apply Prod.ext
  · change forward a z - a.d (a.h.symm (a.linearMap (forward a z))) = z.1
    rw [linearMap_forward, a.h.symm_apply_apply]
    change z.1 + a.d (pair a z) - a.d (pair a z) = z.1
    exact add_sub_cancel_right _ _
  · change (WithLp.ofLp (a.h.symm (a.linearMap (forward a z)))).2 = z.2
    rw [linearMap_forward, a.h.symm_apply_apply]
    rfl

def equiv : (A.Carrier × ScalarL2) ≃ A.Carrier where
  toFun := forward a
  invFun := backward a
  left_inv := backward_forward a
  right_inv := forward_backward a

theorem forward_zero : forward a 0 = 0 := by
  have hz : pair a 0 = 0 := by
    apply WithLp.ofLp_injective 2
    change (a.linearMap 0, (0 : ScalarL2)) = (0, 0)
    rw [map_zero]
  change (0 : A.Carrier) + a.d (pair a 0) = 0
  rw [hz, a.d_zero, add_zero]

theorem d_difference_norm (w w' : HilbertPair H.Carrier) :
    ‖a.d w - a.d w'‖ = ‖w - w'‖ := by
  simpa only [dist_eq_norm] using a.d_isometry.dist_eq w w'

theorem forward_difference (z z' : A.Carrier × ScalarL2) :
    ‖forward a z - forward a z'‖ ≤ ‖z.1 - z'.1‖ + ‖pair a z - pair a z'‖ := by
  calc
    ‖forward a z - forward a z'‖ =
        ‖(z.1 - z'.1) + (a.d (pair a z) - a.d (pair a z'))‖ := by
      congr 1; unfold forward; abel
    _ ≤ ‖z.1 - z'.1‖ + ‖a.d (pair a z) - a.d (pair a z')‖ := norm_add_le _ _
    _ = ‖z.1 - z'.1‖ + ‖pair a z - pair a z'‖ := by rw [d_difference_norm]

theorem backward_difference (ν ν' : A.Carrier) :
    ‖(backward a ν).1 - (backward a ν').1‖ +
      ‖(backward a ν).2 - (backward a ν').2‖ ≤
    ‖ν - ν'‖ + 2 * ‖a.h.symm (a.linearMap ν) - a.h.symm (a.linearMap ν')‖ := by
  let w := a.h.symm (a.linearMap ν)
  let w' := a.h.symm (a.linearMap ν')
  have hf : ‖(backward a ν).1 - (backward a ν').1‖ ≤ ‖ν - ν'‖ + ‖w - w'‖ := by
    calc
      ‖(backward a ν).1 - (backward a ν').1‖ = ‖(ν - ν') - (a.d w - a.d w')‖ := by
        congr 1; change (ν - a.d w) - (ν' - a.d w') = _; abel
      _ ≤ ‖ν - ν'‖ + ‖a.d w - a.d w'‖ := norm_sub_le _ _
      _ = ‖ν - ν'‖ + ‖w - w'‖ := by rw [d_difference_norm]
  have hs : ‖(backward a ν).2 - (backward a ν').2‖ ≤ ‖w - w'‖ := by
    change ‖(WithLp.ofLp (w - w')).2‖ ≤ ‖w - w'‖
    exact WithLp.norm_snd_le H.Carrier (w - w')
  change _ ≤ ‖ν - ν'‖ + 2 * ‖w - w'‖
  linarith

theorem inverse_pair_difference (hc : 0 < 1 - 4 * c) (ν ν' : A.Carrier) :
    ‖a.h.symm (a.linearMap ν) - a.h.symm (a.linearMap ν')‖ ≤
      (1 - 4 * c)⁻¹ * ‖a.linearMap ν - a.linearMap ν'‖ := by
  have hl := a.lower (a.h.symm (a.linearMap ν)) (a.h.symm (a.linearMap ν'))
  rw [a.h.apply_symm_apply, a.h.apply_symm_apply] at hl
  have hd : ‖a.h.symm (a.linearMap ν) - a.h.symm (a.linearMap ν')‖ ≤ ‖a.linearMap ν - a.linearMap ν'‖ / (1 - 4 * c) :=
    (le_div_iff₀ hc).2 (by nlinarith)
  simpa only [div_eq_mul_inv, mul_comm] using hd

end GraphCoordinate
end BanachGeometry
