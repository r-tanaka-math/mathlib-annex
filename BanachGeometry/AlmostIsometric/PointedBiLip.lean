import BanachGeometry.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic

/-!
# Pointed quantitative equivalences

The estimates are explicit fields, not typeclass assumptions. This local
structure records a zero-fixing bijection and two Lipschitz bounds; it does
not supply quantitative Hilbert models. Existence constructs those models
and assembles the fixed Banach pair. Local execution evidence is external.
-/

noncomputable section
namespace BanachGeometry

universe u v w

/-- A bijection fixing zero with the same explicit bound in both directions.
No linearity or additivity is asserted. -/
structure PointedBiLip (E : Type u) (F : Type v)
    [NormedAddCommGroup E] [NormedAddCommGroup F] (C : ℝ) where
  equiv : E ≃ F
  zero_eq : equiv 0 = 0
  forward : ∀ x y, ‖equiv x - equiv y‖ ≤ C * ‖x - y‖
  backward : ∀ x y, ‖equiv.symm x - equiv.symm y‖ ≤ C * ‖x - y‖

namespace PointedBiLip

variable {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    {C D : ℝ}

@[simp] theorem symm_zero (e : PointedBiLip E F C) : e.equiv.symm 0 = 0 := by
  apply e.equiv.injective
  simpa using e.zero_eq.symm

theorem norm_le (e : PointedBiLip E F C) (x : E) : ‖e.equiv x‖ ≤ C * ‖x‖ := by
  simpa [e.zero_eq] using e.forward x 0

theorem symm_norm_le (e : PointedBiLip E F C) (y : F) :
    ‖e.equiv.symm y‖ ≤ C * ‖y‖ := by
  simpa using e.backward y 0

def symm (e : PointedBiLip E F C) : PointedBiLip F E C where
  equiv := e.equiv.symm
  zero_eq := e.symm_zero
  forward := e.backward
  backward := e.forward

def weaken (e : PointedBiLip E F C) (hCD : C ≤ D) : PointedBiLip E F D where
  equiv := e.equiv
  zero_eq := e.zero_eq
  forward x y := (e.forward x y).trans (mul_le_mul_of_nonneg_right hCD (norm_nonneg _))
  backward x y := (e.backward x y).trans (mul_le_mul_of_nonneg_right hCD (norm_nonneg _))

def refl (E : Type u) [NormedAddCommGroup E] (C : ℝ) (hC : 1 ≤ C) :
    PointedBiLip E E C where
  equiv := Equiv.refl E
  zero_eq := rfl
  forward x y := by simpa using mul_le_mul_of_nonneg_right hC (norm_nonneg (x - y))
  backward x y := by simpa using mul_le_mul_of_nonneg_right hC (norm_nonneg (x - y))

def trans (e : PointedBiLip E F C) (f : PointedBiLip F G D)
    (hC : 0 ≤ C) (hD : 0 ≤ D) : PointedBiLip E G (D * C) where
  equiv := e.equiv.trans f.equiv
  zero_eq := by simp [Equiv.trans_apply, e.zero_eq, f.zero_eq]
  forward x y := by
    calc
      ‖f.equiv (e.equiv x) - f.equiv (e.equiv y)‖ ≤ D * ‖e.equiv x - e.equiv y‖ :=
        f.forward _ _
      _ ≤ D * (C * ‖x - y‖) := mul_le_mul_of_nonneg_left (e.forward x y) hD
      _ = (D * C) * ‖x - y‖ := (mul_assoc _ _ _).symm
  backward x y := by
    calc
      ‖e.equiv.symm (f.equiv.symm x) - e.equiv.symm (f.equiv.symm y)‖ ≤
          C * ‖f.equiv.symm x - f.equiv.symm y‖ := e.backward _ _
      _ ≤ C * (D * ‖x - y‖) := mul_le_mul_of_nonneg_left (f.backward x y) hC
      _ = (D * C) * ‖x - y‖ := by ring

end PointedBiLip
end BanachGeometry
