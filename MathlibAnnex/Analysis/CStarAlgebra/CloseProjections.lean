import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Close projections in a unital C-star algebra

Two star projections at distance strictly less than one are unitarily conjugate.
The proof constructs the standard invertible intertwiner and takes its polar part.
-/

set_option autoImplicit false

open scoped NNReal Ring

namespace IsStarProjection

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Conjugation of a star projection by a unitary is a star projection. -/
theorem unitary_conjugate {p : A} (hp : IsStarProjection p) (u : unitary A) :
    IsStarProjection ((u : A) * p * star (u : A)) := by
  constructor
  · rw [isIdempotentElem_iff]
    calc
      ((u : A) * p * star (u : A)) * ((u : A) * p * star (u : A)) =
          (u : A) * p * (star (u : A) * (u : A)) * p * star (u : A) := by
            simp only [mul_assoc]
      _ = (u : A) * p * p * star (u : A) := by
        rw [Unitary.star_mul_self_of_mem u.prop, mul_one]
      _ = (u : A) * (p * p) * star (u : A) := by simp only [mul_assoc]
      _ = (u : A) * p * star (u : A) := by rw [hp.isIdempotentElem.eq]
  · rw [isSelfAdjoint_iff]
    simp [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc]

/-- The standard intertwiner between two projections. -/
def closeIntertwiner (p q : A) : A :=
  q * p + (1 - q) * (1 - p)

omit [PartialOrder A] [StarOrderedRing A] in
theorem closeIntertwiner_mul (p q : A) (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    closeIntertwiner p q * p = q * closeIntertwiner p q := by
  have hl : closeIntertwiner p q * p = q * p := by
    simp [closeIntertwiner, add_mul, mul_assoc, hp.isIdempotentElem.eq,
      hp.one_sub_mul_self]
  have hr : q * closeIntertwiner p q = q * p := by
    simp [closeIntertwiner, mul_add, ← mul_assoc, hq.isIdempotentElem.eq,
      hq.mul_one_sub_self]
  exact hl.trans hr.symm

omit [PartialOrder A] [StarOrderedRing A] in
theorem closeIntertwiner_sub_one (p q : A) (hp : IsStarProjection p) :
    closeIntertwiner p q - 1 = (q - p) * (2 * p - 1) := by
  simp only [closeIntertwiner]
  noncomm_ring [hp.isIdempotentElem.eq]

omit [PartialOrder A] [StarOrderedRing A] in
theorem norm_closeIntertwiner_sub_one (p q : A) [Nontrivial A]
    (hp : IsStarProjection p) :
    ‖closeIntertwiner p q - 1‖ = ‖p - q‖ := by
  rw [closeIntertwiner_sub_one p q hp]
  let s : unitary A := ⟨2 * p - 1, hp.two_mul_sub_one_mem_unitary⟩
  change ‖(q - p) * (s : A)‖ = ‖p - q‖
  rw [CStarRing.norm_mul_coe_unitary]
  exact norm_sub_rev q p

omit [PartialOrder A] [StarOrderedRing A] in
theorem isUnit_closeIntertwiner (p q : A) [Nontrivial A]
    (hp : IsStarProjection p) (hclose : ‖p - q‖ < 1) :
    IsUnit (closeIntertwiner p q) := by
  have hnear : ‖closeIntertwiner p q - (1 : A)‖ <
      (‖(↑((1 : Aˣ)⁻¹) : A)‖)⁻¹ := by
    simpa [norm_closeIntertwiner_sub_one p q hp] using hclose
  exact (Units.ofNearby (1 : Aˣ) (closeIntertwiner p q) hnear).isUnit

/-- The polar part of an invertible intertwiner of self-adjoint elements is unitary and
is still an intertwiner. -/
theorem exists_unitary_of_isUnit_of_mul_eq {x p q : A} (hx : IsUnit x)
    (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q) (hxp : x * p = q * x) :
    ∃ u : unitary A, (u : A) * p = q * u := by
  let a : A := star x * x
  let s : A := CFC.sqrt a
  let t : A := s⁻¹ʳ
  let u : A := x * t
  have ha_pos : IsStrictlyPositive a := by
    apply CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mpr
    exact ⟨x, hx, rfl⟩
  have hs_unit : IsUnit s := by
    exact ha_pos.isUnit_cfcSqrt a
  have hs_self : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)
  have ht_self : IsSelfAdjoint t := hs_self.ringInverse
  have hu_unit : IsUnit u := hx.mul hs_unit.ringInverse
  have hstar : p * star x = star x * q := by
    have := congrArg star hxp
    simpa [star_mul, hp.star_eq, hq.star_eq] using this
  have ha_comm : Commute a p := by
    rw [commute_iff_eq]
    dsimp only [a]
    calc
      star x * x * p = star x * (x * p) := by rw [mul_assoc]
      _ = star x * (q * x) := by rw [hxp]
      _ = (star x * q) * x := by rw [mul_assoc]
      _ = (p * star x) * x := by rw [hstar]
      _ = p * (star x * x) := by rw [mul_assoc]
  have hs_comm : Commute s p := by
    dsimp only [s]
    simpa [CFC.sqrt] using ha_comm.cfcₙ_nnreal NNReal.sqrt
  have ht_comm : Commute t p := by
    dsimp only [t]
    rw [Ring.inverse_of_isUnit hs_unit]
    exact Commute.units_inv_left (by simpa using hs_comm)
  have hu_star_mul : star u * u = 1 := by
    dsimp only [u]
    rw [star_mul, ht_self.star_eq]
    calc
      t * star x * (x * t) = t * (star x * x) * t := by simp only [mul_assoc]
      _ = t * a * t := rfl
      _ = t * (s * s) * t := by rw [CFC.sqrt_mul_sqrt_self a ha_pos.nonneg]
      _ = (t * s) * (s * t) := by simp only [mul_assoc]
      _ = 1 := by
        rw [show t * s = 1 by exact Ring.inverse_mul_cancel s hs_unit,
          show s * t = 1 by exact Ring.mul_inverse_cancel s hs_unit, one_mul]
  have hu_mem : u ∈ unitary A := hu_unit.mem_unitary_of_star_mul_self hu_star_mul
  let U : unitary A := ⟨u, hu_mem⟩
  refine ⟨U, ?_⟩
  change u * p = q * u
  dsimp only [u]
  calc
    x * t * p = x * (t * p) := by rw [mul_assoc]
    _ = x * (p * t) := by rw [ht_comm.eq]
    _ = (x * p) * t := by rw [mul_assoc]
    _ = (q * x) * t := by rw [hxp]
    _ = q * (x * t) := by rw [mul_assoc]

/-- Star projections at distance less than one are unitarily conjugate. -/
theorem exists_unitary_conjugate_of_norm_sub_lt_one {p q : A} [Nontrivial A]
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hclose : ‖p - q‖ < 1) :
    ∃ u : unitary A, (u : A) * p * star u = q := by
  have hx := isUnit_closeIntertwiner p q hp hclose
  obtain ⟨u, hu⟩ := exists_unitary_of_isUnit_of_mul_eq hx hp.isSelfAdjoint
    hq.isSelfAdjoint (closeIntertwiner_mul p q hp hq)
  refine ⟨u, ?_⟩
  rw [hu, mul_assoc, Unitary.coe_mul_star_self, mul_one]

end IsStarProjection
