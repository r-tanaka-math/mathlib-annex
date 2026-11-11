/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.CornerEquivalence
import Mathlib.Tactic.Linarith

/-!
# Matrix coefficients supported on two hereditary corners

The four entries are `z`, `z * v⋆`, `v * z`, and `v * z * v⋆`, where the
coefficient `z` belongs to the actual closed hereditary algebra `Her(c)`.
Their product is the matrix product with the original coefficient product.
This does not manufacture a unit in `Her(c)`, a projection in the ambient
algebra, or matrix units with scalar coefficients.

All four entry maps preserve the norm of their coefficient. The same ambient
conjugation transports every entry of a further split; siblings are therefore
transported together, rather than split by unrelated choices.
-/

set_option autoImplicit false
noncomputable section

open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The four ambient matrix coefficients for a hereditary corner link. -/
def hereditaryMatrixEntry (v : A) (i j : Bool) (z : A) : A :=
  cond i (cond j (v * z * star v) (v * z)) (cond j (z * star v) z)

@[simp]
theorem hereditaryMatrixEntry_zero (v : A) (i j : Bool) :
    hereditaryMatrixEntry v i j 0 = 0 := by
  cases i <;> cases j <;> simp [hereditaryMatrixEntry]

theorem hereditaryMatrixEntry_add (v : A) (i j : Bool) (z w : A) :
    hereditaryMatrixEntry v i j (z + w) =
      hereditaryMatrixEntry v i j z + hereditaryMatrixEntry v i j w := by
  cases i <;> cases j <;> simp [hereditaryMatrixEntry, mul_add, add_mul]

theorem hereditaryMatrixEntry_smul (v : A) (i j : Bool) (r : ℂ) (z : A) :
    hereditaryMatrixEntry v i j (r • z) = r • hereditaryMatrixEntry v i j z := by
  cases i <;> cases j <;>
    simp [hereditaryMatrixEntry, mul_smul_comm, smul_mul_assoc]

@[simp]
theorem star_hereditaryMatrixEntry (v : A) (i j : Bool) (z : A) :
    star (hereditaryMatrixEntry v i j z) = hereditaryMatrixEntry v j i (star z) := by
  cases i <;> cases j <;> simp [hereditaryMatrixEntry, star_mul, mul_assoc]

/-- Exact matrix multiplication with coefficients in a hereditary algebra.
The Kronecker condition is on the middle indices, not on projections in `A`. -/
theorem hereditaryMatrixEntry_mul {c v z w : A} (hc : IsSelfAdjoint c)
    (hv : star v * v * c = c) (hcv : c * v = 0)
    (hz : z ∈ hereditarySubalgebra c) (hw : w ∈ hereditarySubalgebra c)
    (i j k l : Bool) :
    hereditaryMatrixEntry v i j z * hereditaryMatrixEntry v k l w =
      if j = k then hereditaryMatrixEntry v i l (z * w) else 0 := by
  have hzv : z * v = 0 :=
    mul_eq_zero_of_mem_hereditarySubalgebra_right
      (by simpa only [hc.star_eq] using hcv) hz
  have hvc : star v * c = 0 := by
    simpa only [star_mul, hc.star_eq, star_zero] using congrArg star hcv
  have hvw : star v * w = 0 :=
    mul_eq_zero_of_mem_hereditarySubalgebra_left hvc hw
  have hfix : (star v * v) * w = w :=
    mul_eq_self_of_mem_hereditarySubalgebra hv hw
  have hm : (cond j (z * star v) z) * (cond k (v * w) w) =
      if j = k then z * w else 0 := by
    cases j <;> cases k
    · rfl
    · change z * (v * w) = 0
      rw [← mul_assoc, hzv, zero_mul]
    · change (z * star v) * w = 0
      rw [mul_assoc, hvw, mul_zero]
    · change (z * star v) * (v * w) = z * w
      calc
        (z * star v) * (v * w) = z * ((star v * v) * w) := by
          simp only [mul_assoc]
        _ = z * w := by rw [hfix]
  have h := congrArg (hereditaryMatrixEntry v i l) hm
  cases i <;> cases j <;> cases k <;> cases l <;>
    simpa [hereditaryMatrixEntry, mul_assoc] using h

/-- Left multiplication by a link is isometric on the source hereditary corner. -/
theorem norm_mul_of_mem_hereditarySubalgebra {c v z : A}
    (hv : star v * v * c = c) (hz : z ∈ hereditarySubalgebra c) :
    ‖v * z‖ = ‖z‖ := by
  have hfix := mul_eq_self_of_mem_hereditarySubalgebra hv hz
  have heq : star (v * z) * (v * z) = star z * z := by
    calc
      star (v * z) * (v * z) = star z * ((star v * v) * z) := by
        simp only [star_mul, mul_assoc]
      _ = star z * z := by rw [hfix]
  have hn : ‖v * z‖ * ‖v * z‖ = ‖z‖ * ‖z‖ := by
    rw [← CStarRing.norm_star_mul_self, heq, CStarRing.norm_star_mul_self]
  nlinarith only [hn, norm_nonneg (v * z), norm_nonneg z]

/-- Right multiplication by the adjoint link preserves the coefficient norm. -/
theorem norm_mul_star_of_mem_hereditarySubalgebra {c v z : A}
    (hv : star v * v * c = c) (hz : z ∈ hereditarySubalgebra c) :
    ‖z * star v‖ = ‖z‖ := by
  calc
    ‖z * star v‖ = ‖star (v * star z)‖ := by rw [star_mul, star_star]
    _ = ‖v * star z‖ := norm_star _
    _ = ‖star z‖ := norm_mul_of_mem_hereditarySubalgebra hv (star_mem hz)
    _ = ‖z‖ := norm_star _

/-- Each matrix coefficient has exactly its source coefficient norm. -/
theorem norm_hereditaryMatrixEntry {c v z : A} (hc : IsSelfAdjoint c)
    (hv : star v * v * c = c) (hz : z ∈ hereditarySubalgebra c) (i j : Bool) :
    ‖hereditaryMatrixEntry v i j z‖ = ‖z‖ := by
  cases i <;> cases j
  · rfl
  · exact norm_mul_star_of_mem_hereditarySubalgebra hv hz
  · exact norm_mul_of_mem_hereditarySubalgebra hv hz
  · exact norm_conjugate_of_mem_hereditarySubalgebra hc hv hz

/-- Both diagonal entries remain in the specified parent hereditary algebra
when the link and coefficient do. The off-diagonal entries do so as well. -/
theorem hereditaryMatrixEntry_mem {a v z : A}
    (hv : v ∈ hereditarySubalgebra a) (hz : z ∈ hereditarySubalgebra a)
    (i j : Bool) : hereditaryMatrixEntry v i j z ∈ hereditarySubalgebra a := by
  have hstar : star v ∈ hereditarySubalgebra a := star_mem hv
  cases i <;> cases j
  · exact hz
  · exact (hereditarySubalgebra a).mul_mem hz hstar
  · exact (hereditarySubalgebra a).mul_mem hv hz
  · exact (hereditarySubalgebra a).mul_mem
      ((hereditarySubalgebra a).mul_mem hv hz) hstar

/-- Every entry of a second split is transported by the same first link.
This is an exact equality of ambient elements, including off-diagonal entries. -/
theorem conjugate_hereditaryMatrixEntry {c v w z : A} (hc : IsSelfAdjoint c)
    (hv : star v * v * c = c) (hw : w ∈ hereditarySubalgebra c)
    (hz : z ∈ hereditarySubalgebra c) (i j : Bool) :
    v * hereditaryMatrixEntry w i j z * star v =
      hereditaryMatrixEntry (v * w * star v) i j (v * z * star v) := by
  cases i <;> cases j
  · rfl
  · change v * (z * star w) * star v =
      (v * z * star v) * star (v * w * star v)
    rw [show star (v * w * star v) = v * star w * star v by
      simp only [star_mul, star_star, mul_assoc]]
    exact (conjugate_mul_conjugate_of_mem_hereditarySubalgebra hv (star_mem hw)).symm
  · change v * (w * z) * star v = (v * w * star v) * (v * z * star v)
    exact (conjugate_mul_conjugate_of_mem_hereditarySubalgebra hv hz).symm
  · change v * (w * z * star w) * star v =
      (v * w * star v) * (v * z * star v) * star (v * w * star v)
    rw [show star (v * w * star v) = v * star w * star v by
      simp only [star_mul, star_star, mul_assoc]]
    rw [conjugate_mul_conjugate_of_mem_hereditarySubalgebra hv hz,
      conjugate_mul_conjugate_of_mem_hereditarySubalgebra hv (star_mem hw)]

/-- Transporting both the coefficient and its link preserves the local fixing
equation. No independent choice of a split in the target corner occurs. -/
theorem conjugate_link_fix {c v d w : A} (hc : IsSelfAdjoint c)
    (hv : star v * v * c = c) (hd : d ∈ hereditarySubalgebra c)
    (hw : w ∈ hereditarySubalgebra c) (hwd : star w * w * d = d) :
    star (v * w * star v) * (v * w * star v) * (v * d * star v) =
      v * d * star v := by
  rw [show star (v * w * star v) = v * star w * star v by
    simp only [star_mul, star_star, mul_assoc]]
  rw [conjugate_mul_conjugate_of_mem_hereditarySubalgebra hv hw,
    conjugate_mul_conjugate_of_mem_hereditarySubalgebra hv hd, hwd]

/-- The annihilation relation of a child split is preserved by the same link. -/
theorem conjugate_link_mul_eq_zero {c v d w : A}
    (hv : star v * v * c = c) (hw : w ∈ hereditarySubalgebra c)
    (hdw : d * w = 0) :
    (v * d * star v) * (v * w * star v) = 0 := by
  rw [conjugate_mul_conjugate_of_mem_hereditarySubalgebra hv hw, hdw]
  simp only [mul_zero, zero_mul]

end MathlibAnnex.Analysis.CStarAlgebra
