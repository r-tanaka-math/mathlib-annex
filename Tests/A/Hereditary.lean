import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.Representation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-! Direct consumers of the literal sandwich carrier and quotient witnesses. -/

set_option autoImplicit false
noncomputable section

open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra Matrix.Norms.L2Operator NNReal

universe u v

section NonUnital

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

example (a : A) (ha : 0 ≤ a) :
    (hereditarySubalgebra a : Set A) =
      closure (Set.range (fun x : A => a * x * a)) :=
  coe_hereditarySubalgebra_of_isSelfAdjoint ha.isSelfAdjoint

example (a : A) (ha : 0 ≤ a) :
    a ∈ closure (Set.range (fun x : A => a * x * a)) := by
  rw [← coe_hereditarySubalgebra_of_isSelfAdjoint ha.isSelfAdjoint]
  exact self_mem_hereditarySubalgebra ha

example (a : A) (ha : 0 ≤ a) (b : A) :
    a * b * a ∈ hereditarySubalgebra a := by
  simpa only [ha.star_eq] using sandwich_mem_hereditarySubalgebra a b

example (a : A) (x y b : A) (hx : x ∈ hereditarySubalgebra a)
    (hy : y ∈ hereditarySubalgebra a) :
    x * b * y ∈ hereditarySubalgebra a :=
  mul_mul_mem_hereditarySubalgebra a b hx hy

example (a : A) : CompleteSpace (hereditarySubalgebra a) := inferInstance

example (a : A) : NonUnitalCStarAlgebra (hereditarySubalgebra a) := inferInstance

example (a x y : A) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ∈ hereditarySubalgebra a) : x ∈ hereditarySubalgebra a :=
  isHereditary_hereditarySubalgebra a hx hxy hy

example (a b : A) (ha : 0 ≤ a) (hab : a ≤ b) :
    hereditarySubalgebra a ≤ hereditarySubalgebra b :=
  hereditarySubalgebra_le_of_nonneg_le ha hab

example (a : A) (ha : 0 ≤ a) (ε : ℝ≥0) :
    cfcₙ (fun t : ℝ≥0 => t - ε) a ∈ hereditarySubalgebra a ∧
      ‖a - cfcₙ (fun t : ℝ≥0 => t - ε) a‖₊ ≤ ε :=
  ⟨cfcₙ_tsub_mem_hereditarySubalgebra ha ε, nnnorm_sub_cfcₙ_tsub_le ha ε⟩

example (x : A) (hx : x ∈ hereditarySubalgebra (0 : A)) : x = 0 := by
  simpa only [hereditarySubalgebra_zero, NonUnitalStarAlgebra.mem_bot] using hx

end NonUnital

section Surjective

variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

example (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q) (a : A) (b : B)
    (hb : b ∈ hereditarySubalgebra (q a)) :
    ∃ x : A, x ∈ hereditarySubalgebra a ∧ q x = b :=
  (mem_hereditarySubalgebra_image_iff q hq a b).1 hb

example (q : A →⋆ₙₐ[ℂ] B) (a x : A) (hx : x ∈ hereditarySubalgebra a) :
    q x ∈ hereditarySubalgebra (q a) :=
  hereditarySubalgebra_map_le q a ⟨x, hx, rfl⟩

end Surjective

/-- In `M₂(ℂ)`, the hereditary algebra of the unit contains noncommuting elements.
Replacing it with the ordinary one-generator algebra would falsify this consumer. -/
example : ¬ (∀ x ∈ hereditarySubalgebra (1 : Matrix (Fin 2) (Fin 2) ℂ),
    ∀ y ∈ hereditarySubalgebra (1 : Matrix (Fin 2) (Fin 2) ℂ), x * y = y * x) := by
  intro h
  let x : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
  let y : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
  have hxy := h x (by simp) y (by simp)
  have h00 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 0 0) hxy
  norm_num [x, y, Matrix.mul_apply, Fin.sum_univ_two] at h00
