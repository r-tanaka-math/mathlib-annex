import MathlibAnnex.Analysis.CStarAlgebra.SmallUnitary

/-! A small exact vector correction with one path and both all-time actions. -/

set_option autoImplicit false

noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

/-- A near-identity unitary has uniform forward and inverse conjugation
control. The same commutator bounds both actions. -/
theorem unitary_conjugates_sub_le (u : unitary A) (a : A) :
    ‖star (u : A) * a * (u : A) - a‖ ≤
        2 * ‖(u : A) - 1‖ * ‖a‖ ∧
    ‖(u : A) * a * star (u : A) - a‖ ≤
        2 * ‖(u : A) - 1‖ * ‖a‖ := by
  have hcomm : ‖(u : A) * a - a * (u : A)‖ ≤
      2 * ‖(u : A) - 1‖ * ‖a‖ := by
    have heq : (u : A) * a - a * (u : A) =
        ((u : A) - 1) * a - a * ((u : A) - 1) := by
      simp [sub_mul, mul_sub]
    rw [heq]
    calc
      _ ≤ ‖((u : A) - 1) * a‖ + ‖a * ((u : A) - 1)‖ := norm_sub_le _ _
      _ ≤ ‖(u : A) - 1‖ * ‖a‖ + ‖a‖ * ‖(u : A) - 1‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2 * ‖(u : A) - 1‖ * ‖a‖ := by ring
  constructor
  · have heq : star (u : A) * a * (u : A) - a =
        star (u : A) * (a * (u : A) - (u : A) * a) := by
      have hunit : star (u : A) * (u : A) = 1 := u.property.1
      rw [mul_sub, ← mul_assoc, ← mul_assoc, hunit, one_mul, mul_assoc]
    rw [heq]
    calc
      _ = ‖a * (u : A) - (u : A) * a‖ := by
        simpa using CStarRing.norm_coe_unitary_mul (star u)
          (a * (u : A) - (u : A) * a)
      _ = ‖(u : A) * a - a * (u : A)‖ := norm_sub_rev _ _
      _ ≤ _ := hcomm
  · have heq : (u : A) * a * star (u : A) - a =
        ((u : A) * a - a * (u : A)) * star (u : A) := by
      have hunit : (u : A) * star (u : A) = 1 := u.property.2
      rw [sub_mul, mul_assoc, mul_assoc, hunit, mul_one]
    rw [heq]
    calc
      _ = ‖(u : A) * a - a * (u : A)‖ := by
        simpa using CStarRing.norm_mul_coe_unitary
          ((u : A) * a - a * (u : A)) (star u)
      _ ≤ _ := hcomm

/-- Exact correction of nearby unit vectors in an irreducible representation.
The returned path starts at one and has both forward and actual inverse
conjugation bounds at every time. -/
theorem StarAlgHom.exists_small_unitary_path_apply_eq
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ξ η : H, ‖ξ‖ = 1 → ‖η‖ = 1 → ‖ξ - η‖ < δ →
        ∃ u : unitary A, ∃ p : Path 1 u,
          pi (u : A) ξ = η ∧
          ∀ t : Set.Icc (0 : ℝ) 1, ∀ a : A,
            ‖star (p t : A) * a * (p t : A) - a‖ ≤ ε * ‖a‖ ∧
            ‖(p t : A) * a * star (p t : A) - a‖ ≤ ε * ‖a‖ := by
  let r : ℝ := min 1 (ε / 2)
  have hr : 0 < r := lt_min zero_lt_one (half_pos hε)
  obtain ⟨δ, hδ, hsmall⟩ :=
    StarAlgHom.exists_unitary_apply_eq_and_norm_sub_one_lt pi hpi hr
  refine ⟨δ, hδ, ?_⟩
  intro ξ η hξ hη hclose
  obtain ⟨u, huξ, hune⟩ := hsmall ξ η hξ hη hclose
  have huTwo : ‖(u : A) - 1‖ < 2 := by
    calc
      _ < r := hune
      _ ≤ 1 := min_le_left _ _
      _ < 2 := by norm_num
  let p : Path (1 : unitary A) u := Unitary.path 1 u (by simpa using huTwo)
  refine ⟨u, p, huξ, ?_⟩
  intro t a
  have hp : ‖(p t : A) - 1‖ ≤ ‖(u : A) - 1‖ := by
    have h := Unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le
      u t.2 huTwo
    simpa [p, Unitary.path] using h
  have hcoeff : 2 * ‖(p t : A) - 1‖ ≤ ε := by
    have hrε : r ≤ ε / 2 := min_le_right _ _
    linarith
  obtain ⟨hforward, hinverse⟩ := unitary_conjugates_sub_le (p t) a
  constructor
  · exact hforward.trans (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg a))
  · exact hinverse.trans (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg a))

end MathlibAnnex.Analysis.CStarAlgebra
