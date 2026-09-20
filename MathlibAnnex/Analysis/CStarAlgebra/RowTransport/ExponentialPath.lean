import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.Exponential
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.SmallPath

set_option autoImplicit false
noncomputable section
open NormedSpace
namespace MathlibAnnex.Analysis.CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

def expUnitaryPiPath (b : selfAdjoint A) :
    Path (1 : unitary A) (selfAdjoint.expUnitary ((Real.pi : ℝ) • b)) :=
  { toFun := fun t => selfAdjoint.expUnitary ((t : ℝ) • ((Real.pi : ℝ) • b))
    continuous_toFun := by fun_prop
    source' := by simp
    target' := by simp }

theorem expUnitaryPiPath_protection
    (b : selfAdjoint A) (a : A) (t : Set.Icc (0 : ℝ) 1) :
    let p := expUnitaryPiPath b
    ‖(p t : A) * a * star (p t : A) - a‖ ≤
      Real.pi * ‖(b : A) * a - a * (b : A)‖ ∧
    ‖star (p t : A) * a * (p t : A) - a‖ ≤
      Real.pi * ‖(b : A) * a - a * (b : A)‖ := by
  dsimp [expUnitaryPiPath]
  have h := expUnitary_smul_both_conjugations_le ((Real.pi : ℝ) • b) a t t.property
  dsimp at h
  have hc : ‖(((Real.pi : ℝ) • b : selfAdjoint A) : A) * a -
      a * (((Real.pi : ℝ) • b : selfAdjoint A) : A)‖ =
      Real.pi * ‖(b : A) * a - a * (b : A)‖ := by
    change ‖((Real.pi : ℝ) • (b : A)) * a - a * ((Real.pi : ℝ) • (b : A))‖ = _
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  change ‖((Real.pi : ℝ) • (b : A)) * a - a * ((Real.pi : ℝ) • (b : A))‖ = _ at hc
  rw [hc] at h
  have hcoeff : (t : ℝ) * (Real.pi * ‖(b : A) * a - a * (b : A)‖) ≤
      Real.pi * ‖(b : A) * a - a * (b : A)‖ := by
    calc
      _ ≤ 1 * (Real.pi * ‖(b : A) * a - a * (b : A)‖) :=
        mul_le_mul_of_nonneg_right t.property.2
          (mul_nonneg Real.pi_pos.le (norm_nonneg ((b : A) * a - a * (b : A))))
      _ = _ := one_mul _
  exact ⟨h.1.trans hcoeff, h.2.trans hcoeff⟩

variable [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

omit [Nontrivial A] in
theorem representation_expUnitary_pi_apply
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (b : A) (hb : 0 ≤ b) (ξ : H) :
    let bs : selfAdjoint A := ⟨b, IsSelfAdjoint.of_nonneg hb⟩
    let B : selfAdjoint (H →L[ℂ] H) :=
      ⟨pi b, IsSelfAdjoint.of_nonneg (map_nonneg pi hb)⟩
    pi (selfAdjoint.expUnitary ((Real.pi : ℝ) • bs) : A) ξ =
      exp (Complex.I • (((Real.pi : ℝ) • B : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)) ξ := by
  dsimp
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  letI : NormedAlgebra ℚ (H →L[ℂ] H) :=
    NormedAlgebra.restrictScalars ℚ ℂ (H →L[ℂ] H)
  rw [selfAdjoint.expUnitary_coe,
    NormedSpace.map_exp pi (map_continuous pi)]
  rw [map_smul pi Complex.I]
  change (exp (Complex.I • pi ((Real.pi : ℝ) • b))) ξ =
    (exp (Complex.I • ((Real.pi : ℝ) • pi b))) ξ
  have hreal : pi ((Real.pi : ℝ) • b) = (Real.pi : ℝ) • pi b := by
    change pi ((Real.pi : ℂ) • b) = (Real.pi : ℂ) • pi b
    exact map_smul pi (Real.pi : ℂ) b
  rw [hreal]

omit [Nontrivial A] in
theorem representation_expUnitary_pi_endpoint_le
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (b : A) (hb : 0 ≤ b)
    (ξ η : H) :
    ‖pi (selfAdjoint.expUnitary ((Real.pi : ℝ) •
        (⟨b, IsSelfAdjoint.of_nonneg hb⟩ : selfAdjoint A)) : A) ξ - η‖ ≤
      Real.pi / 2 * (‖pi b (ξ + η)‖ + ‖pi b (ξ - η) - (ξ - η)‖) := by
  have hbridge := representation_expUnitary_pi_apply pi b hb ξ
  dsimp at hbridge
  rw [hbridge]
  exact exp_pi_endpoint_le
    (⟨pi b, IsSelfAdjoint.of_nonneg (map_nonneg pi hb)⟩ : selfAdjoint (H →L[ℂ] H)) ξ η
end MathlibAnnex.Analysis.CStarAlgebra
