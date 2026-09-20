import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.ExponentialPath

set_option autoImplicit false
noncomputable section
namespace MathlibAnnex.Analysis.CStarAlgebra

variable {A : Type*} [CStarAlgebra A]

theorem unitary_commutator_product_le (u v : unitary A) (a : A) :
    ‖((v * u : unitary A) : A) * a - a * ((v * u : unitary A) : A)‖ ≤
      ‖(u : A) * a - a * (u : A)‖ +
        ‖(v : A) * a - a * (v : A)‖ := by
  have heq : ((v * u : unitary A) : A) * a - a * ((v * u : unitary A) : A) =
      (v : A) * ((u : A) * a - a * (u : A)) +
        ((v : A) * a - a * (v : A)) * (u : A) := by
    change ((v : A) * (u : A)) * a - a * ((v : A) * (u : A)) = _
    noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖(v : A) * ((u : A) * a - a * (u : A))‖ +
        ‖((v : A) * a - a * (v : A)) * (u : A)‖ := norm_add_le _ _
    _ = _ := by rw [CStarRing.norm_coe_unitary_mul, CStarRing.norm_mul_coe_unitary]

theorem unitary_conjugates_eq_comm (u : unitary A) (a : A) :
    ‖(u : A) * a * star (u : A) - a‖ =
      ‖(u : A) * a - a * (u : A)‖ ∧
    ‖star (u : A) * a * (u : A) - a‖ =
      ‖(u : A) * a - a * (u : A)‖ := by
  constructor
  · have heq : (u : A) * a * star (u : A) - a =
        ((u : A) * a - a * (u : A)) * star (u : A) := by
      have hunit : (u : A) * star (u : A) = 1 := u.property.2
      rw [sub_mul, mul_assoc, mul_assoc, hunit, mul_one]
    rw [heq]
    simpa using CStarRing.norm_mul_coe_unitary ((u : A) * a - a * (u : A)) (star u)
  · have heq : star (u : A) * a * (u : A) - a =
        star (u : A) * (a * (u : A) - (u : A) * a) := by
      have hunit : star (u : A) * (u : A) = 1 := u.property.1
      rw [mul_sub, ← mul_assoc, ← mul_assoc, hunit, one_mul, mul_assoc]
    rw [heq]
    calc
      _ = ‖a * (u : A) - (u : A) * a‖ := by
        simpa using CStarRing.norm_coe_unitary_mul (star u)
          (a * (u : A) - (u : A) * a)
      _ = _ := norm_sub_rev _ _

theorem unitary_conjugates_product_le (u v : unitary A) (a : A) :
    ‖((v * u : unitary A) : A) * a * star ((v * u : unitary A) : A) - a‖ ≤
      ‖(u : A) * a * star (u : A) - a‖ +
        ‖(v : A) * a * star (v : A) - a‖ ∧
    ‖star ((v * u : unitary A) : A) * a * ((v * u : unitary A) : A) - a‖ ≤
      ‖star (u : A) * a * (u : A) - a‖ +
        ‖star (v : A) * a * (v : A) - a‖ := by
  have h := unitary_commutator_product_le u v a
  obtain ⟨huF, huI⟩ := unitary_conjugates_eq_comm u a
  obtain ⟨hvF, hvI⟩ := unitary_conjugates_eq_comm v a
  obtain ⟨hvuF, hvuI⟩ := unitary_conjugates_eq_comm (v * u) a
  constructor
  · rw [hvuF, huF, hvF]
    exact h
  · rw [hvuI, huI, hvI]
    exact h

def unitaryPathProduct {u v : unitary A}
    (pU : Path 1 u) (pV : Path 1 v) : Path 1 (v * u) :=
  pU.trans {
    toFun := fun t => pV t * u
    continuous_toFun := by fun_prop
    source' := by rw [pV.source]; simp
    target' := by rw [pV.target]
  }

theorem unitaryPathProduct_both_bounds {u v : unitary A}
    (pU : Path 1 u) (pV : Path 1 v)
    (a : A) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hU : ∀ t : Set.Icc (0 : ℝ) 1,
      ‖(pU t : A) * a * star (pU t : A) - a‖ ≤ ε₁ ∧
      ‖star (pU t : A) * a * (pU t : A) - a‖ ≤ ε₁)
    (hV : ∀ t : Set.Icc (0 : ℝ) 1,
      ‖(pV t : A) * a * star (pV t : A) - a‖ ≤ ε₂ ∧
      ‖star (pV t : A) * a * (pV t : A) - a‖ ≤ ε₂)
    (t : Set.Icc (0 : ℝ) 1) :
    ‖(unitaryPathProduct pU pV t : A) * a *
        star (unitaryPathProduct pU pV t : A) - a‖ ≤ ε₁ + ε₂ ∧
    ‖star (unitaryPathProduct pU pV t : A) * a *
        (unitaryPathProduct pU pV t : A) - a‖ ≤ ε₁ + ε₂ := by
  unfold unitaryPathProduct
  rw [Path.trans_apply]
  split_ifs with ht
  · obtain ⟨hf, hi⟩ := hU ⟨2 * t, by constructor <;> nlinarith [t.2.1]⟩
    exact ⟨hf.trans (le_add_of_nonneg_right hε₂),
      hi.trans (le_add_of_nonneg_right hε₂)⟩
  · let s : Set.Icc (0 : ℝ) 1 :=
      ⟨2 * t - 1, by constructor <;> nlinarith [t.2.2, (not_le.1 ht).le]⟩
    change ‖((pV s * u : unitary A) : A) * a *
        star ((pV s * u : unitary A) : A) - a‖ ≤ ε₁ + ε₂ ∧
      ‖star ((pV s * u : unitary A) : A) * a *
        ((pV s * u : unitary A) : A) - a‖ ≤ ε₁ + ε₂
    obtain ⟨hprodF, hprodI⟩ := unitary_conjugates_product_le u (pV s) a
    have hu : pU (1 : Set.Icc (0 : ℝ) 1) = u := pU.target
    obtain ⟨huF, huI⟩ := hU 1
    rw [hu] at huF huI
    obtain ⟨hvF, hvI⟩ := hV s
    constructor
    · exact hprodF.trans (add_le_add huF hvF)
    · exact hprodI.trans (add_le_add huI hvI)

end MathlibAnnex.Analysis.CStarAlgebra
