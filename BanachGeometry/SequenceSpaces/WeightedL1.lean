import BanachGeometry.NoC0.NoC0Closure

open scoped ENNReal

/-! A positively weighted ℓ₁ sum in scaled coordinates x_j=λ_j a_j.
The carrier has its inherited ℓ₁ norm. The decoded coordinates range over
EXACTLY the raw weighted-summable sequences and its norm is Σ λ_j ‖a_j‖.
No second norm instance on a fixed carrier is introduced.
Execution evidence is recorded in the external receipts. -/
noncomputable section
namespace BanachGeometry
namespace WeightedL1
variable (V : ℕ → Type*) [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]
    («λ» : ℕ → ℝ) («hλ» : ∀ j, 0 < «λ» j)

abbrev Space (weights : ℕ → ℝ) := L1Sum V
def coord (x : Space V «λ») (j : ℕ) : V j := («λ» j)⁻¹ • x j

theorem coord_add (x y : Space V «λ») (j : ℕ) :
    coord V «λ» (x+y) j = coord V «λ» x j + coord V «λ» y j := smul_add _ _ _

theorem coord_smul (r : ℝ) (x : Space V «λ») (j : ℕ) :
    coord V «λ» (r • x) j = r • coord V «λ» x j := smul_comm _ _ _

include «hλ» in
theorem mul_norm_coord (x : Space V «λ») (j : ℕ) : «λ» j * ‖coord V «λ» x j‖ = ‖x j‖ := by
  rw [coord,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr («hλ» j)),
    ← mul_assoc,mul_inv_cancel₀ («hλ» j).ne',one_mul]

include «hλ» in
theorem norm_eq_tsum_weight_mul_norm_coord (x : Space V «λ») : ‖x‖ = ∑' j, «λ» j * ‖coord V «λ» x j‖ := by
  rw [l1_norm_eq_tsum]
  exact tsum_congr (fun j => (mul_norm_coord V «λ» «hλ» x j).symm)

include «hλ» in
theorem coordinates_summable (x : Space V «λ») : Summable (fun j => «λ» j * ‖coord V «λ» x j‖) := by
  simpa only [mul_norm_coord V «λ» «hλ»] using l1_summable x

def ofCoordinates (a : ∀ j, V j) (ha : Summable (fun j => «λ» j * ‖a j‖)) : Space V «λ» :=
  ⟨fun j => «λ» j • a j, by
    apply (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mpr
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos («hλ» _),ENNReal.toReal_one,Real.rpow_one] using ha⟩

@[simp] theorem coord_ofCoordinates (a : ∀ j, V j) (ha : Summable (fun j => «λ» j * ‖a j‖)) (j : ℕ) :
    coord V «λ» (ofCoordinates V «λ» «hλ» a ha) j = a j := by
  change («λ» j)⁻¹ • («λ» j • a j) = a j
  rw [smul_smul,inv_mul_cancel₀ («hλ» j).ne',one_smul]

@[simp] theorem ofCoordinates_coord (x : Space V «λ») :
    ofCoordinates V «λ» «hλ» (coord V «λ» x) (coordinates_summable V «λ» «hλ» x) = x := by
  apply lp.ext
  funext j
  change «λ» j • ((«λ» j)⁻¹ • x j) = x j
  rw [smul_smul,mul_inv_cancel₀ («hλ» j).ne',one_smul]

def rawEquiv : Space V «λ» ≃ {a : ∀ j, V j // Summable (fun j => «λ» j * ‖a j‖)} where
  toFun x := ⟨coord V «λ» x,coordinates_summable V «λ» «hλ» x⟩
  invFun a := ofCoordinates V «λ» «hλ» a.1 a.2
  left_inv := ofCoordinates_coord V «λ» «hλ»
  right_inv := by intro a; apply Subtype.ext; funext j; exact coord_ofCoordinates V «λ» «hλ» a.1 a.2 j

theorem no_c0 (hno : ∀ j, ¬ ContainsLinearCopy ScalarC0 (V j)) :
    ¬ ContainsLinearCopy ScalarC0 (Space V «λ») :=
  L1NoC0.no_c0_of_coordinate_no_c0 V hno

end WeightedL1
end BanachGeometry
