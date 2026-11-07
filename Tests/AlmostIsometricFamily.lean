import BanachGeometry.AlmostIsometric.Existence
import BanachGeometry.AlmostIsometric.Consequences
import BanachGeometry.LipschitzFreeSpace.PositiveTailLocality

/-! Fresh consumer: intended for actual kernel checking on resume. No check in
this file has run successfully during W01. It exercises an actual fixed family
and the metric exports, and requests compiled axiom inspection. -/

noncomputable section
open BanachGeometry

def realBanach : SeparableRealBanach where
  Carrier := ℝ
  normedAddCommGroup := inferInstance
  normedSpace := inferInstance
  completeSpace := inferInstance
  separableSpace := inferInstance
  nontrivial := inferInstance

def constantRealFamily : AlmostIsometricFamily where
  X := fun _ => realBanach
  Y := fun _ => realBanach
  bound := fun _ => 1
  one_le := fun _ => le_rfl
  tends_one := tendsto_const_nhds
  psi := fun _ => PointedBiLip.refl ℝ 1 le_rfl

#synth NormedAddCommGroup constantRealFamily.FixedY
#synth NormedSpace ℝ constantRealFamily.FixedX

example : branchIndexEquiv 0 none = 0 := rfl
example : branchIndexEquiv 0 (some 3) = 4 := by simp
example : branchIndexEquiv 2 (some 0) = 0 :=
  branchIndexEquiv_some_lt 2 0 (by norm_num)
example : branchIndexEquiv 2 (some 2) = 3 :=
  branchIndexEquiv_some_ge 2 2 le_rfl
example : (branchIndexEquiv 2).symm 2 = none := branchIndexEquiv_symm_at 2
example : (branchIndexEquiv 2).symm 4 = some 3 :=
  branchIndexEquiv_symm_succ 2 3 (by norm_num)

example (ε : ℝ) (hε : 0 < ε) :
    ∃ f : constantRealFamily.FixedX ≃ constantRealFamily.FixedY,
      f 0 = 0 ∧
      (∀ x y, ‖f x - f y‖ ≤ (1 + ε) * ‖x - y‖) ∧
      (∀ x y, ‖f.symm x - f.symm y‖ ≤ (1 + ε) * ‖x - y‖) :=
  constantRealFamily.fixed_spaces_almost_isometric ε hε

#check C0Sum.homogeneousLinearIsometryEquiv ScalarL2
#check QuantitativeHilbertData
#check HasQuantitativeHilbertModels
#check ExistsAlmostIsometricNonisomorphicPair

#print axioms branchIndex_left_inv
#print axioms branchIndex_right_inv
#print axioms l1_coordinate_summable
#print axioms l1Map_difference_le
#print axioms C0Sum.homogeneousLinearIsometryEquiv
#print axioms c0ReindexBiLip
#print axioms AlmostIsometricFamily.nearEquiv
#print axioms AlmostIsometricFamily.fixed_spaces_almost_isometric
