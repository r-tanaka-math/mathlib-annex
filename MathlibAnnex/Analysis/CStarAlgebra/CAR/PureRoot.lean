import MathlibAnnex.Analysis.CStarAlgebra.CAR.GNS
import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.KishimotoOzawaSakai

/-!
# Purity of the finite-stage root state

At each matrix stage, a normalized positive functional which takes value one on
the distinguished rank-one projection is forced to be the root vector state.
This gives a direct extreme-point proof, using the positive-functional GNS
Cauchy--Schwarz null-vector lemma rather than finite-dimensional spectral theory.
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder Convex

namespace MathlibAnnex.CStarAlgebra.CAR

@[simp]
theorem rootFunctional_mem_stateSpace (n : ℕ) :
    rootFunctional n ∈ MathlibAnnex.CStarAlgebra.stateSpace (Stage n) := by
  constructor
  · intro x hx
    exact rootLinear_nonneg n x hx
  · exact rootPositiveFunctional_one n

/-- A state supported with value one on the root projection is the root state. -/
theorem eq_rootFunctional_of_apply_rootProjection_eq_one (n : ℕ)
    (phi : Stage n →L[ℂ] ℂ) (hphi : phi ∈ MathlibAnnex.CStarAlgebra.stateSpace (Stage n))
    (hp : phi (rootProjection n) = 1) :
    phi = rootFunctional n := by
  let p : Stage n := rootProjection n
  let q : Stage n := 1 - p
  have hp_proj : IsStarProjection p := isStarProjection_rootProjection n
  have hq_proj : IsStarProjection q := hp_proj.one_sub
  let f : Stage n →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ phi.toLinearMap hphi.1
  have hf_apply (x : Stage n) : f x = phi x := rfl
  have hq_zero : f q = 0 := by
    rw [hf_apply, show q = 1 - p by rfl, map_sub, hphi.2, hp, sub_self]
  have hq_null : f (star q * q) = 0 := by
    rw [hq_proj.isSelfAdjoint.star_eq, hq_proj.isIdempotentElem.eq, hq_zero]
  have hleft (x : Stage n) : f (q * x) = 0 := by
    simpa [hq_proj.isSelfAdjoint.star_eq] using
      f.apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero hq_null x
  have hright (x : Stage n) : f (x * q) = 0 := by
    simpa using
      f.apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_right hq_null (star x)
  apply ContinuousLinearMap.ext
  intro x
  have hx_decomp : x = p * x * p + q * x + p * x * q := by
    dsimp only [q]
    noncomm_ring [hp_proj.isIdempotentElem.eq]
  calc
    phi x = f x := rfl
    _ = f (p * x * p + q * x + p * x * q) := by rw [← hx_decomp]
    _ = f (p * x * p) := by rw [map_add, map_add, hleft, hright, add_zero, add_zero]
    _ = f ((x 0 0) • p) := by rw [show p * x * p = (x 0 0) • p by
      exact rootProjection_mul_mul n x]
    _ = x 0 0 := by simp [map_smul, hf_apply, p, hp]
    _ = rootFunctional n x := rfl

/-- The distinguished root-coordinate state is pure at every finite matrix stage. -/
theorem isPureState_rootFunctional (n : ℕ) :
    MathlibAnnex.CStarAlgebra.IsPureState (Stage n) (rootFunctional n) := by
  rw [MathlibAnnex.CStarAlgebra.IsPureState, mem_extremePoints_iff_left]
  refine ⟨rootFunctional_mem_stateSpace n, ?_⟩
  intro phi₁ hphi₁ phi₂ hphi₂ hsegment
  rcases hsegment with ⟨a, b, ha, hb, hab, hcomb⟩
  let p : Stage n := rootProjection n
  let q : Stage n := 1 - p
  have hp_proj : IsStarProjection p := isStarProjection_rootProjection n
  have hq_nonneg : 0 ≤ q := hp_proj.one_sub.nonneg
  have hphi₁q : 0 ≤ phi₁ q := hphi₁.1 q hq_nonneg
  have hphi₂q : 0 ≤ phi₂ q := hphi₂.1 q hq_nonneg
  have hrootq : rootFunctional n q = 0 := by
    simp [q, p, rootProjection]
  have hsum : a • phi₁ q + b • phi₂ q = 0 := by
    have := congrArg (fun psi : Stage n →L[ℂ] ℂ => psi q) hcomb
    simpa [hrootq] using this
  have ha_nonneg : 0 ≤ a • phi₁ q := smul_nonneg ha.le hphi₁q
  have hb_nonneg : 0 ≤ b • phi₂ q := smul_nonneg hb.le hphi₂q
  have ha_nonpos : a • phi₁ q ≤ 0 := by
    rw [← hsum]
    simp only [le_add_iff_nonneg_right]
    exact hb_nonneg
  have ha_zero : a • phi₁ q = 0 := le_antisymm ha_nonpos ha_nonneg
  have hphi₁q_zero : phi₁ q = 0 := by
    exact (smul_eq_zero.mp ha_zero).resolve_left ha.ne'
  have hphi₁p : phi₁ p = 1 := by
    have h := hphi₁q_zero
    rw [show q = 1 - p by rfl, map_sub, hphi₁.2, sub_eq_zero] at h
    exact h.symm
  exact eq_rootFunctional_of_apply_rootProjection_eq_one n phi₁ hphi₁ hphi₁p

end MathlibAnnex.CStarAlgebra.CAR
