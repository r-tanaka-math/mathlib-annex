import MathlibAnnex.Analysis.CStarAlgebra.ExactInterpolation
import Mathlib.Analysis.CStarAlgebra.Exponential

/-!
# Exponentials on invariant subspaces

An equality of bounded operators on an invariant subspace propagates through
their exponential power series.  This is the bridge used when an exact Kadison
witness lifts a finite-dimensional self-adjoint logarithm.
-/

set_option autoImplicit false

open NormedSpace
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

theorem exp_apply_eq_of_eqOn_of_mapsTo
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H]
    (S T : H →L[ℂ] H) (E : Submodule ℂ H)
    (hST : ∀ x : H, x ∈ E → S x = T x)
    (hT : Set.MapsTo T E E) {x : H} (hx : x ∈ E) :
    exp S x = exp T x := by
  have hTpow (n : ℕ) {y : H} (hy : y ∈ E) : (T ^ n) y ∈ E := by
    induction n with
    | zero => simpa using hy
    | succ n ih =>
        rw [pow_succ']
        exact hT ih
  have hpow (n : ℕ) {y : H} (hy : y ∈ E) : (S ^ n) y = (T ^ n) y := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ', pow_succ']
        change S ((S ^ n) y) = T ((T ^ n) y)
        rw [ih]
        exact hST _ (hTpow n hy)
  let ev : (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H x
  have hSsum := (expSeries_hasSum_exp (𝕂 := ℂ) S).map ev ev.continuous
  have hTsum := (expSeries_hasSum_exp (𝕂 := ℂ) T).map ev ev.continuous
  apply HasSum.unique hSsum
  convert hTsum using 1
  · funext n
    simp only [ev, Function.comp_apply, ContinuousLinearMap.apply_apply,
      expSeries_apply_eq, map_smul]
    rw [hpow n hx]
  · simp [ev]

/-- A star representation carries an exponential Kadison lift to the
exponential of the target operator on the finite invariant subspace. -/
theorem StarAlgHom.expUnitary_apply_eq_of_eqOn_of_mapsTo
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : selfAdjoint A)
    (T : H →L[ℂ] H) (E : Submodule ℂ H)
    (heq : ∀ x : H, x ∈ E → pi (h : A) x = T x)
    (hT : Set.MapsTo T E E) {x : H} (hx : x ∈ E) :
    pi (selfAdjoint.expUnitary h : A) x =
      NormedSpace.exp (Complex.I • T) x := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  letI : NormedAlgebra ℚ (H →L[ℂ] H) :=
    NormedAlgebra.restrictScalars ℚ ℂ (H →L[ℂ] H)
  rw [selfAdjoint.expUnitary_coe,
    NormedSpace.map_exp pi (map_continuous pi)]
  have hmap : pi (Complex.I • (h : A)) = Complex.I • pi (h : A) :=
    map_smul pi Complex.I (h : A)
  rw [hmap]
  apply exp_apply_eq_of_eqOn_of_mapsTo
      (Complex.I • pi (h : A)) (Complex.I • T) E
  · intro y hy
    simp [heq y hy]
  · intro y hy
    simp only [smul_apply]
    exact E.smul_mem Complex.I (hT hy)
  · exact hx

end MathlibAnnex.Analysis.CStarAlgebra
