import MathlibAnnex.Analysis.Normed.Sphere.ModelTransport
import MathlibAnnex.Analysis.Normed.Sphere.Dimension
import MathlibAnnex.Analysis.Normed.Sphere.RadialExtension
import Mathlib.Analysis.Normed.Operator.LinearIsometry

noncomputable section
set_option autoImplicit false
open Set
universe u v

namespace MathlibAnnex.Sphere
namespace Internal
private noncomputable def coordinateEquivOfFinrankEq
    {n : ℕ} (X : Type u)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    (h : n = Module.finrank ℝ X) : (Fin n → ℝ) ≃L[ℝ] X :=
  ContinuousLinearEquiv.ofFinrankEq (by
    change Module.finrank ℝ (Fin n → ℝ) = Module.finrank ℝ X
    calc
      Module.finrank ℝ (Fin n → ℝ) = n :=
        (Module.finrank_fin_fun ℝ :
          Module.finrank ℝ (Fin n → ℝ) = n)
      _ = Module.finrank ℝ X := h)
private theorem nonempty_linearIsometryEquiv_of_sphereIsometryEquiv
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    [Nontrivial X] [Nontrivial Y]
    (Δ : (Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1)) : Nonempty (X ≃ₗᵢ[ℝ] Y) := by
  have hdim : Module.finrank ℝ X = Module.finrank ℝ Y :=
    finrank_eq Δ
  have hpos : 0 < Module.finrank ℝ X :=
    (Module.finrank_pos_iff (R := ℝ)).2 inferInstance
  let m : ℕ := Module.finrank ℝ X - 1
  have hmX : m + 1 = Module.finrank ℝ X := by
    dsimp [m]
    omega
  have hmY : m + 1 = Module.finrank ℝ Y := hmX.trans hdim
  let eX : (Fin (m + 1) → ℝ) ≃L[ℝ] X :=
    coordinateEquivOfFinrankEq X hmX
  let eY : (Fin (m + 1) → ℝ) ≃L[ℝ] Y :=
    coordinateEquivOfFinrankEq Y hmY
  exact nonempty_linearIsometryEquiv_of_coordinate_model Δ eX eY

end Internal
open Internal
private noncomputable def sphereIsoOfIsometrySurjective
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (f : (Metric.sphere (0 : X) 1) → (Metric.sphere (0 : Y) 1))
    (hf : Isometry f) (hsurj : Function.Surjective f) : (Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) where
  toEquiv := Equiv.ofBijective f ⟨hf.injective, hsurj⟩
  isometry_toFun := hf
noncomputable def isometryEquivOfLinearIsometryEquiv
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : X ≃ₗᵢ[ℝ] Y) : (Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) where
  toEquiv := {
    toFun := fun u => ⟨A u.1, by
      apply mem_sphere_zero_iff_norm.mpr
      calc
        ‖A u.1‖ = ‖u.1‖ := A.norm_map u.1
        _ = 1 := mem_sphere_zero_iff_norm.mp u.2⟩
    invFun := fun v => ⟨A.symm v.1, by
      apply mem_sphere_zero_iff_norm.mpr
      calc
        ‖A.symm v.1‖ = ‖v.1‖ := A.symm.norm_map v.1
        _ = 1 := mem_sphere_zero_iff_norm.mp v.2⟩
    left_inv := by
      intro u
      apply Subtype.ext
      exact A.symm_apply_apply u.1
    right_inv := by
      intro v
      apply Subtype.ext
      exact A.apply_symm_apply v.1
  }
  isometry_toFun := by
    refine Isometry.of_dist_eq ?_
    intro u v
    change dist (A (u : X)) (A (v : X)) = dist u v
    calc
      dist (A (u : X)) (A (v : X)) = dist (u : X) (v : X) :=
        A.isometry.dist_eq _ _
      _ = dist u v :=
        (isometry_subtype_coe :
          Isometry ((↑) : (Metric.sphere (0 : X) 1) → X)).dist_eq u v
theorem nonempty_linearIsometryEquiv_of_isometryEquiv_finiteDimensional
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (Δ : (Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1)) : Nonempty (X ≃ₗᵢ[ℝ] Y) := by
  have hdim : Module.finrank ℝ X = Module.finrank ℝ Y :=
    finrank_eq Δ
  by_cases hzeroX : Module.finrank ℝ X = 0
  · have hzeroY : Module.finrank ℝ Y = 0 := hdim.symm.trans hzeroX
    letI : Subsingleton X :=
      (Module.finrank_zero_iff (R := ℝ) (M := X)).mp hzeroX
    letI : Subsingleton Y :=
      (Module.finrank_zero_iff (R := ℝ) (M := Y)).mp hzeroY
    exact ⟨{
      toLinearEquiv := LinearEquiv.ofSubsingleton X Y
      norm_map' := by
        intro x
        have hx : x = 0 := Subsingleton.elim _ _
        subst x
        simp }⟩
  · have hposX : 0 < Module.finrank ℝ X := Nat.pos_of_ne_zero hzeroX
    have hposY : 0 < Module.finrank ℝ Y := by
      rw [← hdim]
      exact hposX
    letI : Nontrivial X :=
      Module.nontrivial_of_finrank_pos (R := ℝ) hposX
    letI : Nontrivial Y :=
      Module.nontrivial_of_finrank_pos (R := ℝ) hposY
    exact nonempty_linearIsometryEquiv_of_sphereIsometryEquiv Δ

/-- Function-form sphere-metric rigidity for all finite dimensions. -/
theorem nonempty_linearIsometryEquiv_of_isometry_surjective_finiteDimensional
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (f : (Metric.sphere (0 : X) 1) → (Metric.sphere (0 : Y) 1))
    (hf : Isometry f) (hsurj : Function.Surjective f) :
    Nonempty (X ≃ₗᵢ[ℝ] Y) :=
  nonempty_linearIsometryEquiv_of_isometryEquiv_finiteDimensional
    (sphereIsoOfIsometrySurjective f hf hsurj)

/-- The unit-sphere chord metric is a complete invariant in every finite dimension. -/
theorem nonempty_isometryEquiv_iff_nonempty_linearIsometryEquiv_finiteDimensional
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] :
    Nonempty ((Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1)) ↔ Nonempty (X ≃ₗᵢ[ℝ] Y) := by
  constructor
  · rintro ⟨Δ⟩
    exact nonempty_linearIsometryEquiv_of_isometryEquiv_finiteDimensional Δ
  · rintro ⟨A⟩
    exact ⟨isometryEquivOfLinearIsometryEquiv A⟩
theorem nonempty_linearIsometryEquiv_of_isometryEquiv_finiteDimensional_domain
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ X]
    (Δ : (Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1)) : Nonempty (X ≃ₗᵢ[ℝ] Y) := by
  letI : FiniteDimensional ℝ Y := finiteDimensional_codomain Δ
  exact nonempty_linearIsometryEquiv_of_isometryEquiv_finiteDimensional Δ

/-- Sphere-metric rigidity when the target ambient space is finite-dimensional. -/
theorem nonempty_linearIsometryEquiv_of_isometryEquiv_finiteDimensional_codomain
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y]
    (Δ : (Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1)) : Nonempty (X ≃ₗᵢ[ℝ] Y) := by
  letI : FiniteDimensional ℝ X := finiteDimensional_domain Δ
  exact nonempty_linearIsometryEquiv_of_isometryEquiv_finiteDimensional Δ

/-- Sphere-metric rigidity assuming that at least one ambient space is finite-dimensional. -/
theorem nonempty_linearIsometryEquiv_of_isometryEquiv_of_finiteDimensional
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (hfin : FiniteDimensional ℝ X ∨ FiniteDimensional ℝ Y)
    (Δ : (Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1)) : Nonempty (X ≃ₗᵢ[ℝ] Y) := by
  rcases hfin with hX | hY
  · letI : FiniteDimensional ℝ X := hX
    exact nonempty_linearIsometryEquiv_of_isometryEquiv_finiteDimensional_domain Δ
  · letI : FiniteDimensional ℝ Y := hY
    exact nonempty_linearIsometryEquiv_of_isometryEquiv_finiteDimensional_codomain Δ

/-- Function form of sphere-metric rigidity when one ambient space is finite-dimensional. -/
theorem nonempty_linearIsometryEquiv_of_isometry_surjective_of_finiteDimensional
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (hfin : FiniteDimensional ℝ X ∨ FiniteDimensional ℝ Y)
    (f : (Metric.sphere (0 : X) 1) → (Metric.sphere (0 : Y) 1))
    (hf : Isometry f) (hsurj : Function.Surjective f) :
    Nonempty (X ≃ₗᵢ[ℝ] Y) :=
  nonempty_linearIsometryEquiv_of_isometryEquiv_of_finiteDimensional hfin
    (sphereIsoOfIsometrySurjective f hf hsurj)

/-- If one ambient space is finite-dimensional, the unit-sphere chord metric
is a complete invariant of real normed spaces up to linear isometry. -/
theorem nonempty_isometryEquiv_iff_nonempty_linearIsometryEquiv_of_finiteDimensional
    {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (hfin : FiniteDimensional ℝ X ∨ FiniteDimensional ℝ Y) :
    Nonempty ((Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1)) ↔ Nonempty (X ≃ₗᵢ[ℝ] Y) := by
  constructor
  · rintro ⟨Δ⟩
    exact nonempty_linearIsometryEquiv_of_isometryEquiv_of_finiteDimensional hfin Δ
  · rintro ⟨A⟩
    exact ⟨isometryEquivOfLinearIsometryEquiv A⟩

end MathlibAnnex.Sphere
