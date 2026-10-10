module

public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Algebra.Module.LinearMap.DivisionRing

/-!
# Kernels of continuous scalar-valued linear functionals

These results do not depend on an inner product. The proofs are preserved from
an earlier matrix-coefficient module; geometric-structure and operator-theory
clients share this single implementation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Normalizing one functional at an actual vector determines the scalar in a
kernel inclusion. No topological or closed-range assumption is needed. -/
theorem eq_smul_of_ker_le_of_apply_eq_one
    {f g : V →L[𝕜] 𝕜} (hker : f.ker ≤ g.ker)
    {v : V} (hv : f v = 1) : g = g v • f := by
  ext w
  have hw : w - f w • v ∈ f.ker := by
    change f (w - f w • v) = 0
    rw [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
  have hgw := hker hw
  change g (w - f w • v) = 0 at hgw
  rw [map_sub, map_smul, smul_eq_mul] at hgw
  change g w = g v * f w
  exact (sub_eq_zero.mp hgw).trans (mul_comm _ _)

/-- A nonzero continuous scalar-valued functional admits no strictly larger
proper functional kernel. The scalar in this inclusion statement may be zero. -/
theorem ker_le_ker_iff_exists_smul
    {f g : V →L[𝕜] 𝕜} (hf : f ≠ 0) :
    f.ker ≤ g.ker ↔ ∃ c : 𝕜, g = c • f := by
  constructor
  · intro hker
    have hfl : f.toLinearMap ≠ 0 := by
      intro hzero
      apply hf
      ext w
      exact congrArg (fun q : V →ₗ[𝕜] 𝕜 => q w) hzero
    obtain ⟨v, hv⟩ := (LinearMap.surjective_iff_ne_zero.mpr hfl) 1
    exact ⟨g v, eq_smul_of_ker_le_of_apply_eq_one hker hv⟩
  · rintro ⟨c, rfl⟩ w hw
    change f w = 0 at hw
    change c • f w = 0
    rw [hw, smul_zero]

/-- Equality of the kernels of scalar-valued functionals is equality up to a
nonzero scalar, provided the first functional is nonzero. -/
theorem ker_eq_ker_iff_exists_ne_zero_smul
    {f g : V →L[𝕜] 𝕜} (hf : f ≠ 0) :
    f.ker = g.ker ↔ ∃ c : 𝕜, c ≠ 0 ∧ g = c • f := by
  constructor
  · intro hker
    obtain ⟨c, hc⟩ := (ker_le_ker_iff_exists_smul hf).mp hker.le
    refine ⟨c, ?_, hc⟩
    intro hzero
    have hg : g = 0 := by
      ext w
      have hw := congrArg (fun q : V →L[𝕜] 𝕜 => q w) hc
      simpa [hzero] using hw
    apply hf
    ext w
    have hgw : w ∈ g.ker := by
      change g w = 0
      rw [hg, ContinuousLinearMap.zero_apply]
    have hfw : w ∈ f.ker := hker.symm ▸ hgw
    exact hfw
  · rintro ⟨c, hc, rfl⟩
    ext w
    change f w = 0 ↔ c * f w = 0
    simp only [mul_eq_zero, hc, false_or]

end ContinuousLinearMap
