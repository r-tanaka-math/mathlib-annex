/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.Normed.Module.Dual
import MathlibAnnex.Analysis.Normed.Module.DualKernel
import MathlibAnnex.Analysis.Normed.Module.L1Pair
import MathlibAnnex.LinearAlgebra.Dual.FiniteKernel

/-! # Pairs of continuous scalar-functional kernels

Algebraic factorization and l1 independence are separate hypotheses and results.
The proof bodies were moved unchanged from the R8 C*-coefficient application.
-/

set_option autoImplicit false
noncomputable section
open Set Metric

namespace ContinuousLinearMap

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- The two-kernel factorization for continuous scalar functionals. Continuity
of the factors is automatic because they are a finite linear combination of
the original continuous functionals. -/
theorem inf_ker_le_ker_iff_exists_smul_add_smul (f g h : V →L[𝕜] 𝕜) :
    f.ker ⊓ g.ker ≤ h.ker ↔ ∃ a b : 𝕜, h = a • f + b • g := by
  constructor
  · intro hk
    obtain ⟨a, b, hab⟩ :=
      (LinearMap.inf_ker_le_ker_iff_exists_smul_add_smul
        f.toLinearMap g.toLinearMap h.toLinearMap).1 hk
    refine ⟨a, b, ?_⟩
    ext x
    exact congrArg (fun l : V →ₗ[𝕜] 𝕜 => l x) hab
  · rintro ⟨a, b, rfl⟩ x hx
    change a * f x + b * g x = 0
    rw [show f x = 0 from hx.1, show g x = 0 from hx.2, mul_zero, mul_zero, add_zero]

/-- Distinctness of kernels follows from l1 independence, not from distinct
representation labels or an injectivity assertion about primitive ideals. -/
theorem ker_ne_of_norm_smul_add
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℂ V]
    (f g : StrongDual ℂ V) (hf : ‖f‖ = 1)
    (hl1 : ∀ a b : ℂ, ‖a • f + b • g‖ = ‖a‖ + ‖b‖) : f.ker ≠ g.ker := by
  have hf0 : f ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hf
    exact zero_ne_one hf
  intro hk
  obtain ⟨c, _, hc⟩ := (ker_eq_ker_iff_exists_ne_zero_smul hf0).1 hk
  have hz : (-c) • f + (1 : ℂ) • g = 0 := by
    rw [hc, one_smul]
    ext x
    change (-c) * f x + c * f x = 0
    ring
  have hn := hl1 (-c) 1
  rw [hz, norm_zero] at hn
  have hnon : 0 ≤ ‖c‖ := norm_nonneg _
  norm_num at hn
  linarith

end ContinuousLinearMap
