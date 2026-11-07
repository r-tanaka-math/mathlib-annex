/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Algebra.Module.LinearMap.DivisionRing
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic

/-!
# Two functional kernels and a finite linear combination

This is algebraic linear algebra over a field, with no topology, dimension,
independence, or nonzero assumptions on the functionals. The proof eliminates
one coordinate, including the case where that elimination is zero.
-/

set_option autoImplicit false

namespace LinearMap

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- A functional vanishing on two common kernels is a linear combination of
those functionals. Degenerate and zero functionals are included. -/
theorem inf_ker_le_ker_iff_exists_smul_add_smul (f g h : V →ₗ[𝕜] 𝕜) :
    f.ker ⊓ g.ker ≤ h.ker ↔ ∃ a b : 𝕜, h = a • f + b • g := by
  classical
  have one_kernel (p q : V →ₗ[𝕜] 𝕜) (hp : p ≠ 0)
      (hpq : p.ker ≤ q.ker) : ∃ c : 𝕜, q = c • p := by
    obtain ⟨u, hu⟩ := (LinearMap.surjective_iff_ne_zero.mpr hp) 1
    refine ⟨q u, ?_⟩
    ext x
    have hx : x - p x • u ∈ p.ker := by
      change p (x - p x • u) = 0
      simp only [map_sub, map_smul, smul_eq_mul, hu, mul_one, sub_self]
    have hh : q (x - p x • u) = 0 := hpq hx
    simp only [map_sub, map_smul, smul_eq_mul] at hh
    change q x = q u * p x
    exact (sub_eq_zero.mp hh).trans (mul_comm _ _)
  constructor
  · intro hker
    by_cases hf : f = 0
    · by_cases hg : g = 0
      · refine ⟨0, 0, ?_⟩
        ext x
        have hx : x ∈ f.ker ⊓ g.ker := by simp [hf, hg]
        have hh : h x = 0 := hker hx
        simpa using hh
      · obtain ⟨b, hb⟩ := one_kernel g h hg (fun x hx => hker ⟨by simp [hf], hx⟩)
        exact ⟨0, b, by simpa using hb⟩
    obtain ⟨u, hu⟩ := (LinearMap.surjective_iff_ne_zero.mpr hf) 1
    let k : V →ₗ[𝕜] 𝕜 := g - g u • f
    by_cases hk : k = 0
    · have hg : g = g u • f := sub_eq_zero.mp hk
      obtain ⟨a, ha⟩ := one_kernel f h hf (by
        intro x hx
        apply hker
        refine ⟨hx, ?_⟩
        change g x = 0
        rw [hg]
        change g u * f x = 0
        rw [show f x = 0 from hx, mul_zero])
      exact ⟨a, 0, by simpa using ha⟩
    obtain ⟨v, hv⟩ := (LinearMap.surjective_iff_ne_zero.mpr hk) 1
    let w : V := v - f v • u
    have hfw : f w = 0 := by simp [w, hu]
    have hgw : g w = 1 := by
      dsimp only [w]
      rw [map_sub, map_smul, smul_eq_mul]
      have hkval : g v - g u * f v = 1 := hv
      simpa only [mul_comm] using hkval
    refine ⟨h u - g u * h w, h w, ?_⟩
    ext x
    have hfx : f (x - f x • u - (g x - f x * g u) • w) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul, hu, hfw]
      ring
    have hgx : g (x - f x • u - (g x - f x * g u) • w) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul, hgw]
      ring
    have hh : h (x - f x • u - (g x - f x * g u) • w) = 0 := hker ⟨hfx, hgx⟩
    simp only [map_sub, map_smul, smul_eq_mul] at hh
    change h x = (h u - g u * h w) * f x + h w * g x
    linear_combination hh
  · rintro ⟨a, b, rfl⟩ x hx
    change a * f x + b * g x = 0
    rw [show f x = 0 from hx.1, show g x = 0 from hx.2, mul_zero, mul_zero, add_zero]

/-- The factorization gives membership in the actual two-functional span. -/
theorem mem_span_pair_of_inf_ker_le_ker (f g h : V →ₗ[𝕜] 𝕜)
    (hker : f.ker ⊓ g.ker ≤ h.ker) : h ∈ Submodule.span 𝕜 {f, g} := by
  obtain ⟨a, b, rfl⟩ := (inf_ker_le_ker_iff_exists_smul_add_smul f g h).1 hker
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_insert f {g}))
  · exact Submodule.smul_mem _ b
      (Submodule.subset_span (Set.mem_insert_of_mem f (Set.mem_singleton g)))

end LinearMap


namespace LinearMap

variable {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [Fintype ι]

/-- A functional vanishing on a finite intersection of kernels is a finite
linear combination. Empty and linearly dependent families are included. -/
theorem iInf_ker_le_ker_iff_exists_sum_smul (f : ι → V →ₗ[𝕜] 𝕜)
    (h : V →ₗ[𝕜] 𝕜) :
    (⨅ i, (f i).ker) ≤ h.ker ↔ ∃ c : ι → 𝕜, h = ∑ i, c i • f i := by
  classical
  constructor
  · intro hker
    let F : V →ₗ[𝕜] (ι → 𝕜) := LinearMap.pi f
    have hF : F.ker ≤ h.ker := by
      simpa only [F, LinearMap.ker_pi] using hker
    let p : F.range →ₗ[𝕜] 𝕜 :=
      (F.ker.liftQ h hF).comp F.quotKerEquivRange.symm.toLinearMap
    obtain ⟨g, hg⟩ := LinearMap.exists_extend p
    have hval (x : V) : g (F x) = h x := by
      have hx := LinearMap.congr_fun hg (⟨F x, ⟨x, rfl⟩⟩ : F.range)
      change g (F x) = (F.ker.liftQ h hF)
        (F.quotKerEquivRange.symm ⟨F x, ⟨x, rfl⟩⟩) at hx
      calc
        g (F x) = (F.ker.liftQ h hF)
            (F.quotKerEquivRange.symm ⟨F x, ⟨x, rfl⟩⟩) := hx
        _ = (F.ker.liftQ h hF) (F.ker.mkQ x) :=
          congrArg (F.ker.liftQ h hF) (F.quotKerEquivRange_symm_apply_image x ⟨x, rfl⟩)
        _ = h x := rfl
    refine ⟨fun i => g (Pi.single i 1), ?_⟩
    ext x
    have hdecomp : F x = ∑ i, (f i x) • Pi.single i (1 : 𝕜) := by
      ext i
      simp [F, Pi.single_apply]
    calc
      h x = g (F x) := (hval x).symm
      _ = ∑ i, f i x * g (Pi.single i 1) := by
        rw [hdecomp, map_sum]
        simp only [map_smul, smul_eq_mul]
      _ = (∑ i, g (Pi.single i 1) • f i) x := by
        simp [mul_comm]
  · rintro ⟨c, rfl⟩ x hx
    have hf (i : ι) : f i x = 0 := by
      exact ((Submodule.mem_iInf (fun i => (f i).ker)).mp hx) i
    change (∑ i, c i • f i) x = 0
    simp [hf]

/-- The finite-kernel criterion, in pointwise zero-incidence form. -/
theorem forall_eq_zero_imp_iff_exists_sum_smul (f : ι → V →ₗ[𝕜] 𝕜)
    (h : V →ₗ[𝕜] 𝕜) :
    (∀ x, (∀ i, f i x = 0) → h x = 0) ↔
      ∃ c : ι → 𝕜, h = ∑ i, c i • f i := by
  rw [← iInf_ker_le_ker_iff_exists_sum_smul]
  simp only [SetLike.le_def, Submodule.mem_iInf, LinearMap.mem_ker]

end LinearMap
