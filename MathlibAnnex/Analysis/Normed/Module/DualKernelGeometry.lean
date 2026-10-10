/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.Module.DualKernel
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# A third continuous-dual kernel through two distinct hyperplanes

These are statements about kernels of individual linear functionals. They do
not impose a submodule structure on a union of kernels or on an arbitrary
geometric-structure point. The third functional is the actual sum `f + g`.
-/

@[expose] public section

set_option autoImplicit false

open Set

universe u v

namespace NormedSpace

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Inclusion between kernels of two nonzero scalar functionals forces equality. -/
theorem preimage_zero_eq_of_subset_of_ne_zero_dual
    {f g : StrongDual 𝕜 E} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : (f : E → 𝕜) ⁻¹' {0} ⊆ (g : E → 𝕜) ⁻¹' {0}) :
    (f : E → 𝕜) ⁻¹' {0} = (g : E → 𝕜) ⁻¹' {0} := by
  have hker : f.ker ≤ g.ker := hfg
  obtain ⟨c, hc⟩ := (ContinuousLinearMap.ker_le_ker_iff_exists_smul hf).1 hker
  have hcne : c ≠ 0 := by
    intro hc0
    apply hg
    ext x
    change g x = 0
    have hv := congrArg (fun q : StrongDual 𝕜 E => q x) hc
    change g x = c * f x at hv
    simpa only [hc0, zero_mul] using hv
  have heq := (ContinuousLinearMap.ker_eq_ker_iff_exists_ne_zero_smul hf).2 ⟨c, hcne, hc⟩
  apply Set.ext
  intro x
  change x ∈ f.ker ↔ x ∈ g.ker
  rw [heq]

/-- Distinct nonzero functional kernels yield a nonzero sum functional, whose
kernel is different from each of the two and contains their intersection. -/
theorem add_dual_ne_zero_and_preimage_zero_ne_of_preimage_zero_ne
    {f g : StrongDual 𝕜 E} (hf : f ≠ 0) (hg : g ≠ 0)
    (hne : (f : E → 𝕜) ⁻¹' {0} ≠ (g : E → 𝕜) ⁻¹' {0}) :
    f + g ≠ 0 ∧
      ((f + g : StrongDual 𝕜 E) : E → 𝕜) ⁻¹' {0} ≠ (f : E → 𝕜) ⁻¹' {0} ∧
      ((f + g : StrongDual 𝕜 E) : E → 𝕜) ⁻¹' {0} ≠ (g : E → 𝕜) ⁻¹' {0} ∧
      ((f : E → 𝕜) ⁻¹' {0} ∩ (g : E → 𝕜) ⁻¹' {0}) ⊆
        ((f + g : StrongDual 𝕜 E) : E → 𝕜) ⁻¹' {0} := by
  have hleft (h : ∀ x : E, f x = 0 → (f + g) x = 0) : False := by
    apply hne
    apply preimage_zero_eq_of_subset_of_ne_zero_dual hf hg
    intro x hx
    change f x = 0 at hx
    have hsum := h x hx
    change f x + g x = 0 at hsum
    change g x = 0
    simpa only [hx, zero_add] using hsum
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hsum
    exact hleft fun x _ => congrArg (fun q : StrongDual 𝕜 E => q x) hsum
  · intro heq
    apply hleft
    intro x hx
    have hmem : x ∈ (f : E → 𝕜) ⁻¹' {0} := hx
    rw [← heq] at hmem
    exact hmem
  · intro heq
    apply hne
    symm
    apply preimage_zero_eq_of_subset_of_ne_zero_dual hg hf
    intro x hx
    change g x = 0 at hx
    have hmem : x ∈ (g : E → 𝕜) ⁻¹' {0} := hx
    rw [← heq] at hmem
    change f x + g x = 0 at hmem
    change f x = 0
    simpa only [hx, add_zero] using hmem
  · intro x hx
    change f x + g x = 0
    rw [show f x = 0 from hx.1, show g x = 0 from hx.2, add_zero]

end NormedSpace

namespace NormedSpace

section DualPair

variable {𝕜 : Type v} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Algebraic dimension at least two supplies actual continuous coordinate
functionals. Finite dimension is used only on the span of two independent
vectors, and Hahn--Banach extends both coordinates to the original space. -/
theorem exists_dual_pair_apply_eq_of_two_le_rank (hdim : 2 ≤ Module.rank 𝕜 E) :
    ∃ (x y : E) (f g : StrongDual 𝕜 E),
      f x = 1 ∧ f y = 0 ∧ g x = 0 ∧ g y = 1 := by
  classical
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank (R := 𝕜) (M := E) (n := 2) hdim
  let p : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range v)
  let b : Module.Basis (Fin 2) 𝕜 p := Module.Basis.span hv
  letI : FiniteDimensional 𝕜 p := b.finiteDimensional_of_finite
  let f₀ : StrongDual 𝕜 p := (b.coord 0).toContinuousLinearMap
  let g₀ : StrongDual 𝕜 p := (b.coord 1).toContinuousLinearMap
  obtain ⟨f, hf, _⟩ := exists_extension_norm_eq p f₀
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq p g₀
  refine ⟨(b 0 : E), (b 1 : E), f, g, ?_, ?_, ?_, ?_⟩
  · rw [hf (b 0)]
    change (b.repr (b 0)) 0 = 1
    simp
  · rw [hf (b 1)]
    change (b.repr (b 1)) 0 = 0
    simp
  · rw [hg (b 0)]
    change (b.repr (b 0)) 1 = 0
    simp
  · rw [hg (b 1)]
    change (b.repr (b 1)) 1 = 1
    simp

/-- The continuous coordinate witnesses give two different nonzero dual kernels,
without requiring the ambient normed space to be finite dimensional. -/
theorem exists_ne_zero_dual_preimage_zero_ne_of_two_le_rank
    (hdim : 2 ≤ Module.rank 𝕜 E) :
    ∃ f g : StrongDual 𝕜 E, f ≠ 0 ∧ g ≠ 0 ∧
      (f : E → 𝕜) ⁻¹' {0} ≠ (g : E → 𝕜) ⁻¹' {0} := by
  obtain ⟨x, y, f, g, hfx, hfy, hgx, hgy⟩ :=
    exists_dual_pair_apply_eq_of_two_le_rank hdim
  refine ⟨f, g, ?_, ?_, ?_⟩
  · intro hf
    have : (0 : 𝕜) = 1 := by simpa only [hf, ContinuousLinearMap.zero_apply] using hfx
    exact zero_ne_one this
  · intro hg
    have : (0 : 𝕜) = 1 := by simpa only [hg, ContinuousLinearMap.zero_apply] using hgy
    exact zero_ne_one this
  · intro hker
    have hy : y ∈ (f : E → 𝕜) ⁻¹' {0} := hfy
    rw [hker] at hy
    have hgy0 : g y = 0 := hy
    exact one_ne_zero (hgy.symm.trans hgy0)

end DualPair

end NormedSpace
