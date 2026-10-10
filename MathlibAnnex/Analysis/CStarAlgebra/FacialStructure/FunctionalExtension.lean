/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Tactic

/-!
# Norm-preserving extension to the canonical unitization

This is a Hahn--Banach extension of a functional, not the canonical extension
of a state. No positivity or extremality of the extension is asserted.
The range of the actual isometric inclusion is used as the subspace.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- Any bounded functional extends to the canonical unitization without
changing its norm, including the zero functional. -/
theorem exists_extension_unitization_norm_eq (rho : StrongDual ℂ A) :
    ∃ g : StrongDual ℂ (Unitization ℂ A),
      (∀ a : A, g (Unitization.inr a) = rho a) ∧ ‖g‖ = ‖rho‖ := by
  let j : A →ₗ[ℂ] Unitization ℂ A :=
    (Unitization.inrNonUnitalStarAlgHom ℂ A : A →ₗ[ℂ] Unitization ℂ A)
  let M : Submodule ℂ (Unitization ℂ A) := LinearMap.range j
  let f : StrongDual ℂ M :=
    { toFun := fun z => rho z.1.snd
      map_add' := by intro z w; simp
      map_smul' := by intro c z; simp
      cont := rho.continuous.comp (Unitization.continuous_snd.comp continuous_subtype_val) }
  have hf (a : A) : f ⟨Unitization.inr a, LinearMap.mem_range_self j a⟩ = rho a := by
    change rho (Unitization.inr a).snd = rho a
    rw [Unitization.snd_inr]
  have hfnorm : ‖f‖ = ‖rho‖ := by
    apply le_antisymm
    · apply f.opNorm_le_bound (norm_nonneg rho)
      intro z
      obtain ⟨a, ha⟩ := z.property
      have hza : (z : Unitization ℂ A) = Unitization.inr a := ha.symm
      change ‖rho z.1.snd‖ ≤ ‖rho‖ * ‖(z : Unitization ℂ A)‖
      rw [hza, Unitization.snd_inr, Unitization.norm_inr]
      exact rho.le_opNorm a
    · apply rho.opNorm_le_bound (norm_nonneg f)
      intro a
      have h := f.le_opNorm ⟨Unitization.inr a, LinearMap.mem_range_self j a⟩
      rw [hf] at h
      change ‖rho a‖ ≤ ‖f‖ * ‖(Unitization.inr a : Unitization ℂ A)‖ at h
      simpa only [Unitization.norm_inr] using h
  obtain ⟨g, hg, hgnorm⟩ := exists_extension_norm_eq M f
  exact ⟨g, fun a => (hg ⟨Unitization.inr a, LinearMap.mem_range_self j a⟩).trans (hf a),
    hgnorm.trans hfnorm⟩

/-- A chosen norm-preserving extension; unlike `unitizationExtension` for
states, this choice need not be positive or unique. -/
def unitizationDualExtension (rho : StrongDual ℂ A) : StrongDual ℂ (Unitization ℂ A) :=
  (exists_extension_unitization_norm_eq rho).choose

@[simp]
theorem unitizationDualExtension_inr (rho : StrongDual ℂ A) (a : A) :
    unitizationDualExtension rho (Unitization.inr a) = rho a :=
  (exists_extension_unitization_norm_eq rho).choose_spec.1 a

@[simp]
theorem norm_unitizationDualExtension (rho : StrongDual ℂ A) :
    ‖unitizationDualExtension rho‖ = ‖rho‖ :=
  (exists_extension_unitization_norm_eq rho).choose_spec.2

theorem unitizationDualExtension_ne_zero {rho : StrongDual ℂ A} (hrho : rho ≠ 0) :
    unitizationDualExtension rho ≠ 0 := by
  intro h
  apply hrho
  ext a
  simpa only [h, ContinuousLinearMap.zero_apply] using
    (unitizationDualExtension_inr rho a).symm

end MathlibAnnex.Analysis.CStarAlgebra
