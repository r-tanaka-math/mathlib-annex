/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Tactic.Linarith

/-!
# Quotient duals and relative weak-star topology

Precomposition with the actual canonical quotient is a linear isometry onto
its annihilator. The reverse operator-norm inequality uses epsilon lifts
from `Submodule.Quotient.norm_mk_lt`, not norm-minimizing representatives.
The same map is a homeomorphism from the weak dual of the quotient onto the
annihilator with the subtype topology inherited from the ambient weak dual.

The construction does not require completeness or a proper subspace. It even
works for a nonclosed submodule when its quotient is equipped with the canonical
seminorm; for closed submodules this is the usual normed quotient. No assertion
that a nonclosed quotient is Hausdorff is made. In particular K = top and a zero
quotient need no exception and produce the zero annihilator.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace Submodule

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (K : Submodule 𝕜 E)

/-- The continuous annihilator, as a submodule of the strong dual. -/
def strongDualAnnihilator : Submodule 𝕜 (StrongDual 𝕜 E) where
  carrier := {f | ∀ x ∈ K, f x = 0}
  zero_mem' := by intro x hx; rfl
  add_mem' := by
    intro f g hf hg x hx
    change f x + g x = 0
    rw [hf x hx, hg x hx, add_zero]
  smul_mem' := by
    intro c f hf x hx
    change c • f x = 0
    rw [hf x hx, smul_zero]

@[simp]
theorem mem_strongDualAnnihilator (f : StrongDual 𝕜 E) :
    f ∈ K.strongDualAnnihilator ↔ ∀ x ∈ K, f x = 0 := Iff.rfl

/-- The same annihilator in the weak dual. Its inherited topology is relative weak-star. -/
def weakDualAnnihilator : Submodule 𝕜 (WeakDual 𝕜 E) :=
  K.strongDualAnnihilator.comap WeakDual.toStrongDual.toLinearMap

@[simp]
theorem mem_weakDualAnnihilator (f : WeakDual 𝕜 E) :
    f ∈ K.weakDualAnnihilator ↔ ∀ x ∈ K, f x = 0 := Iff.rfl

/-- Every annihilator is weak-star closed, even if the original submodule is not closed. -/
theorem isClosed_weakDualAnnihilator :
    IsClosed (K.weakDualAnnihilator : Set (WeakDual 𝕜 E)) := by
  change IsClosed {f : WeakDual 𝕜 E | ∀ x ∈ K, f x = 0}
  simp only [Set.setOf_forall]
  exact isClosed_biInter fun x hx => isClosed_eq (WeakDual.eval_continuous x) continuous_const

/-- The algebraic linear equivalence uses the actual continuous quotient and lift maps. -/
def quotientDualEquiv : StrongDual 𝕜 (E ⧸ K) ≃ₗ[𝕜] K.strongDualAnnihilator where
  toFun f := ⟨f.comp K.mkQL, by
    intro x hx
    change f (Submodule.Quotient.mk x) = 0
    rw [(Submodule.Quotient.mk_eq_zero K).2 hx, map_zero]⟩
  invFun g := K.liftQL g.val (by intro x hx; exact g.property x hx)
  left_inv f := by
    apply ContinuousLinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := K.mkQ_surjective y
    rfl
  right_inv g := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_add' f g := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    rfl

@[simp]
theorem quotientDualEquiv_apply (f : StrongDual 𝕜 (E ⧸ K)) :
    (K.quotientDualEquiv f).val = f.comp K.mkQL := rfl

/-- Evaluation of the descended functional on an actual quotient representative. -/
@[simp]
theorem quotientDualEquiv_symm_apply_mk (g : K.strongDualAnnihilator) (x : E) :
    K.quotientDualEquiv.symm g (K.mkQ x) = g.val x := rfl

/-- Epsilon representatives give equality, not just an upper bound, for the norm of pullback. -/
theorem norm_comp_mkQL (f : StrongDual 𝕜 (E ⧸ K)) : ‖f.comp K.mkQL‖ = ‖f‖ := by
  apply le_antisymm
  · apply (f.comp K.mkQL).opNorm_le_bound (norm_nonneg f)
    intro x
    exact (f.le_opNorm (K.mkQ x)).trans
      (mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le K x) (norm_nonneg f))
  · let M : ℝ := ‖f.comp K.mkQL‖
    have hM : 0 ≤ M := norm_nonneg _
    apply f.opNorm_le_bound hM
    intro y
    apply _root_.le_of_forall_pos_le_add
    intro ε hε
    have hp : 0 < M + 1 := by linarith
    obtain ⟨x, hx, hxn⟩ := Submodule.Quotient.norm_mk_lt y (div_pos hε hp)
    have hmul : M * (ε / (M + 1)) ≤ ε := by
      calc
        M * (ε / (M + 1)) ≤ (M + 1) * (ε / (M + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hε.le hp.le)
        _ = ε := by rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hp)]
    calc
      ‖f y‖ = ‖(f.comp K.mkQL) x‖ := by rw [← hx]; rfl
      _ ≤ M * ‖x‖ := (f.comp K.mkQL).le_opNorm x
      _ ≤ M * (‖y‖ + ε / (M + 1)) := mul_le_mul_of_nonneg_left hxn.le hM
      _ ≤ M * ‖y‖ + ε := by rw [mul_add]; exact add_le_add le_rfl hmul

/-- The dual of the quotient is linearly isometric to the continuous annihilator. -/
def quotientDualLinearIsometryEquiv :
    StrongDual 𝕜 (E ⧸ K) ≃ₗᵢ[𝕜] K.strongDualAnnihilator where
  toLinearEquiv := K.quotientDualEquiv
  norm_map' f := K.norm_comp_mkQL f

/-- The bundled isometry is precomposition with the canonical quotient, not an abstract choice. -/
@[simp]
theorem quotientDualLinearIsometryEquiv_apply_apply
    (f : StrongDual 𝕜 (E ⧸ K)) (x : E) :
    (K.quotientDualLinearIsometryEquiv f).val x = f (K.mkQ x) := rfl

@[simp]
theorem quotientDualLinearIsometryEquiv_symm_apply_mk
    (g : K.strongDualAnnihilator) (x : E) :
    K.quotientDualLinearIsometryEquiv.symm g (K.mkQ x) = g.val x := rfl

/-- The kernel of a pulled-back functional is the set-theoretic preimage of its kernel. -/
theorem preimage_zero_quotientDualLinearIsometryEquiv (f : StrongDual 𝕜 (E ⧸ K)) :
    ((K.quotientDualLinearIsometryEquiv f).val : E → 𝕜) ⁻¹' {0} =
      K.mkQ ⁻¹' ((f : E ⧸ K → 𝕜) ⁻¹' {0}) := rfl

/-- Change only the dual topologies, retaining the same underlying pullback and descent. -/
def quotientWeakDualEquiv : WeakDual 𝕜 (E ⧸ K) ≃ₗ[𝕜] K.weakDualAnnihilator where
  toFun f := ⟨StrongDual.toWeakDual ((K.quotientDualEquiv (WeakDual.toStrongDual f)).val),
    (K.quotientDualEquiv (WeakDual.toStrongDual f)).property⟩
  invFun g := StrongDual.toWeakDual
    (K.quotientDualEquiv.symm ⟨WeakDual.toStrongDual g.val, g.property⟩)
  left_inv f := by
    apply WeakDual.toStrongDual.injective
    change K.quotientDualEquiv.symm (K.quotientDualEquiv (WeakDual.toStrongDual f)) =
      WeakDual.toStrongDual f
    exact K.quotientDualEquiv.symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    apply WeakDual.toStrongDual.injective
    change (K.quotientDualEquiv
      (K.quotientDualEquiv.symm ⟨WeakDual.toStrongDual g.val, g.property⟩)).val =
        WeakDual.toStrongDual g.val
    exact congrArg Subtype.val
      (K.quotientDualEquiv.apply_symm_apply ⟨WeakDual.toStrongDual g.val, g.property⟩)
  map_add' f g := by
    apply Subtype.ext
    apply WeakDual.toStrongDual.injective
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply WeakDual.toStrongDual.injective
    apply ContinuousLinearMap.ext
    intro x
    rfl

/-- Forward weak-star evaluation uses only the quotient map. -/
@[simp]
theorem quotientWeakDualEquiv_apply_apply (f : WeakDual 𝕜 (E ⧸ K)) (x : E) :
    (K.quotientWeakDualEquiv f).val x = f (K.mkQ x) := rfl

/-- Reverse evaluation uses any representative, not a continuous or norm-minimizing section. -/
@[simp]
theorem quotientWeakDualEquiv_symm_apply_mk (g : K.weakDualAnnihilator) (x : E) :
    K.quotientWeakDualEquiv.symm g (K.mkQ x) = g.val x := rfl

/-- Precomposition is weak-star to relative weak-star continuous. -/
theorem continuous_quotientWeakDualEquiv : Continuous K.quotientWeakDualEquiv := by
  apply Continuous.subtype_mk
  apply WeakDual.continuous_of_continuous_eval
  intro x
  change Continuous (fun f : WeakDual 𝕜 (E ⧸ K) => f (K.mkQ x))
  exact WeakDual.eval_continuous (K.mkQ x)

/-- Descent is continuous for the relative weak-star topology on the annihilator. -/
theorem continuous_quotientWeakDualEquiv_symm : Continuous K.quotientWeakDualEquiv.symm := by
  apply WeakDual.continuous_of_continuous_eval
  intro y
  obtain ⟨x, rfl⟩ := K.mkQ_surjective y
  change Continuous (fun g : K.weakDualAnnihilator => g.val x)
  exact (WeakDual.eval_continuous x).comp continuous_subtype_val

/-- The actual weak-star to relative weak-star homeomorphism for a quotient dual. -/
def quotientWeakDualHomeomorph : WeakDual 𝕜 (E ⧸ K) ≃ₜ K.weakDualAnnihilator where
  toEquiv := K.quotientWeakDualEquiv.toEquiv
  continuous_toFun := K.continuous_quotientWeakDualEquiv
  continuous_invFun := K.continuous_quotientWeakDualEquiv_symm

/-- The norm-isometric and weak-star-homeomorphic realizations have identical underlying maps. -/
theorem toStrongDual_quotientWeakDualHomeomorph (f : WeakDual 𝕜 (E ⧸ K)) :
    WeakDual.toStrongDual (K.quotientWeakDualHomeomorph f).val =
      (K.quotientDualLinearIsometryEquiv (WeakDual.toStrongDual f)).val := rfl

/-- A representative formula for the inverse homeomorphism. -/
theorem quotientWeakDualHomeomorph_symm_apply_of_mkQ_eq
    (g : K.weakDualAnnihilator) {x : E} {y : E ⧸ K} (h : K.mkQ x = y) :
    K.quotientWeakDualHomeomorph.symm g y = g.val x := by
  subst y
  rfl

/-- No properness assumption is hidden in the annihilator: top gives zero. -/
@[simp]
theorem strongDualAnnihilator_top :
    (⊤ : Submodule 𝕜 E).strongDualAnnihilator = ⊥ := by
  ext f
  constructor
  · intro hf
    apply (Submodule.mem_bot 𝕜).2
    apply ContinuousLinearMap.ext
    intro x
    exact hf x (by trivial)
  · intro hf
    have hf0 : f = 0 := (Submodule.mem_bot 𝕜).1 hf
    subst f
    intro x hx
    rfl

/-- The zero submodule imposes no condition on a continuous functional. -/
@[simp]
theorem strongDualAnnihilator_bot :
    (⊥ : Submodule 𝕜 E).strongDualAnnihilator = ⊤ := by
  ext f
  constructor
  · intro hf
    trivial
  · intro hf x hx
    have hx0 : x = 0 := (Submodule.mem_bot 𝕜).1 hx
    rw [hx0, map_zero]

end Submodule
