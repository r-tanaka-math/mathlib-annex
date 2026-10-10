/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Hilbert-basis index embeddings

An embedding of actual Hilbert-basis indices induces a linear isometry by the
orthogonal Hilbert sum. The target is complete; no operator ideal is used.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Cardinal

universe uF uH uK uI uJ

namespace HilbertBasis

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
variable {ι : Type uI} {κ : Type uJ}
variable [hK : CompleteSpace K]

include hK in
/-- Send a Hilbert basis into the subfamily specified by an embedding of indices.
The isometry is formed from Mathlib's orthogonal Hilbert sum, not an algebraic
linear extension on a purported Hamel basis. -/
def linearIsometryOfIndexEmbedding (b : HilbertBasis ι 𝕜 H)
    (c : HilbertBasis κ 𝕜 K) (f : ι ↪ κ) : H →ₗᵢ[𝕜] K :=
  ((c.orthonormal.comp f f.injective).orthogonalFamily.linearIsometry).comp
    b.repr.toLinearIsometry

/-- Evaluation on each original Hilbert-basis vector. -/
@[simp]
theorem linearIsometryOfIndexEmbedding_apply (b : HilbertBasis ι 𝕜 H)
    (c : HilbertBasis κ 𝕜 K) (f : ι ↪ κ) (i : ι) :
    b.linearIsometryOfIndexEmbedding c f (b i) = c (f i) := by
  classical
  change (c.orthonormal.comp f f.injective).orthogonalFamily.linearIsometry
      (b.repr (b i)) = c (f i)
  rw [b.repr_self, OrthogonalFamily.linearIsometry_apply_single]
  simp only [LinearIsometry.toSpanSingleton_apply, one_smul, Function.comp_apply]

include hK in
/-- Genuine lifted Hilbert-basis cardinal comparison supplies an isometric
embedding, with independent index and ambient universes. -/
theorem nonempty_linearIsometry_of_lift_mk_le (b : HilbertBasis ι 𝕜 H)
    (c : HilbertBasis κ 𝕜 K)
    (h : Cardinal.lift.{uJ} (#ι) ≤ Cardinal.lift.{uI} (#κ)) :
    Nonempty (H →ₗᵢ[𝕜] K) := by
  obtain ⟨f⟩ := Cardinal.lift_mk_le'.mp h
  exact ⟨b.linearIsometryOfIndexEmbedding c f⟩

end HilbertBasis
