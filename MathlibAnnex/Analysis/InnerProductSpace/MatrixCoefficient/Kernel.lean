import MathlibAnnex.Analysis.InnerProductSpace.MatrixCoefficient.Basic
import MathlibAnnex.Analysis.Normed.Module.DualKernel
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Kernels of matrix coefficients

All kernels below are the existing `ContinuousLinearMap.ker`, not a new geometric
structure-space definition. Pullbacks use actual continuous linear maps. The
algebraic span result includes finite and empty families, without a finite-dimensional
hypothesis on the operator space.
-/

set_option autoImplicit false

noncomputable section


namespace InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]

section Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]

@[simp]
theorem mem_ker_matrixCoefficient_iff (x : E) (y : F) (T : E →L[𝕜] F) :
    T ∈ (matrixCoefficient 𝕜 x y).ker ↔ inner 𝕜 y (T x) = 0 := Iff.rfl

theorem isClosed_ker_matrixCoefficient (x : E) (y : F) :
    IsClosed ((matrixCoefficient 𝕜 x y).ker : Set (E →L[𝕜] F)) := by
  change IsClosed ((matrixCoefficient 𝕜 x y) ⁻¹' ({0} : Set 𝕜))
  exact isClosed_singleton.preimage (matrixCoefficient 𝕜 x y).continuous

theorem ker_matrixCoefficient_smul_left {c : 𝕜} (hc : c ≠ 0) (x : E) (y : F) :
    (matrixCoefficient 𝕜 (c • x) y).ker = (matrixCoefficient 𝕜 x y).ker := by
  ext T
  simp only [mem_ker_matrixCoefficient_iff, map_smul, inner_smul_right,
    mul_eq_zero, hc, false_or]

theorem ker_matrixCoefficient_smul_right {c : 𝕜} (hc : c ≠ 0) (x : E) (y : F) :
    (matrixCoefficient 𝕜 x (c • y)).ker = (matrixCoefficient 𝕜 x y).ker := by
  ext T
  simp [mem_ker_matrixCoefficient_iff, inner_smul_left, hc]

/-- Matrix coefficient kernels pull back along an actual continuous linear map. -/
theorem ker_matrixCoefficient_comp
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
    (pi : V →L[𝕜] (E →L[𝕜] F)) (x : E) (y : F) :
    ((matrixCoefficient 𝕜 x y).comp pi).ker =
      (matrixCoefficient 𝕜 x y).ker.comap pi.toLinearMap := by
  ext v
  rfl

@[simp]
theorem mem_ker_matrixCoefficient_comp_iff
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
    (pi : V →L[𝕜] (E →L[𝕜] F)) (x : E) (y : F) (v : V) :
    v ∈ ((matrixCoefficient 𝕜 x y).comp pi).ker ↔ inner 𝕜 y (pi v x) = 0 := Iff.rfl

/-- Restriction to a subspace is a special case of kernel pullback. -/
theorem ker_matrixCoefficient_comp_subtypeL
    (S : Submodule 𝕜 (E →L[𝕜] F)) (x : E) (y : F) :
    ((matrixCoefficient 𝕜 x y).comp S.subtypeL).ker =
      (matrixCoefficient 𝕜 x y).ker.comap S.subtype := by
  ext T
  rfl

@[simp]
theorem mem_iInf_ker_matrixCoefficient_iff {ι : Sort*}
    (x : ι → E) (y : ι → F) (T : E →L[𝕜] F) :
    T ∈ (⨅ i, (matrixCoefficient 𝕜 (x i) (y i)).ker) ↔
      ∀ i, inner 𝕜 (y i) (T (x i)) = 0 := by
  simp only [Submodule.mem_iInf, mem_ker_matrixCoefficient_iff]

/-- Every algebraic linear combination vanishes on the common kernel. -/
theorem matrixCoefficient_span_apply_eq_zero {ι : Type*}
    (x : ι → E) (y : ι → F) {T : E →L[𝕜] F}
    (hT : ∀ i, matrixCoefficient 𝕜 (x i) (y i) T = 0)
    {f : (E →L[𝕜] F) →L[𝕜] 𝕜}
    (hf : f ∈ Submodule.span 𝕜 (Set.range fun i => matrixCoefficient 𝕜 (x i) (y i))) :
    f T = 0 := by
  let ev : ((E →L[𝕜] F) →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜 :=
    { toFun := fun g => g T
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hspan : Submodule.span 𝕜 (Set.range fun i => matrixCoefficient 𝕜 (x i) (y i)) ≤
      ev.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hT i
  exact hspan hf

/-- Replacing a family by its algebraic span does not change the common kernel.
In particular this applies to finite families; an empty family gives the top subspace. -/
theorem iInf_ker_span_matrixCoefficient {ι : Type*} (x : ι → E) (y : ι → F) :
    (⨅ f : Submodule.span 𝕜 (Set.range fun i => matrixCoefficient 𝕜 (x i) (y i)),
      f.val.ker) = ⨅ i, (matrixCoefficient 𝕜 (x i) (y i)).ker := by
  ext T
  simp only [Submodule.mem_iInf]
  constructor
  · intro h i
    exact h ⟨matrixCoefficient 𝕜 (x i) (y i), Submodule.subset_span ⟨i, rfl⟩⟩
  · intro h f
    exact matrixCoefficient_span_apply_eq_zero x y h f.property

end Seminormed

section Normed

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Nonzero coefficient vectors give proper kernels, without assuming a unit
or an irreducible representation. -/
theorem ker_matrixCoefficient_ne_top {x : E} {y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    (matrixCoefficient 𝕜 x y).ker ≠ ⊤ := by
  intro htop
  apply matrixCoefficient_ne_zero (𝕜 := 𝕜) hx hy
  ext T
  have hT : T ∈ (matrixCoefficient 𝕜 x y).ker := by
    rw [htop]
    trivial
  exact hT

/-- The kernel determines a nonzero coefficient up to a nonzero scalar.
This concerns the full operator space, not an assumed faithful image. -/
theorem ker_matrixCoefficient_eq_iff_exists_smul
    {x u : E} {y v : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    (matrixCoefficient 𝕜 x y).ker = (matrixCoefficient 𝕜 u v).ker ↔
      ∃ c : 𝕜, c ≠ 0 ∧ matrixCoefficient 𝕜 u v = c • matrixCoefficient 𝕜 x y :=
  ContinuousLinearMap.ker_eq_ker_iff_exists_ne_zero_smul (matrixCoefficient_ne_zero hx hy)

end Normed

end InnerProductSpace
