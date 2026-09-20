import MathlibAnnex.Analysis.Normed.Operator.WeakCompact

/-!
# Canonical normal extension of a dual functional

Every bounded functional on a normed space is canonically an element of the
triple dual.  Equivalently, it is a weak-star continuous functional on the
bidual.  This file records that construction, its exact norm, canonical
restriction, naturality, and simultaneous finite-family convergence.  It
does not install an algebra or order structure on a bidual.
-/

set_option autoImplicit false

open Filter Topology WeakDual

namespace MathlibAnnex.NormalExtension

open MathlibAnnex.WeakCompact

universe uK uX uY uI

noncomputable section

variable {𝕜 : Type uK} [RCLike 𝕜]
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
variable {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedSpace ℝ Y] [IsScalarTower ℝ 𝕜 Y]

/-- The canonical weak-star continuous extension of `phi : X*` to `X**`,
viewed with its norm topology as an element of `X***`. -/
def normalExtension (phi : StrongDual 𝕜 X) :
    StrongDual 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X)) :=
  NormedSpace.inclusionInDoubleDual 𝕜 (StrongDual 𝕜 X) phi

@[simp]
theorem normalExtension_apply (phi : StrongDual 𝕜 X)
    (omega : StrongDual 𝕜 (StrongDual 𝕜 X)) :
    normalExtension phi omega = omega phi := rfl

/-- The extension restricts exactly to the original functional on the
canonical copy of `X`. -/
@[simp]
theorem normalExtension_canonical (phi : StrongDual 𝕜 X) (x : X) :
    normalExtension phi (NormedSpace.inclusionInDoubleDual 𝕜 X x) =
      phi x := rfl

-- The outer `StrongDual` notation hides the semilinear-map parameters deeply
-- enough that instance search does not unfold the operator norm automatically.
local instance tripleDualNorm :
    Norm (StrongDual 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 X))) :=
  ContinuousLinearMap.hasOpNorm
    (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := StrongDual 𝕜 (StrongDual 𝕜 X)) (F := 𝕜)
    (σ₁₂ := RingHom.id 𝕜)

/-- Canonical normal extension preserves the operator norm. -/
@[simp]
theorem norm_normalExtension (phi : StrongDual 𝕜 X) :
    ‖normalExtension (𝕜 := 𝕜) (X := X) phi‖ = ‖phi‖ :=
  (NormedSpace.inclusionInDoubleDualLi
    (𝕜 := 𝕜) (E := StrongDual 𝕜 X)).norm_map phi

/-- On the bidual equipped with its weak-star topology, the canonical
extension is continuous. -/
theorem continuous_normalExtension (phi : StrongDual 𝕜 X) :
    Continuous fun omega : WeakDual 𝕜 (StrongDual 𝕜 X) ↦
      normalExtension phi (WeakDual.toStrongDual omega) := by
  exact WeakDual.eval_continuous phi

/-- Naturality under a bounded map: extending `psi ∘ T` is the same as
extending `psi` and applying `T**`. -/
@[simp]
theorem normalExtension_comp (T : X →L[𝕜] Y) (psi : StrongDual 𝕜 Y)
    (omega : StrongDual 𝕜 (StrongDual 𝕜 X)) :
    normalExtension (psi.comp T) omega =
      normalExtension psi (bidualMap T omega) := rfl

/-- Weak-star convergence implies convergence under every canonically
normal-extended functional. -/
theorem tendsto_normalExtension
    {I : Type uI} {l : Filter I}
    {omega : I → WeakDual 𝕜 (StrongDual 𝕜 X)}
    {eta : WeakDual 𝕜 (StrongDual 𝕜 X)}
    (homega : Tendsto omega l (𝓝 eta)) (phi : StrongDual 𝕜 X) :
    Tendsto
      (fun i ↦ normalExtension phi
        (WeakDual.toStrongDual (omega i))) l
      (𝓝 (normalExtension phi (WeakDual.toStrongDual eta))) :=
  (continuous_normalExtension phi).continuousAt.tendsto.comp homega

/-- A finite family of original dual functionals is evaluated
simultaneously along the same weak-star convergent net. -/
theorem tendsto_normalExtension_finset
    {I : Type uI} {l : Filter I}
    {omega : I → WeakDual 𝕜 (StrongDual 𝕜 X)}
    {eta : WeakDual 𝕜 (StrongDual 𝕜 X)}
    (homega : Tendsto omega l (𝓝 eta))
    (s : Finset (StrongDual 𝕜 X)) :
    ∀ phi ∈ s,
      Tendsto
        (fun i ↦ normalExtension phi
          (WeakDual.toStrongDual (omega i))) l
        (𝓝 (normalExtension phi (WeakDual.toStrongDual eta))) := by
  intro phi _
  exact tendsto_normalExtension homega phi

end

end MathlibAnnex.NormalExtension
