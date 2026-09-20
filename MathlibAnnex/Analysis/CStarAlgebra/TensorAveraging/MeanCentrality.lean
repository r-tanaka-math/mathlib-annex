import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.OmegaFromMean

/-!
# Directional centrality adapter for represented mean assembly

`leftForm` acts on the FIRST factor by `a*x`; `rightForm` acts on the
SECOND by `y*a`.  Sampling uses `B(s⋆,s)`, so these are exactly the two
Haagerup invariance tests.  `IsInvariantOn` is an explicit unproved input
until an actual mean on the separately normal forms is constructed.
The extension's action naturality is also an explicit unproved Work/bridge
input.  The theorem below does not prove a universal Ω.
-/

set_option autoImplicit false
open scoped CStarAlgebra BoundedContinuousFunction
noncomputable section
namespace MathlibAnnex.CStarAlgebra.TensorAveraging
open MathlibAnnex.ProjectiveTensorProduct.Algebra

variable (M : Type*) [CStarAlgebra M] [Nontrivial M]

def leftForm (a : M) (B : ContinuousBilinearForm M) : ContinuousBilinearForm M :=
  B.comp (leftMul ℂ M a)

def rightForm (a : M) (B : ContinuousBilinearForm M) : ContinuousBilinearForm M :=
  (B.flip.comp (rightMul ℂ M a)).flip

theorem leftForm_apply (a : M) (B : ContinuousBilinearForm M) (x y : M) :
    leftForm M a B x y = B (a * x) y := rfl

theorem rightForm_apply (a : M) (B : ContinuousBilinearForm M) (x y : M) :
    rightForm M a B x y = B x (y * a) := rfl

/-- The exact identity required of an invariant mean on the specified
normal-form class; its existence is not asserted. -/
def IsInvariantOn (m : (Isometry M →ᵇ ℂ) →L[ℂ] ℂ)
    (N : Set (ContinuousBilinearForm M)) : Prop :=
  ∀ B ∈ N, ∀ a : M,
    m (sample M (leftForm M a B)) = m (sample M (rightForm M a B))

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem fromMean_central
    (ρ : A →⋆ₐ[ℂ] M)
    (E : StrongDual ℂ (Tensor A) →L[ℂ] ContinuousBilinearForm M)
    (m : (Isometry M →ᵇ ℂ) →L[ℂ] ℂ)
    (N : Set (ContinuousBilinearForm M))
    (hInv : IsInvariantOn M m N)
    (hNormal : ∀ f, E f ∈ N)
    (hLeft : ∀ (a : A) (f : StrongDual ℂ (Tensor A)),
      E (f.comp (leftAction ℂ A a)) = leftForm M (ρ a) (E f))
    (hRight : ∀ (a : A) (f : StrongDual ℂ (Tensor A)),
      E (f.comp (rightAction ℂ A a)) = rightForm M (ρ a) (E f)) :
    ∀ (a : A) (f : StrongDual ℂ (Tensor A)),
      fromMean A M E m (f.comp (leftAction ℂ A a)) =
        fromMean A M E m (f.comp (rightAction ℂ A a)) := by
  intro a f
  rw [fromMean_apply, fromMean_apply, hLeft, hRight]
  exact hInv (E f) (hNormal f) (ρ a)

end MathlibAnnex.CStarAlgebra.TensorAveraging
