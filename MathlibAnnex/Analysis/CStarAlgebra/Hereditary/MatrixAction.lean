/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Closedness of the algebra of scalar matrix actions

An ambient element has a scalar matrix action on a finite family of matrix
corners when its left and right products are the corresponding finite sums.
The set of these ambient elements is closed: both families of products define
a continuous map into a Hausdorff product topological vector space, and the
allowed scalar matrix actions form a finite-dimensional linear subspace there.

This uses the original ambient norm topology. The auxiliary function space
has the product topology; no operator norm or completeness assumption on the
corner is introduced. In particular, closedness needs neither injectivity nor
isometry nor the multiplication relations of the entry maps.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {ι : Type v} [Fintype ι]
variable {B : NonUnitalStarSubalgebra ℂ A}

/-- The actual left and right scalar-matrix action identities on a family of
linear matrix entries with coefficients in a specified nonunital subalgebra. -/
def ActsOnMatrixCorners (E : ι → ι → B →ₗ[ℂ] A)
    (a : A) (M : CStarMatrix ι ι ℂ) : Prop :=
  (∀ i j b, a * E i j b = ∑ k, M k i • E k j b) ∧
    (∀ i j b, E i j b * a = ∑ k, M j k • E i k b)

private def matrixCornerScalarAction (E : ι → ι → B →ₗ[ℂ] A) :
    CStarMatrix ι ι ℂ →ₗ[ℂ] ((ι → ι → B → A) × (ι → ι → B → A)) where
  toFun M := (fun i j b => ∑ k, M k i • E k j b,
    fun i j b => ∑ k, M j k • E i k b)
  map_add' M N := by
    apply Prod.ext
    · funext i j b
      change (∑ k, (M + N) k i • E k j b) =
        (∑ k, M k i • E k j b) + ∑ k, N k i • E k j b
      simp only [CStarMatrix.add_apply, add_smul, Finset.sum_add_distrib]
    · funext i j b
      change (∑ k, (M + N) j k • E i k b) =
        (∑ k, M j k • E i k b) + ∑ k, N j k • E i k b
      simp only [CStarMatrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r M := by
    apply Prod.ext
    · funext i j b
      change (∑ k, (r • M) k i • E k j b) = r • ∑ k, M k i • E k j b
      simp only [CStarMatrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
    · funext i j b
      change (∑ k, (r • M) j k • E i k b) = r • ∑ k, M j k • E i k b
      simp only [CStarMatrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

private def matrixCornerAmbientAction (E : ι → ι → B →ₗ[ℂ] A) (a : A) :
    (ι → ι → B → A) × (ι → ι → B → A) :=
  (fun i j b => a * E i j b, fun i j b => E i j b * a)

/-- The scalar-action condition is closed in the original ambient norm topology.
There is no norm or multiplication hypothesis on the entry maps: the only
finite-dimensional space in this argument is the scalar matrix parameter space. -/
theorem isClosed_setOf_exists_actsOnMatrixCorners (E : ι → ι → B →ₗ[ℂ] A) :
    IsClosed {a : A | ∃ M : CStarMatrix ι ι ℂ, ActsOnMatrixCorners E a M} := by
  classical
  let X := (ι → ι → B → A) × (ι → ι → B → A)
  let L : CStarMatrix ι ι ℂ →ₗ[ℂ] X := matrixCornerScalarAction E
  let R : A → X := matrixCornerAmbientAction E
  letI : FiniteDimensional ℂ (CStarMatrix ι ι ℂ) :=
    (CStarMatrix.ofMatrixₗ (R := ℂ) (m := ι) (n := ι) (A := ℂ)).finiteDimensional
  have hclosed : IsClosed (LinearMap.range L : Set X) :=
    (LinearMap.range L).closed_of_finiteDimensional
  have hcont : Continuous R := by
    change Continuous (fun a : A =>
      (fun i j (b : B) => a * E i j b, fun i j (b : B) => E i j b * a))
    fun_prop
  have hset : {a : A | ∃ M : CStarMatrix ι ι ℂ, ActsOnMatrixCorners E a M} =
      R ⁻¹' (LinearMap.range L : Set X) := by
    ext a
    constructor
    · rintro ⟨M, hleft, hright⟩
      refine ⟨M, Prod.ext ?_ ?_⟩
      · exact funext fun i => funext fun j => funext fun b => (hleft i j b).symm
      · exact funext fun i => funext fun j => funext fun b => (hright i j b).symm
    · rintro ⟨M, hM⟩
      refine ⟨M, ?_, ?_⟩
      · intro i j b
        exact (congrArg (fun z : X => z.1 i j b) hM).symm
      · intro i j b
        exact (congrArg (fun z : X => z.2 i j b) hM).symm
  rw [hset]
  exact hclosed.preimage hcont

end MathlibAnnex.Analysis.CStarAlgebra
