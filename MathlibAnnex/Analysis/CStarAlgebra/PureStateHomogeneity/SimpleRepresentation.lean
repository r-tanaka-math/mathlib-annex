import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.KishimotoOzawaSakai
import MathlibAnnex.Analysis.CStarAlgebra.CompactPreimage
import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Adapters
import MathlibAnnex.Analysis.CStarAlgebra.State.VectorApproximation
import MathlibAnnex.Analysis.CStarAlgebra.Cyclic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.FullImage
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteMatrixRow
import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
# Faithfulness and essentiality of simple-algebra representations

This separates the infinite-dimensional essential case from the remaining
finite-dimensional compact-image case. It does not supply local rows.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.CStarAlgebra

open MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem representation_injective_of_simple
    (hsimple : IsSimpleCStarAlgebra A)
    (pi : Representation A H) (hpi : pi.IsIrreducible) :
    Function.Injective pi := by
  let I : TwoSidedIdeal A := TwoSidedIdeal.ker pi.toRingHom
  have hclosed : IsClosed (I : Set A) := by
    have hset : (I : Set A) =
        (Representation.continuousLinearMap pi) ⁻¹' ({0} : Set (H →L[ℂ] H)) := by
      ext a
      change a ∈ I ↔ pi a = 0
      exact TwoSidedIdeal.mem_ker pi.toRingHom
    rw [hset]
    exact isClosed_singleton.preimage (Representation.continuousLinearMap pi).continuous
  rcases hsimple.2 I hclosed with hbot | htop
  · exact (TwoSidedIdeal.ker_eq_bot pi.toRingHom).mp hbot
  · have hzero : pi (1 : A) = 0 := by
      have h1 : (1 : A) ∈ I := by
        rw [htop]
        exact Set.mem_univ _
      exact (TwoSidedIdeal.mem_ker pi.toRingHom).mp h1
    have hne : (1 : H →L[ℂ] H) ≠ 0 := by
      letI : Nontrivial H := pi.nontrivial_of_isNonzero hpi.1
      exact one_ne_zero
    exact (hne (by simpa only [map_one] using hzero)).elim

theorem hasNoNonzeroCompactImage_representation_of_simple_infinite
    (hsimple : IsSimpleCStarAlgebra A)
    (hinfinite : ¬ FiniteDimensional ℂ A)
    (pi : Representation A H) (hpi : pi.IsIrreducible) :
    pi.HasNoNonzeroCompactImage := by
  letI : Nontrivial A := hsimple.1
  have hinj : Function.Injective pi :=
    representation_injective_of_simple hsimple pi hpi
  intro a ha
  have hz : a = 0 :=
    MathlibAnnex.CStarAlgebra.eq_zero_of_isCompactOperator_of_injective
      hinfinite hsimple.2 pi hinj ha
  rw [hz, map_zero]

/-- A nonzero irreducible representation of a finite-dimensional algebra
has finite-dimensional Hilbert space. Its algebraic orbit is already closed. -/
theorem finiteDimensional_representation_space_of_finiteDimensional_algebra
    [FiniteDimensional ℂ A]
    (pi : Representation A H) (hpi : pi.IsIrreducible) :
    FiniteDimensional ℂ H := by
  letI : Nontrivial H := pi.nontrivial_of_isNonzero hpi.1
  obtain ⟨ξ : H, hξ⟩ := exists_ne (0 : H)
  let R : Submodule ℂ H := LinearMap.range (StarAlgHom.orbitMap pi ξ)
  letI : FiniteDimensional ℂ R := LinearMap.finiteDimensional_range _
  have htop : R = ⊤ := by
    have hcyclic := StarAlgHom.cyclicSubspace_eq_top pi
      (Representation.isIrreducible_starAlgHom pi hpi) hξ
    change R.topologicalClosure = ⊤ at hcyclic
    rwa [Submodule.topologicalClosure_eq_self] at hcyclic
  exact LinearMap.finiteDimensional_of_surjective
    (StarAlgHom.orbitMap pi ξ) htop

/-- In the finite-dimensional simple case the represented image is the
whole operator algebra, the starting point for the compact-image route. -/
theorem representation_surjective_of_simple_finiteDimensional
    (_hsimple : IsSimpleCStarAlgebra A) [FiniteDimensional ℂ A]
    (pi : Representation A H) (hpi : pi.IsIrreducible) :
    Function.Surjective pi := by
  letI : Nontrivial H := pi.nontrivial_of_isNonzero hpi.1
  letI : FiniteDimensional ℂ H :=
    finiteDimensional_representation_space_of_finiteDimensional_algebra pi hpi
  exact Representation.surjective_of_irreducible_of_finiteDimensional pi hpi

/-- A finite-dimensional simple algebra has an actual normalized row with
exactly central row map. Its construction uses matrix units in its full
irreducible image, rather than an assumed invariant mean. -/
theorem representation_exists_finiteRow_of_simple_finiteDimensional
    (hsimple : IsSimpleCStarAlgebra A) [FiniteDimensional ℂ A]
    (pi : Representation A H) (hpi : pi.IsIrreducible)
    (ξ : H) (F : Finset A) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (x : Fin n → A),
      0 ≤ MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x ∧
      ‖MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x‖ ≤ 1 ∧
      pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) ξ = ξ ∧
      ∀ a ∈ F, ∀ z : A,
        ‖a * MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x z -
          MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x z * a‖ ≤ ε * ‖z‖ := by
  letI : Nontrivial A := hsimple.1
  letI : Nontrivial H := pi.nontrivial_of_isNonzero hpi.1
  letI : FiniteDimensional ℂ H :=
    finiteDimensional_representation_space_of_finiteDimensional_algebra pi hpi
  have hinj : Function.Injective pi :=
    representation_injective_of_simple hsimple pi hpi
  have hsurj : Function.Surjective pi :=
    representation_surjective_of_simple_finiteDimensional hsimple pi hpi
  obtain ⟨n, x, hq, hcentral⟩ :=
    MathlibAnnex.CStarAlgebra.TensorAveraging.exists_normalized_central_matrix_row
      pi hinj hsurj
  refine ⟨n, x, MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare_nonneg A x,
    ?_, ?_, ?_⟩
  · rw [hq, norm_one]
  · simp [hq]
  · intro a _ z
    rw [hcentral a z, sub_self, norm_zero]
    positivity

end MathlibAnnex.CStarAlgebra
