import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Hyperfinite concrete von Neumann algebras

The approximating algebras are unital star subalgebras of the given operator
algebra. Their union is dense for the standard strong operator topology.
The set of approximants allows arbitrary directed families; a sequence is a
particularly useful witness. No topology on the normed operator type is changed.
-/

set_option autoImplicit false

open Set Topology

namespace VonNeumannAlgebra

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "toSOT" =>
  ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H

/-- A concrete von Neumann algebra is hyperfinite if a nonempty, inclusion-directed
family of finite-dimensional unital star subalgebras has strongly dense union.
Using a set of subalgebras keeps the predicate independent of the universe of
a chosen index type. `isHyperfinite_of_directed` accepts indices in any universe. -/
def IsHyperfinite (M : VonNeumannAlgebra H) : Prop :=
  ∃ 𝒜 : Set (StarSubalgebra ℂ (H →L[ℂ] H)),
    𝒜.Nonempty ∧
    DirectedOn (· ≤ ·) 𝒜 ∧
    (∀ S ∈ 𝒜, S ≤ M.toStarSubalgebra ∧ FiniteDimensional ℂ S) ∧
    closure (toSOT '' {T | ∃ S ∈ 𝒜, T ∈ S}) =
      toSOT '' (M : Set (H →L[ℂ] H))

/-- A directed family, with an arbitrary index universe, witnesses hyperfiniteness. -/
theorem isHyperfinite_of_directed (M : VonNeumannAlgebra H)
    {ι : Type v} [Nonempty ι] (F : ι → StarSubalgebra ℂ (H →L[ℂ] H))
    (hF : Directed (· ≤ ·) F)
    (hFM : ∀ i, F i ≤ M.toStarSubalgebra)
    (hfinite : ∀ i, FiniteDimensional ℂ (F i))
    (hdense : closure (toSOT '' ⋃ i, (F i : Set (H →L[ℂ] H))) =
      toSOT '' (M : Set (H →L[ℂ] H))) : IsHyperfinite M := by
  refine ⟨Set.range F, ?_, ?_, ?_, ?_⟩
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨F i, ⟨i, rfl⟩⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := hF i j
    exact ⟨F k, ⟨k, rfl⟩, hik, hjk⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨hFM i, hfinite i⟩
  · have hunion : {T : H →L[ℂ] H | ∃ S ∈ Set.range F, T ∈ S} =
        ⋃ i, (F i : Set (H →L[ℂ] H)) := by
      ext T
      constructor
      · rintro ⟨S, ⟨i, rfl⟩, hT⟩
        exact Set.mem_iUnion.mpr ⟨i, hT⟩
      · intro hT
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hT
        exact ⟨F i, ⟨i, rfl⟩, hi⟩
    rw [hunion]
    exact hdense

/-- An increasing sequence of finite-dimensional unital star subalgebras with
strongly dense union is a hyperfinite approximation. -/
theorem isHyperfinite_of_monotone (M : VonNeumannAlgebra H)
    (F : ℕ → StarSubalgebra ℂ (H →L[ℂ] H))
    (hF : Monotone F)
    (hFM : ∀ n, F n ≤ M.toStarSubalgebra)
    (hfinite : ∀ n, FiniteDimensional ℂ (F n))
    (hdense : closure (toSOT '' ⋃ n, (F n : Set (H →L[ℂ] H))) =
      toSOT '' (M : Set (H →L[ℂ] H))) : IsHyperfinite M := by
  apply isHyperfinite_of_directed M F ?_ hFM hfinite hdense
  intro i j
  exact ⟨max i j, hF (le_max_left i j), hF (le_max_right i j)⟩

end VonNeumannAlgebra
