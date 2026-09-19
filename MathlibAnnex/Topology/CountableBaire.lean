import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Separation.Basic

/-!
# Isolated points in countable Baire spaces
-/

set_option autoImplicit false

open Set

namespace MathlibAnnex.Topology

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A nonempty countable T1 Baire space has an isolated point. -/
theorem exists_isOpen_singleton [Nonempty X] [Countable X] [T1Space X]
    [BaireSpace X] : ∃ x : X, IsOpen ({x} : Set X) := by
  obtain ⟨x, y, hy⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun x : X => ({x} : Set X))
    (fun _ => isClosed_singleton)
    (by ext y; simp)
  have hyx : y = x := mem_singleton_iff.mp (interior_subset hy)
  have hx : x ∈ interior ({x} : Set X) := hyx ▸ hy
  refine ⟨x, interior_eq_iff_isOpen.mp ?_⟩
  exact le_antisymm interior_subset (singleton_subset_iff.mpr hx)

end MathlibAnnex.Topology
