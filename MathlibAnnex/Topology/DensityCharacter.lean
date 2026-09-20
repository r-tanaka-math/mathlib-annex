import Mathlib.Topology.Bases
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Exact density character

`HasDensityCharacter X κ` means that κ is the attained minimum of cardinalities
of dense subsets of X. In particular, it is not merely the existence of a dense
subset with κ elements. For a normed space, the inherited topology is the norm
topology. This interface avoids converting a generator-count statement into a
density statement without proof.
-/

set_option autoImplicit false
open Set
open scoped Cardinal
namespace MathlibAnnex.Topology
universe u

/-- The minimum cardinality of a dense subset of X is exactly κ. -/
def HasDensityCharacter (X : Type u) [TopologicalSpace X] (κ : Cardinal.{u}) : Prop :=
  (∃ s : Set X, Dense s ∧ #s = κ) ∧ ∀ s : Set X, Dense s → κ ≤ #s

namespace HasDensityCharacter
variable {X : Type u} [TopologicalSpace X] {κ μ : Cardinal.{u}}

/-- The witnessing dense subset realizes the specified cardinal. -/
theorem exists_dense (h : HasDensityCharacter X κ) :
    ∃ s : Set X, Dense s ∧ #s = κ := h.1

/-- Every dense subset has cardinality at least the density character. -/
theorem le_cardinalMk (h : HasDensityCharacter X κ) (s : Set X) (hs : Dense s) :
    κ ≤ #s := h.2 s hs

/-- Exact density character is unique. -/
theorem unique (hκ : HasDensityCharacter X κ) (hμ : HasDensityCharacter X μ) : κ = μ := by
  obtain ⟨s, hs, hsc⟩ := hκ.1
  obtain ⟨t, ht, htc⟩ := hμ.1
  exact le_antisymm (htc ▸ hκ.2 t ht) (hsc ▸ hμ.2 s hs)

/-- A cardinal upper bound on X and the matching bound on every dense subset
identify both the cardinality and the density character. -/
theorem of_cardinalMk_le_of_forall_dense
    (hupper : #X ≤ κ) (hlower : ∀ s : Set X, Dense s → κ ≤ #s) :
    HasDensityCharacter X κ := by
  have hlow : κ ≤ #X := by simpa using hlower Set.univ dense_univ
  have hcard : #X = κ := le_antisymm hupper hlow
  exact ⟨⟨Set.univ, dense_univ, by simpa using hcard⟩, hlower⟩

end HasDensityCharacter
end MathlibAnnex.Topology
