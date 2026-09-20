import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Analysis.Real.Cardinality

/-!
# Cardinality of a separable metric space

The countable coordinate embedding is reused from pinned Mathlib. No
separability assertion for operator spaces is used.
-/
set_option autoImplicit false
open Function TopologicalSpace
open scoped Cardinal
namespace MathlibAnnex.Topology
universe u v

/-- An injection into a set of cardinality at most the continuum gives the
same bound, with independent universes on the two sets. -/
theorem cardinalMk_le_continuum_of_injective
    {X : Type u} {Y : Type v} (f : X → Y) (hf : Injective f)
    (hY : #Y ≤ Cardinal.continuum) : #X ≤ Cardinal.continuum := by
  have hle := Cardinal.lift_mk_le_lift_mk_of_injective hf
  have hY' : Cardinal.lift.{u} (#Y) ≤ Cardinal.continuum := by
    simpa using hY
  simpa using hle.trans hY'

/-- A separable metric space has cardinality at most the continuum, including
empty spaces. The embedding is the existing Mathlib Hilbert-cube embedding. -/
theorem cardinalMk_le_continuum_of_separableSpace
    (X : Type u) [MetricSpace X] [SeparableSpace X] :
    #X ≤ Cardinal.continuum := by
  obtain ⟨f, hf⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
  let g : X → ℕ → ℝ := fun x n => (f x n : ℝ)
  have hg : Injective g := by
    intro x y hxy
    apply hf.injective
    funext n
    apply Subtype.ext
    exact congrFun hxy n
  apply cardinalMk_le_continuum_of_injective g hg
  simp [Cardinal.mk_arrow, Cardinal.mk_real]

end MathlibAnnex.Topology
