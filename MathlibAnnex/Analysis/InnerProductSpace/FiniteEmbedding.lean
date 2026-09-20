import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Finite-dimensional isometric embeddings into infinite Hilbert spaces

The construction chooses finitely many members of a Hilbert basis of the
target and sends a finite orthonormal basis of the source to them.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace MathlibAnnex.Analysis.InnerProductSpace

/-- Every finite-dimensional complex inner product space embeds linearly and
isometrically into an infinite-dimensional complete complex inner product
space. -/
theorem nonempty_linearIsometry_of_finiteDimensional_of_not_finiteDimensional
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (hF : ¬ FiniteDimensional ℂ F) : Nonempty (E →ₗᵢ[ℂ] F) := by
  classical
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℂ F
  have hs : s.Infinite := by
    intro hsfin
    letI : Fintype s := hsfin.fintype
    haveI : FiniteDimensional ℂ F :=
      b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
    exact hF inferInstance
  letI : Infinite s := hs.to_subtype
  let e : Fin (Module.finrank ℂ E) ↪ s :=
    Fin.valEmbedding.trans (Infinite.natEmbedding s)
  let u : Fin (Module.finrank ℂ E) → F := fun i => b (e i)
  have hu : Orthonormal ℂ u := b.orthonormal.comp e e.injective
  let v : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E :=
    stdOrthonormalBasis ℂ E
  let f : E →ₗ[ℂ] F := v.toBasis.constr ℂ u
  have hf : f ∘ v.toBasis = u := by
    funext i
    simp [f]
  exact ⟨f.isometryOfOrthonormal v.orthonormal (hf ▸ hu)⟩

end MathlibAnnex.Analysis.InnerProductSpace
