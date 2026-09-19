import Mathlib.Analysis.CStarAlgebra.GelfandDuality

/-!
# Characters separating closed ideals in commutative C-star algebras

Gelfand duality identifies a norm-closed ideal with the continuous
functions vanishing off its associated open set.  Consequently every
element outside such an ideal is detected by a character annihilating the
ideal.
-/

set_option autoImplicit false

open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

/-- A character separates an element from a norm-closed ideal of a
commutative unital complex C-star algebra. -/
theorem exists_character_annihilating_closedIdeal_of_not_mem
    {D : Type u} [CommCStarAlgebra D]
    (J : Ideal D) (hJclosed : IsClosed (J : Set D))
    {d : D} (hd : d ∉ J) :
    ∃ chi : WeakDual.characterSpace ℂ D,
      (∀ x : D, x ∈ J → chi x = 0) ∧ chi d ≠ 0 := by
  let e := gelfandStarTransform D
  let K : Ideal C(WeakDual.characterSpace ℂ D, ℂ) :=
    J.map e.toRingEquiv.toRingHom
  have he : Isometry e := gelfandTransform_isometry D
  have hKcarrier : (K : Set C(WeakDual.characterSpace ℂ D, ℂ)) =
      e '' (J : Set D) := by
    ext f
    rw [Set.mem_image]
    simp only [K, SetLike.mem_coe]
    rw [Ideal.mem_map_iff_of_surjective e.toRingEquiv.toRingHom e.surjective]
    constructor
    · rintro ⟨x, hx, hxf⟩
      exact ⟨x, hx, hxf⟩
    · rintro ⟨x, hx, hxf⟩
      exact ⟨x, hx, hxf⟩
  have hKclosed : IsClosed (K : Set C(WeakDual.characterSpace ℂ D, ℂ)) := by
    rw [hKcarrier]
    exact he.isClosedEmbedding.isClosedMap (J : Set D) hJclosed
  have hed_not : e d ∉ K := by
    intro hed
    have hed' : e d ∈ (K : Set C(WeakDual.characterSpace ℂ D, ℂ)) := hed
    rw [hKcarrier] at hed'
    obtain ⟨x, hx, heq⟩ := hed'
    apply hd
    simpa [he.injective heq] using hx
  have hed_not_vanish :
      e d ∉ ContinuousMap.idealOfSet ℂ (ContinuousMap.setOfIdeal K) := by
    rwa [ContinuousMap.idealOfSet_ofIdeal_isClosed hKclosed]
  obtain ⟨chi, hchiOutside, hdchi⟩ :=
    ContinuousMap.notMem_idealOfSet.mp hed_not_vanish
  refine ⟨chi, ?_, ?_⟩
  · intro x hx
    have hexK : e x ∈ K := by
      have : e x ∈ (e '' (J : Set D)) := ⟨x, hx, rfl⟩
      rwa [← hKcarrier] at this
    have hvanish := ContinuousMap.notMem_setOfIdeal.mp hchiOutside hexK
    exact hvanish
  · exact hdchi

end MathlibAnnex.Analysis.CStarAlgebra
