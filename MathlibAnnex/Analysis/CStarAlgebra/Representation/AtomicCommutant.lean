import MathlibAnnex.Analysis.CStarAlgebra.Intertwiner
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Atomic
import MathlibAnnex.Analysis.InnerProductSpace.HilbertSumCoordinates

/-!
# The commutant of an atomic sum joined by inter-block links

For an arbitrary dependent family of pairwise inequivalent irreducible
representations, a commuting operator has scalar diagonal blocks and zero
off-diagonal blocks.  Operators linking a selected unit vector in every block
to one root block force all diagonal scalars to agree.  The proof uses the
density of the arbitrary-index finite-support expansion `lp.hasSum_single`;
there is no finite or countable index restriction.
-/

set_option autoImplicit false

open scoped ENNReal lp InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {A : Type u} [CStarAlgebra A]
variable {I : Type v} {H : I → Type w}
variable [DecidableEq I]
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)] [∀ i, Nontrivial (H i)]

open MathlibAnnex.Analysis.InnerProductSpace

/-- The `(j,i)` block of an operator on a dependent Hilbert sum. -/
noncomputable def atomicBlock (T : HilbertSum H →L[ℂ] HilbertSum H)
    (i j : I) : H i →L[ℂ] H j :=
  (coordinateProjection j).comp (T.comp (coordinateEmbedding i))

@[simp]
theorem atomicBlock_apply (T : HilbertSum H →L[ℂ] HilbertSum H)
    (i j : I) (x : H i) :
    atomicBlock T i j x = T (coordinateEmbedding i x) j :=
  rfl

/-- Every matrix block of an operator in the atomic commutant is an
intertwiner between the corresponding fiber representations. -/
theorem intertwines_atomicBlock_of_inCommutant
    (pi : ∀ i, Representation A (H i))
    (T : HilbertSum H →L[ℂ] HilbertSum H)
    (hT : StarAlgHom.InCommutant (atomicRepresentation pi) T)
    (i j : I) :
    StarAlgHom.Intertwines (pi i) (pi j) (atomicBlock T i j) := by
  intro a
  apply ContinuousLinearMap.ext
  intro x
  have hcomm := congrArg
    (fun R : HilbertSum H →L[ℂ] HilbertSum H ↦ R (coordinateEmbedding i x))
    (hT a).eq
  have hcoord := congrArg (fun y : HilbertSum H ↦ y j) hcomm
  simpa [atomicBlock, ContinuousLinearMap.comp_apply,
    coordinateEmbedding_apply] using hcoord

/-- The atomic source and one vector-link from every block to a root block
have scalar commutant.  Link unitarity is not needed for this implication;
the source-derived model supplies it separately from rank-one completion. -/
theorem eq_algebraMap_of_atomic_of_links
    (pi : ∀ i, Representation A (H i))
    (hirr : ∀ i, StarAlgHom.IsIrreducible (pi i))
    (hno : ∀ ⦃i j : I⦄, i ≠ j → ∀ U : H i ≃ₗᵢ[ℂ] H j,
      ¬ StarAlgHom.Intertwines (pi i) (pi j) (U : H i →L[ℂ] H j))
    (o : I) (xi : ∀ i, H i) (hxi : ∀ i, ‖xi i‖ = 1)
    (L : I → HilbertSum H →L[ℂ] HilbertSum H)
    (hL : ∀ i, L i (coordinateEmbedding i (xi i)) =
      coordinateEmbedding o (xi o))
    (T : HilbertSum H →L[ℂ] HilbertSum H)
    (hTsource : StarAlgHom.InCommutant (atomicRepresentation pi) T)
    (hTlink : ∀ i, Commute T (L i)) :
    ∃ z : ℂ, T = algebraMap ℂ (HilbertSum H →L[ℂ] HilbertSum H) z := by
  have hblocks (i : I) : ∃ z : ℂ,
      atomicBlock T i i = algebraMap ℂ (H i →L[ℂ] H i) z := by
    apply StarAlgHom.eq_algebraMap_of_irreducible (pi i) (hirr i)
    intro a
    exact intertwines_atomicBlock_of_inCommutant pi T hTsource i i a
  choose z hz using hblocks
  have hoff {i j : I} (hij : i ≠ j) : atomicBlock T i j = 0 := by
    exact (intertwines_atomicBlock_of_inCommutant pi T hTsource i j).eq_zero_of_no_unitary
      (hirr i) (hirr j) (hno hij)
  have hsingle (i : I) (x : H i) :
      T (coordinateEmbedding i x) = coordinateEmbedding i (z i • x) := by
    apply lp.ext
    funext j
    by_cases hji : j = i
    · subst j
      have h := congrArg (fun R : H i →L[ℂ] H i ↦ R x) (hz i)
      simpa [atomicBlock, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.algebraMap_apply] using h
    · have h := congrArg (fun R : H i →L[ℂ] H j ↦ R x) (hoff (Ne.symm hji))
      simpa [atomicBlock, ContinuousLinearMap.comp_apply,
        coordinateEmbedding_apply, hji] using h
  have hzi (i : I) : z i = z o := by
    have hcomm := congrArg
      (fun R : HilbertSum H →L[ℂ] HilbertSum H ↦
        R (coordinateEmbedding i (xi i))) (hTlink i).eq
    change T (L i (coordinateEmbedding i (xi i))) =
      L i (T (coordinateEmbedding i (xi i))) at hcomm
    rw [hL, hsingle, hsingle,
      map_smul (coordinateEmbedding o) (z o) (xi o),
      map_smul (coordinateEmbedding i) (z i) (xi i),
      map_smul (L i) (z i) (coordinateEmbedding i (xi i)), hL] at hcomm
    have hcoord := congrArg (fun y : HilbertSum H ↦ y o) hcomm
    have hxine : xi o ≠ 0 := norm_ne_zero_iff.mp (by rw [hxi]; exact one_ne_zero)
    apply smul_left_injective ℂ hxine
    simpa [coordinateEmbedding_apply] using hcoord.symm
  refine ⟨z o, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  have hxsum : HasSum (fun i ↦ coordinateEmbedding i (x i)) x := by
    simpa [coordinateEmbedding_apply] using
      (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) x)
  have hTsum : HasSum (fun i ↦ T (coordinateEmbedding i (x i))) (T x) :=
    hxsum.mapL T
  have hzsum : HasSum (fun i ↦ z o • coordinateEmbedding i (x i)) (z o • x) :=
    hxsum.const_smul (z o)
  have hterms : (fun i ↦ T (coordinateEmbedding i (x i))) =
      (fun i ↦ z o • coordinateEmbedding i (x i)) := by
    funext i
    rw [hsingle, hzi]
    exact map_smul (coordinateEmbedding i) (z o) (x i)
  have hTsum' : HasSum (fun i ↦ z o • coordinateEmbedding i (x i)) (T x) :=
    hTsum.congr_fun fun i ↦ (congrFun hterms i).symm
  have heq : T x = z o • x := hTsum'.unique hzsum
  simpa [ContinuousLinearMap.algebraMap_apply] using heq

/-- A unital star representation with scalar bounded commutant is
topologically irreducible. -/
theorem StarAlgHom.isIrreducible_of_commutant_eq_algebraMap
    {B K : Type*} [CStarAlgebra B]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K] (rho : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hscalar : ∀ T : K →L[ℂ] K, StarAlgHom.InCommutant rho T →
      ∃ z : ℂ, T = algebraMap ℂ (K →L[ℂ] K) z) :
    StarAlgHom.IsIrreducible rho := by
  intro M hMclosed hMreduces
  letI : IsClosed (M : Set K) := hMclosed
  letI : CompleteSpace M := inferInstance
  letI : M.HasOrthogonalProjection := inferInstance
  let P : K →L[ℂ] K := M.starProjection
  have hPcomm : StarAlgHom.InCommutant rho P := by
    intro b
    change P.comp (rho b) = (rho b).comp P
    exact Submodule.Reduces.starProjection_commute (hMreduces b)
  obtain ⟨z, hz⟩ := hscalar P hPcomm
  by_cases hM : M = ⊥
  · exact Or.inl hM
  right
  obtain ⟨x, hxM, hxne⟩ := M.ne_bot_iff.mp hM
  have hPx : P x = x := by
    exact M.starProjection_eq_self_iff.mpr hxM
  have hzapply : P x = z • x := by
    simpa [ContinuousLinearMap.algebraMap_apply] using
      congrArg (fun T : K →L[ℂ] K ↦ T x) hz
  have hzx : z • x = (1 : ℂ) • x := by
    rw [← hzapply, hPx, one_smul]
  have hzone : z = 1 := smul_left_injective ℂ hxne hzx
  rw [← M.range_starProjection, show M.starProjection = 1 by simpa [P, hz, hzone]]
  exact LinearMap.range_eq_top.mpr fun y ↦ ⟨y, rfl⟩

end MathlibAnnex.Analysis.CStarAlgebra
