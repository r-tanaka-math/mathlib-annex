import MathlibAnnex.Analysis.CStarAlgebra.Compression
import MathlibAnnex.Analysis.CStarAlgebra.CyclicTransport
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Adapters
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Atomic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional
import MathlibAnnex.Analysis.CStarAlgebra.Intertwiner
import MathlibAnnex.Analysis.InnerProductSpace.HilbertSumCoordinates
import MathlibAnnex.Analysis.InnerProductSpace.RankOne
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Fixed spaces of represented projection flags

Compression identifies the common fixed projection in its cyclic fiber and
excludes it in inequivalent irreducible fibers.  A coordinate argument then
identifies the common fixed space of an arbitrary dependent atomic sum.
-/

set_option autoImplicit false

open Filter Topology
open scoped ENNReal lp InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

open MathlibAnnex.Analysis.InnerProductSpace

universe u v w

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- For represented star projections, being fixed is equivalent to belonging
to the operator range, so the common fixed subspace is the infimum of the
ranges. -/
theorem commonFixedSubspace_eq_iInf_range
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (pi : Representation A H) (q : ℕ → A) (hq : ∀ n, IsStarProjection (q n)) :
    commonFixedSubspace (fun n ↦ pi (q n)) = ⨅ n, (pi (q n)).range := by
  ext x
  rw [mem_commonFixedSubspace_iff, Submodule.mem_iInf]
  apply forall_congr'
  intro n
  exact (LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap
      ((hq n).map pi).isIdempotentElem)).symm

/-- A supplied star projection with the represented common-fixed range is
the canonical common fixed projection. -/
theorem starProjection_eq_commonFixedProjection_of_range_iInf
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (pi : Representation A H) (q : ℕ → A) (hq : ∀ n, IsStarProjection (q n))
    (P : H →L[ℂ] H) (hP : IsStarProjection P)
    (hPrange : P.range = ⨅ n, (pi (q n)).range) :
    P = commonFixedProjection (fun n ↦ pi (q n)) := by
  obtain ⟨hProjection, hPeq⟩ :=
    isStarProjection_iff_eq_starProjection_range.mp hP
  have hrange : P.range = commonFixedSubspace (fun n ↦ pi (q n)) :=
    hPrange.trans (commonFixedSubspace_eq_iInf_range pi q hq).symm
  simpa only [commonFixedProjection, hrange] using hPeq

/-- A projection has to fix a unit vector when its vector state takes value
one on that projection. -/
theorem projection_apply_eq_self_of_vectorFunctional_eq_one
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (pi : Representation A H) (p : A) (hp : IsStarProjection p)
    (xi : H) (hxi : ‖xi‖ = 1)
    (hvalue : Representation.vectorFunctional pi xi p = 1) :
    pi p xi = xi := by
  have hcomp : IsStarProjection (1 - p) := hp.one_sub
  have hfunctional :
      Representation.vectorFunctional pi xi (star (1 - p) * (1 - p)) = 0 := by
    rw [hcomp.isSelfAdjoint.star_eq, hcomp.isIdempotentElem.eq, map_sub,
      Representation.vectorFunctional_one pi hxi, hvalue, sub_self]
  have hinner : inner ℂ (pi (1 - p) xi) (pi (1 - p) xi) = 0 := by
    rw [← Representation.vectorFunctional_star_mul]
    exact hfunctional
  have hzero : pi (1 - p) xi = 0 := inner_self_eq_zero.mp hinner
  have hsub : xi - pi p xi = 0 := by
    simpa [map_sub, map_one] using hzero
  exact (sub_eq_zero.mp hsub).symm

/-- A unit vector fixed by every member of a compressing self-adjoint flag
has exactly the limiting compression functional as its vector state. -/
theorem vectorFunctional_eq_of_compression_tendsto
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (pi : Representation A H) (q : ℕ → A) (phi : A →L[ℂ] ℂ)
    (hq_star : ∀ n, star (q n) = q n)
    (hcompression : ∀ b : A,
      Tendsto (fun n ↦ q n * b * q n - phi b • q n) atTop (nhds 0))
    (eta : H) (heta : ‖eta‖ = 1)
    (hfixed : ∀ n, pi (q n) eta = eta) :
    Representation.vectorFunctional pi eta = phi := by
  apply ContinuousLinearMap.ext
  intro b
  have hcoeff := inner_map_eq_of_compression_tendsto pi
    (Representation.continuousLinearMap pi).continuous q phi b eta eta
    hq_star hfixed hfixed (hcompression b)
  have hself : inner ℂ eta eta = 1 := by
    rw [inner_self_eq_norm_sq_to_K, heta]
    norm_num
  change inner ℂ eta (pi b eta) = phi b
  calc
    inner ℂ eta (pi b eta) = phi b * inner ℂ eta eta := hcoeff
    _ = phi b := by rw [hself, mul_one]

/-- In a cyclic realization of the compression state, the represented common
fixed projection is exactly the projection onto the cyclic vector. -/
theorem commonFixedProjection_eq_rankOne_of_dense_orbit
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (pi : Representation A H) (q : ℕ → A) (phi : A →L[ℂ] ℂ) (xi : H)
    (hq_star : ∀ n, star (q n) = q n)
    (hcompression : ∀ b : A,
      Tendsto (fun n ↦ q n * b * q n - phi b • q n) atTop (nhds 0))
    (hfixed : ∀ n, pi (q n) xi = xi)
    (hphi : ∀ b : A, phi b = inner ℂ xi (pi b xi))
    (hdense : DenseRange (StarAlgHom.orbitMap pi xi)) :
    commonFixedProjection (fun n ↦ pi (q n)) =
      InnerProductSpace.rankOne ℂ xi xi := by
  let Q : ℕ → H →L[ℂ] H := fun n ↦ pi (q n)
  let P := commonFixedProjection Q
  apply projection_eq_rankOne_of_dense_orbit pi phi P xi
  · exact (commonFixedProjection_eq_self_iff Q xi).2
      ((mem_commonFixedSubspace_iff Q xi).2 hfixed)
  · intro b
    exact commonFixedProjection_comp_map_comp_eq pi
      (Representation.continuousLinearMap pi).continuous q phi b hq_star
      (hcompression b)
  · exact hphi
  · exact hdense

/-- In an inequivalent irreducible realization, the common fixed projection
of a flag with a pure cyclic compression state must vanish. -/
theorem commonFixedProjection_eq_zero_of_no_unitary
    {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K]
    (pi : Representation A H) (rho : Representation A K)
    (q : ℕ → A) (phi : A →L[ℂ] ℂ) (xi : H)
    (hq_star : ∀ n, star (q n) = q n)
    (hcompression : ∀ b : A,
      Tendsto (fun n ↦ q n * b * q n - phi b • q n) atTop (nhds 0))
    (hxiState : ∀ b : A, inner ℂ xi (pi b xi) = phi b)
    (hxiCyclic : DenseRange (StarAlgHom.orbitMap pi xi))
    (hrho : StarAlgHom.IsIrreducible rho)
    (hno : ∀ U : H ≃ₗᵢ[ℂ] K,
      ¬ StarAlgHom.Intertwines pi rho (U : H →L[ℂ] K)) :
    commonFixedProjection (fun n ↦ rho (q n)) = 0 := by
  let Q : ℕ → K →L[ℂ] K := fun n ↦ rho (q n)
  let P := commonFixedProjection Q
  by_contra hP
  have hex : ∃ z : K, P z ≠ 0 := by
    by_contra h
    push_neg at h
    apply hP
    ext z
    exact h z
  obtain ⟨z, hz⟩ := hex
  let r : ℝ := ‖P z‖
  have hr : r ≠ 0 := norm_ne_zero_iff.mpr hz
  let eta : K := ((r⁻¹ : ℝ) : ℂ) • P z
  have heta_norm : ‖eta‖ = 1 := by
    dsimp only [eta]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hr]
  have heta_ne : eta ≠ 0 := norm_ne_zero_iff.mp (by rw [heta_norm]; exact one_ne_zero)
  have heta_fixed (n : ℕ) : rho (q n) eta = eta := by
    dsimp only [eta]
    rw [map_smul]
    exact congrArg (fun y : K ↦ ((r⁻¹ : ℝ) : ℂ) • y)
      (commonFixedProjection_apply_fixed Q n z)
  have heta_state (b : A) : inner ℂ eta (rho b eta) = phi b := by
    have h := inner_map_eq_of_compression_tendsto rho
      (Representation.continuousLinearMap rho).continuous q phi b eta eta
      hq_star heta_fixed heta_fixed (hcompression b)
    have hself : inner ℂ eta eta = 1 := by
      rw [inner_self_eq_norm_sq_to_K, heta_norm]
      norm_num
    calc
      inner ℂ eta (rho b eta) = phi b * inner ℂ eta eta := h
      _ = phi b := by rw [hself, mul_one]
  have hrho' : Representation.IsIrreducible rho :=
    (Representation.isIrreducible_iff_starAlgHom rho).2 hrho
  have hetaCyclic : DenseRange (StarAlgHom.orbitMap rho eta) :=
    Representation.denseRange_orbitMap_of_isIrreducible rho hrho' heta_ne
  obtain ⟨U, hU, -⟩ := StarAlgHom.existsUnique_pointedCyclicTransport
    pi rho xi eta hxiCyclic hetaCyclic (fun b ↦ (hxiState b).trans (heta_state b).symm)
  exact hno U hU.2.2

/-- If exactly one fiber of an arbitrary atomic sum has a nonzero common fixed
projection, its atomic common fixed space is the span of the corresponding
coordinate vector. -/
theorem iInf_range_atomicRepresentation_eq_span
    {I : Type v} {H : I → Type w}
    [DecidableEq I]
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    (pi : ∀ i, Representation A (H i))
    (q : ℕ → A) (hq : ∀ n, IsStarProjection (q n))
    (i : I) (xi : H i) (hxi : ‖xi‖ = 1)
    (hsame : commonFixedProjection (fun n ↦ pi i (q n)) =
      InnerProductSpace.rankOne ℂ xi xi)
    (hother : ∀ j, j ≠ i →
      commonFixedProjection (fun n ↦ pi j (q n)) = 0) :
    (⨅ n, (atomicRepresentation pi (q n)).range) =
      ℂ ∙ coordinateEmbedding i xi := by
  let Q (j : I) : ℕ → H j →L[ℂ] H j := fun n ↦ pi j (q n)
  have hxiCommon : xi ∈ commonFixedSubspace (Q i) := by
    rw [← commonFixedProjection_eq_self_iff]
    rw [hsame]
    simp [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, hxi]
  have hxiFixed : ∀ n, pi i (q n) xi = xi :=
    (mem_commonFixedSubspace_iff (Q i) xi).1 hxiCommon
  apply le_antisymm
  · intro x hx
    have hfixed (n : ℕ) : atomicRepresentation pi (q n) x = x := by
      rcases (Submodule.mem_iInf
        (fun n ↦ (atomicRepresentation pi (q n)).range)).mp hx n with ⟨y, rfl⟩
      change atomicRepresentation pi (q n)
          (atomicRepresentation pi (q n) y) = atomicRepresentation pi (q n) y
      rw [← ContinuousLinearMap.mul_apply, ← map_mul,
        (hq n).isIdempotentElem.eq]
    have hfiberFixed (j : I) : ∀ n, pi j (q n) (x j) = x j := by
      intro n
      exact congrArg (fun y : HilbertSum H ↦ y j) (hfixed n)
    have hfiberProjection (j : I) : commonFixedProjection (Q j) (x j) = x j :=
      (commonFixedProjection_eq_self_iff (Q j) (x j)).2
        ((mem_commonFixedSubspace_iff (Q j) (x j)).2 (hfiberFixed j))
    refine Submodule.mem_span_singleton.mpr ⟨inner ℂ xi (x i), ?_⟩
    apply lp.ext
    funext j
    by_cases hji : j = i
    · subst j
      have hi := hfiberProjection i
      rw [hsame] at hi
      simpa [coordinateEmbedding_apply, InnerProductSpace.rankOne_apply] using hi
    · have hj := hfiberProjection j
      rw [hother j hji] at hj
      have hxj : x j = 0 := by simpa using hj.symm
      simp [coordinateEmbedding_apply, lp.coeFn_single, hji, hxj]
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    apply (Submodule.mem_iInf
      (fun n ↦ (atomicRepresentation pi (q n)).range)).mpr
    intro n
    refine ⟨c • coordinateEmbedding i xi, ?_⟩
    calc
      atomicRepresentation pi (q n) (c • coordinateEmbedding i xi) =
          c • atomicRepresentation pi (q n) (coordinateEmbedding i xi) :=
        map_smul _ _ _
      _ = c • lp.single 2 i (pi i (q n) xi) := by
        rw [coordinateEmbedding_apply, atomicRepresentation_single]
      _ = c • coordinateEmbedding i xi := by
        rw [hxiFixed n, coordinateEmbedding_apply]

end MathlibAnnex.Analysis.CStarAlgebra
