/- R6 Section 2: full public statements, assembled from the generic port.
The optimal Lipschitz constant is expressed by IsLeast, so both inequalities
are part of the statement. supported K is the isometric copy of F(K) in F(M).
These are composition wrappers, not new independent mathematical results.
Local execution status is recorded in the external qualification receipts.
-/
import BanachGeometry.Basic
import BanachGeometry.LipschitzFreeGeometry.CompactReduction
import BanachGeometry.LipschitzFreeGeometry.CompactHilbertWSC

noncomputable section
open scoped Topology NNReal
namespace BanachGeometry.LipschitzFreeProperties
open BanachGeometry.LipschitzFreeGeometry

universe uM uB uH

section Linearization
variable {M : Type uM} [MetricSpace M] [Zero M]
variable {B : Type uB} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- The operator norm is the least Lipschitz constant of g, with no chosen
nonoptimal bound substituted for Lip(g). This is R6 Proposition 2.1's norm identity. -/
theorem isLeast_lipschitzConstants_linearize (g : M → B) {L : ℝ≥0}
    (hg : LipschitzWith L g) (hg0 : g 0 = 0) :
    IsLeast {K : ℝ≥0 | LipschitzWith K g} ‖FreeSpace.linearize g‖₊ := by
  refine ⟨FreeSpace.lipschitz_linearize g hg hg0, ?_⟩
  intro K hK
  exact_mod_cast (FreeSpace.norm_linearize_le g hK hg0)

/-- R6 Proposition 2.1: existence, uniqueness, and the optimal norm together,
for an arbitrary pointed metric M and an arbitrary real Banach target B. -/
theorem existsUnique_linearization (g : M → B) {L : ℝ≥0}
    (hg : LipschitzWith L g) (hg0 : g 0 = 0) :
    ∃! T : FreeSpace.Space M →L[ℝ] B,
      (∀ x, T (FreeSpace.point x) = g x) ∧
        IsLeast {K : ℝ≥0 | LipschitzWith K g} ‖T‖₊ := by
  refine ⟨FreeSpace.linearize g,
    ⟨FreeSpace.linearize_point g hg hg0,
      isLeast_lipschitzConstants_linearize g hg hg0⟩, ?_⟩
  intro T hT
  exact (FreeSpace.linearize_unique g hg hg0 T hT.1).symm

end Linearization

/-- R6 Theorem 2.2, including the supremum norm bound in its stated form.
Weak nullity is used for boundedness of the original sequence only.
No weak convergence assertion about the approximating sequence is made. -/
theorem exists_compact_approximation_with_iSup_norm
    {M : Type uM} [MetricSpace M] [Zero M] [CompleteSpace M]
    (μ : ℕ → FreeSpace.Space M) (hμ : BanachGeometry.WeakNull μ)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ K : Set M, IsCompact K ∧ (0 : M) ∈ K ∧
      ∃ ν : ℕ → FreeSpace.Space M,
        (∀ n, ν n ∈ FreeSpace.supported K) ∧
        (∀ n, ‖μ n - ν n‖ < τ) ∧
        (∀ n, ‖ν n‖ ≤ (⨆ j, ‖μ j‖) + τ) := by
  classical
  have hw : WeakSequences.WeakNull μ := hμ
  obtain ⟨C, hC⟩ := (show WeakSequences.WeakCauchy μ from
    fun f => (hw f).cauchySeq).bounded
  have hbounded : BddAbove (Set.range (fun j => ‖μ j‖)) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact hC j
  have hsup (n : ℕ) : ‖μ n‖ ≤ ⨆ j, ‖μ j‖ := le_ciSup hbounded n
  obtain ⟨K, hK, hK0, happrox⟩ := FreeSpace.hasCompactReduction μ hw τ hτ
  choose ν hνK hνdist using happrox
  refine ⟨K, hK, hK0, ν, hνK, hνdist, ?_⟩
  intro n
  have hsplit : μ n + (ν n - μ n) = ν n := by abel
  calc
    ‖ν n‖ = ‖μ n + (ν n - μ n)‖ := congrArg norm hsplit.symm
    _ ≤ ‖μ n‖ + ‖ν n - μ n‖ := norm_add_le _ _
    _ = ‖μ n‖ + ‖μ n - ν n‖ := by rw [norm_sub_rev (ν n)]
    _ ≤ (⨆ j, ‖μ j‖) + τ := add_le_add (hsup n) (hνdist n).le

/-- R6 Theorem 2.3 for every complete real Hilbert H, without separability,
nontriviality, coordinate, or constructed-Base assumptions. Weak sequential
completeness is proved for this free space and is used by the concrete
QuantitativeHilbertData construction, rather than supplied as an extra input. -/
theorem hilbert_free_no_c0 {H : Type uH}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    ¬ BanachGeometry.ContainsLinearCopy BanachGeometry.ScalarC0 (FreeSpace.Space H) := by
  rintro ⟨T, a, ha, hT⟩
  exact WeakSequences.no_c0_of_wsc (CompactWSC.hilbert_free_wsc (H := H)) T a ha hT

end BanachGeometry.LipschitzFreeProperties
