import BanachGeometry.WeakSequences.WeakTailGliding
import BanachGeometry.WeakSequences.SeparableDualSubsequence

/-! R6 Lemma 4.2 for a domain with separable dual: WeakTailGliding supplies
uniform tails for weakly Cauchy ℓ₁ sequences and SeparableDualSubsequence
supplies the required unit-ball subsequences. The theorem retains its
separable-dual assumption. Local execution evidence is external. -/

noncomputable section
open Filter TopologicalSpace
namespace BanachGeometry
namespace L1Tails

theorem tendsto_opNorm_tail_comp
    (V : ℕ → Type*) [∀ n, NormedAddCommGroup (V n)] [∀ n, NormedSpace ℝ (V n)]
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [SeparableSpace (B →L[ℝ] ℝ)] (T : B →L[ℝ] L1Sum V) :
    Tendsto (fun m => ‖(tail V m).comp T‖) atTop (nhds 0) :=
  WeakTailGliding.operator_norm_tails_of_domain_subsequences V T
    SeparableDual.unit_sequence_subsequence

end L1Tails
end BanachGeometry
