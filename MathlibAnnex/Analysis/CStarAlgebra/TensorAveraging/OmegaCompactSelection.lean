import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteAveragePoint
import MathlibAnnex.Analysis.LocallyConvex.CompactAnnihilator

/-!
# One Omega from finite central averages

Compactness is applied to the intersection of the fixed norm-one ball,
the all-test row closure and ALL exact matrix-moment constraints. The
selected point therefore cannot change when a source element, tensor test,
or vector is chosen. No separability or sequence is assumed.

The only new existence premise is HasFiniteCentralAverages, explicitly
assigned to source author A. It is not proved by this file or by a checker.
C04 source candidate, unbuilt.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Topology
open scoped InnerProductSpace
namespace MathlibAnnex.RepresentedCentralCorner
open MathlibAnnex.FiniteApproximation MathlibAnnex.CStarAlgebra.TensorAveraging
open MathlibAnnex.ProjectiveTensorProduct.Algebra
universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]
variable (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)

private noncomputable instance : NormedAddCommGroup (StrongDual ℂ (StrongDual ℂ (Tensor A))) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := StrongDual ℂ (Tensor A)) (F := ℂ)
    (σ₁₂ := RingHom.id ℂ)

private noncomputable instance : NormedSpace ℂ (StrongDual ℂ (StrongDual ℂ (Tensor A))) :=
  ContinuousLinearMap.toNormedSpace (E := StrongDual ℂ (Tensor A)) (F := ℂ)
    (σ₁₂ := RingHom.id ℂ)

/-- The exact moments are imposed before the centrality compactness step. -/
def momentFiber : Set (WeakDual ℂ (StrongDual ℂ (Tensor A))) :=
  {w | ∀ eta xi : H,
    w (matrixCoefficient A H pi.toNonUnitalStarAlgHom eta xi) = inner ℂ eta xi}

theorem isClosed_momentFiber : IsClosed (momentFiber pi) := by
  simp only [momentFiber, setOf_forall]
  apply isClosed_iInter
  intro eta
  apply isClosed_iInter
  intro xi
  exact isClosed_eq
    (WeakDual.eval_continuous (matrixCoefficient A H pi.toNonUnitalStarAlgHom eta xi))
    continuous_const

/-- A genuine compact feasible set in the fixed weak dual. -/
def omegaCompactSet : Set (WeakDual ℂ (StrongDual ℂ (Tensor A))) :=
  (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1) ∩
    (closure (canonicalImage (𝕜 := ℂ) (rowConvexSet A)) ∩ momentFiber pi)

theorem isCompact_omegaCompactSet : IsCompact (omegaCompactSet pi) :=
  by
    unfold omegaCompactSet
    have hc : IsClosed (closure (canonicalImage (𝕜 := ℂ) (rowConvexSet A))) :=
      isClosed_closure
    have hm := isClosed_momentFiber pi
    have hbase := WeakDual.isCompact_closedBall (𝕜 := ℂ)
      (E := StrongDual ℂ (Tensor A))
      (0 : StrongDual ℂ (StrongDual ℂ (Tensor A))) 1
    have hleft := hbase.inter_right hc
    have hall := hleft.inter_right hm
    simpa only [Set.inter_assoc] using hall

theorem averageTensorPoint_mem_omegaCompactSet
    (d : FiniteIsometryAverage (H →L[ℂ] H)) :
    StrongDual.toWeakDual (averageTensorPoint pi hpi d) ∈ omegaCompactSet pi := by
  refine ⟨?_, averageTensorPoint_rowClosure pi hpi d, ?_⟩
  · have hn : ‖averageTensorPoint pi hpi d‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro f
      simpa only [one_mul] using norm_averageTensorPoint_le_one pi hpi d f
    simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right,
      StrongDual.toStrongDual_toWeakDual] using hn
  · exact fun eta xi => averageTensorPoint_matrixCoefficient pi hpi d eta xi

/-- Complete compact selection from the exact finite-average boundary.
All three downstream properties are supplied by the SAME omega. -/
theorem exists_omega_of_finiteCentralAverages
    (hfinite : HasFiniteCentralAverages pi hpi) :
    ∃ omega : StrongDual ℂ (StrongDual ℂ (Tensor A)),
      ‖omega‖ ≤ 1 ∧ InWeakStarClosure omega (rowConvexSet A) ∧
      (∀ (a : A) (f : StrongDual ℂ (Tensor A)),
        omega (f.comp (leftAction ℂ A a)) = omega (f.comp (rightAction ℂ A a))) ∧
      (∀ eta xi : H,
        omega (matrixCoefficient A H pi.toNonUnitalStarAlgHom eta xi) = inner ℂ eta xi) := by
  have hf : ∀ tests : Finset (A × StrongDual ℂ (Tensor A)), ∀ epsilon : ℝ,
      0 < epsilon → ∃ w ∈ omegaCompactSet pi,
        ∀ af ∈ tests, ‖w (centralTest af.1 af.2)‖ < epsilon := by
    intro tests epsilon hepsilon
    obtain ⟨d, hd⟩ := hfinite tests epsilon hepsilon
    refine ⟨StrongDual.toWeakDual (averageTensorPoint pi hpi d),
      averageTensorPoint_mem_omegaCompactSet pi hpi d, ?_⟩
    intro af haf
    change ‖averageTensorPoint pi hpi d (centralTest af.1 af.2)‖ < epsilon
    simpa only [averageTensorPoint_centralTest] using hd af haf
  obtain ⟨w, hw, hz⟩ := MathlibAnnex.CompactAnnihilator.exists_mem_annihilating
    (omegaCompactSet pi) (isCompact_omegaCompactSet pi)
    (fun af : A × StrongDual ℂ (Tensor A) => centralTest af.1 af.2) hf
  refine ⟨w.toStrongDual, ?_, hw.2.1, ?_, hw.2.2⟩
  · simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right] using hw.1
  · intro a f
    have h := hz (a, f)
    change w.toStrongDual (f.comp (leftAction ℂ A a) - f.comp (rightAction ℂ A a)) = 0 at h
    rw [map_sub, sub_eq_zero] at h
    exact h

/-- The vector-moment form expected by the exact finite-row consumer. -/
theorem exists_omega_vector_of_finiteCentralAverages
    (hfinite : HasFiniteCentralAverages pi hpi) :
    ∃ omega : StrongDual ℂ (StrongDual ℂ (Tensor A)),
      InWeakStarClosure omega (rowConvexSet A) ∧
      (∀ (a : A) (f : StrongDual ℂ (Tensor A)),
        omega (f.comp (leftAction ℂ A a)) = omega (f.comp (rightAction ℂ A a))) ∧
      (∀ xi : H, omega (vectorMoment A H pi.toNonUnitalStarAlgHom xi) = (‖xi‖ ^ 2 : ℂ)) := by
  obtain ⟨omega, hn, hc, hb, hm⟩ := exists_omega_of_finiteCentralAverages pi hpi hfinite
  refine ⟨omega, hc, hb, fun xi => ?_⟩
  change omega (matrixCoefficient A H pi.toNonUnitalStarAlgHom xi xi) = _
  calc
    omega (matrixCoefficient A H pi.toNonUnitalStarAlgHom xi xi) = inner ℂ xi xi := hm xi xi
    _ = (‖xi‖ ^ 2 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast

end MathlibAnnex.RepresentedCentralCorner
