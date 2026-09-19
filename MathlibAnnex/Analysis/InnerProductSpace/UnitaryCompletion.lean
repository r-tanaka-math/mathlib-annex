import MathlibAnnex.Analysis.InnerProductSpace.ProjectionShell

/-!
# Exact unitary completion from finite defect relations

A fixed unitary conjugating every finite defect projection conjugates the
limiting defect projections.  If its complementary finite pieces converge
strongly to `S`, the remaining corner `V = U P` completes `S` exactly.
-/

set_option autoImplicit false

open Filter Topology
open scoped InnerProduct

namespace ContinuousLinearMap

variable {𝕜 E F : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Termwise shell relations sum to the corresponding finite relation. -/
theorem comp_partialSum_eq_of_comp_eq
    (e : E →L[𝕜] F) (D : ℕ → E →L[𝕜] E) (W : ℕ → E →L[𝕜] F)
    (h : ∀ n, e.comp (D n) = W n) (N : ℕ) :
    e.comp (partialSum D N) = partialSum W N := by
  ext x
  simp only [partialSum, map_sum, sum_apply,
    ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro n hn
  exact congrArg (fun T : E →L[𝕜] F ↦ T x) (h n)

/-- Termwise shells plus a finite telescoping identity give the finite
complement relation consumed by `unitaryCompletion_of_finite_relations`. -/
theorem comp_complement_eq_partialSum_of_shells
    (e : E →L[𝕜] F) (D : ℕ → E →L[𝕜] E) (W : ℕ → E →L[𝕜] F)
    (U : ℕ → Submodule 𝕜 E) [∀ N, (U N).HasOrthogonalProjection]
    (hshell : ∀ n, e.comp (D n) = W n)
    (htelescope : ∀ N, partialSum D N = 1 - (U N).starProjection) :
    ∀ N, e.comp (1 - (U N).starProjection) = partialSum W N := by
  intro N
  rw [← htelescope]
  exact comp_partialSum_eq_of_comp_eq e D W hshell N

/-- If a unitary's complementary corner has the prescribed final defect product,
then it conjugates the remaining projection onto the remaining final projection. -/
theorem unitary_conjugacy_of_complement_product
    (e : E ≃ₗᵢ[𝕜] F) (P : E →L[𝕜] E) (Q : F →L[𝕜] F)
    (A : E →L[𝕜] F)
    (hPadj : P† = P) (hPidem : P.comp P = P)
    (hA : (e : E →L[𝕜] F).comp (1 - P) = A)
    (hprod : A.comp (A†) = 1 - Q) :
    ((e : E →L[𝕜] F).comp P).comp ((e : E →L[𝕜] F)†) = Q := by
  have hAadj : A† = (1 - P).comp ((e : E →L[𝕜] F)†) := by
    have h := congrArg (fun T : E →L[𝕜] F ↦ T†) hA
    simpa [adjoint_comp, map_sub, hPadj] using h.symm
  have hPapply : ∀ x, P (P x) = P x := by
    intro x
    exact congrArg (fun T : E →L[𝕜] E ↦ T x) hPidem
  have hcompApply : ∀ x, (1 - P) ((1 - P) x) = (1 - P) x := by
    intro x
    simp [hPapply]
  ext y
  have hprodApply := congrArg (fun T : F →L[𝕜] F ↦ T y) hprod
  change A ((A†) y) = y - Q y at hprodApply
  rw [hAadj] at hprodApply
  change A ((1 - P) (((e : E →L[𝕜] F)†) y)) = y - Q y at hprodApply
  have hAApply : ∀ x, A x = e ((1 - P) x) := by
    intro x
    exact (congrArg (fun T : E →L[𝕜] F ↦ T x) hA).symm
  rw [hAApply, hcompApply] at hprodApply
  change e (P (((e : E →L[𝕜] F)†) y)) = Q y
  have heApply : e (((e : E →L[𝕜] F)†) y) = y := by
    rw [e.adjoint_eq_symm]
    exact e.apply_symm_apply y
  have hdecomp : e ((1 - P) (((e : E →L[𝕜] F)†) y)) =
      e (((e : E →L[𝕜] F)†) y) - e (P (((e : E →L[𝕜] F)†) y)) := by
    simp
  rw [hdecomp, heApply] at hprodApply
  exact sub_right_inj.mp hprodApply

/-- The raw termwise unitary shell relation and the two shell support identities
imply every finite unitary conjugacy relation. -/
theorem unitary_starProjection_conjugacy_of_projectionShells
    (e : E ≃ₗᵢ[𝕜] F) (W : ℕ → E →L[𝕜] F)
    (U : ℕ → Submodule 𝕜 E) (V : ℕ → Submodule 𝕜 F)
    [∀ n, (U n).HasOrthogonalProjection]
    [∀ n, (V n).HasOrthogonalProjection]
    (hU : Antitone U) (hV : Antitone V)
    (hU0 : U 0 = ⊤) (hV0 : V 0 = ⊤)
    (hInitial : ∀ n, ((W n)†).comp (W n) = Submodule.projectionShell U n)
    (hFinal : ∀ n, (W n).comp ((W n)†) = Submodule.projectionShell V n)
    (hUnitary : ∀ n, (e : E →L[𝕜] F).comp (Submodule.projectionShell U n) = W n) :
    ∀ N, ((e : E →L[𝕜] F).comp (U N).starProjection).comp
      ((e : E →L[𝕜] F)†) = (V N).starProjection := by
  intro N
  have hi := pairwiseInitialOrthogonal_of_projectionShells W U hU hInitial
  have hfiniteComplement : (e : E →L[𝕜] F).comp (1 - (U N).starProjection) =
      partialSum W N :=
    comp_complement_eq_partialSum_of_shells (e : E →L[𝕜] F)
      (Submodule.projectionShell U) W U hUnitary
      (Submodule.partialSum_projectionShell U hU0) N
  have hfiniteProduct : (partialSum W N).comp
      (partialSum (fun n ↦ (W n)†) N) = 1 - (V N).starProjection := by
    rw [partialSum_comp_adjoint_partialSum_eq W (Submodule.projectionShell V) hi hFinal,
      Submodule.partialSum_projectionShell V hV0]
  have hpartialAdjoint : (partialSum W N)† = partialSum (fun n ↦ (W n)†) N := by
    exact (partialSum_adjoint W N).symm
  apply unitary_conjugacy_of_complement_product e (U N).starProjection
    (V N).starProjection (partialSum W N)
  · exact (U N).starProjection_isSymmetric.clm_adjoint_eq
  · exact (U N).isIdempotentElem_starProjection
  · exact hfiniteComplement
  · rwa [hpartialAdjoint]

/-- Exact completion of a strong shell limit by the limiting defect corner.
The two finite hypotheses are precisely the finite complement and finite
conjugacy relations; all asserted limiting and corner identities are proved. -/
theorem unitaryCompletion_of_finite_relations
    (e : E ≃ₗᵢ[𝕜] F) (A : ℕ → E →L[𝕜] F) (S : E →L[𝕜] F)
    (U : ℕ → Submodule 𝕜 E) (V : ℕ → Submodule 𝕜 F)
    [∀ N, (U N).HasOrthogonalProjection]
    [∀ N, (V N).HasOrthogonalProjection]
    [(⨅ N, U N).HasOrthogonalProjection]
    [(⨅ N, V N).HasOrthogonalProjection]
    (hU : Antitone U) (hV : Antitone V)
    (hA : StronglyConverges A atTop S)
    (hfiniteComplement : ∀ N,
      (e : E →L[𝕜] F).comp (1 - (U N).starProjection) = A N)
    (hfiniteConjugacy : ∀ N,
      ((e : E →L[𝕜] F).comp (U N).starProjection).comp
        ((e : E →L[𝕜] F)†) = (V N).starProjection) :
    let P := (⨅ N, U N).starProjection
    let Q := (⨅ N, V N).starProjection
    let R := (e : E →L[𝕜] F).comp P
    (e : E →L[𝕜] F) = S + R ∧
      R = (e : E →L[𝕜] F).comp P ∧
      (R†).comp R = P ∧ R.comp (R†) = Q ∧
      R = (Q.comp R).comp P ∧
      (∀ x, x ∈ ⨅ N, U N ↔ e x ∈ ⨅ N, V N) := by
  dsimp only
  let P : E →L[𝕜] E := (⨅ N, U N).starProjection
  let Q : F →L[𝕜] F := (⨅ N, V N).starProjection
  let R : E →L[𝕜] F := (e : E →L[𝕜] F).comp P
  have hPlim := Submodule.stronglyConverges_starProjection_iInf U hU
  have hQlim := Submodule.stronglyConverges_starProjection_iInf V hV
  have hcompLimit : (e : E →L[𝕜] F).comp (1 - P) = S := by
    apply ext
    intro x
    apply tendsto_nhds_unique (l := (atTop : Filter ℕ))
    · exact ((StronglyConverges.const (ι := ℕ) (l := atTop)
        (1 : E →L[𝕜] E)).sub hPlim |>.comp_left (e : E →L[𝕜] F)) x
    · simpa [hfiniteComplement] using hA x
  have hconjLimit :
      ((e : E →L[𝕜] F).comp P).comp ((e : E →L[𝕜] F)†) = Q := by
    apply ext
    intro y
    apply tendsto_nhds_unique (l := (atTop : Filter ℕ))
    · exact (hPlim.comp_left (e : E →L[𝕜] F) |>.comp_right
        ((e : E →L[𝕜] F)†)) y
    · apply Filter.Tendsto.congr'
        (h := by simpa [Q] using hQlim y)
      filter_upwards [] with N
      exact (congrArg (fun T : F →L[𝕜] F ↦ T y)
        (hfiniteConjugacy N)).symm
  have hPadj : P† = P := by
    exact (⨅ N, U N).starProjection_isSymmetric.clm_adjoint_eq
  have hQadj : Q† = Q := by
    exact (⨅ N, V N).starProjection_isSymmetric.clm_adjoint_eq
  have hPidem : P.comp P = P := (⨅ N, U N).isIdempotentElem_starProjection
  have hQidem : Q.comp Q = Q := (⨅ N, V N).isIdempotentElem_starProjection
  have hleft : (e : E →L[𝕜] F) = S + R := by
    apply ext
    intro x
    have hx := congrArg (fun T : E →L[𝕜] F ↦ T x) hcompLimit
    change e ((1 - P) x) = S x at hx
    calc
      e x = e ((1 - P) x + P x) := by simp
      _ = e ((1 - P) x) + e (P x) := map_add e _ _
      _ = S x + R x := by rw [hx]; rfl
      _ = (S + R) x := rfl
  have hPapply : ∀ x, P (P x) = P x := by
    intro x
    exact congrArg (fun T : E →L[𝕜] E ↦ T x) hPidem
  have hRadj : R† = P.comp ((e : E →L[𝕜] F)†) := by
    simp [R, adjoint_comp, hPadj]
  have hinitial : (R†).comp R = P := by
    ext x
    rw [hRadj]
    change P (((e : E →L[𝕜] F)†) (e (P x))) = P x
    rw [LinearIsometryEquiv.adjoint_eq_symm]
    have he : (e.symm : F →L[𝕜] E) (e (P x)) = P x := by
      exact e.symm_apply_apply (P x)
    rw [he]
    exact hPapply x
  have hfinal : R.comp (R†) = Q := by
    ext y
    have hc := congrArg (fun T : F →L[𝕜] F ↦ T y) hconjLimit
    change e (P (((e : E →L[𝕜] F)†) y)) = Q y at hc
    rw [hRadj]
    change e (P (P (((e : E →L[𝕜] F)†) y))) = Q y
    rw [hPapply]
    exact hc
  have hsupport : R = (Q.comp R).comp P := by
    have hi : ∀ x, (R†) (R x) = P x := by
      intro x
      exact congrArg (fun T : E →L[𝕜] E ↦ T x) hinitial
    have hf : ∀ y, R ((R†) y) = Q y := by
      intro y
      exact congrArg (fun T : F →L[𝕜] F ↦ T y) hfinal
    ext x
    calc
      R x = R (P x) := by
        dsimp [R]
        rw [hPapply]
      _ = R ((R†) (R (P x))) := by rw [hi, hPapply]
      _ = Q (R (P x)) := hf _
      _ = ((Q.comp R).comp P) x := rfl
  have hmem : ∀ x, x ∈ ⨅ N, U N ↔ e x ∈ ⨅ N, V N := by
    intro x
    rw [← Submodule.starProjection_eq_self_iff, ← Submodule.starProjection_eq_self_iff]
    change P x = x ↔ Q (e x) = e x
    constructor
    · intro hx
      have hc := congrArg (fun T : F →L[𝕜] F ↦ T (e x)) hconjLimit
      simpa [P, Q, ContinuousLinearMap.comp_apply, hx] using hc.symm
    · intro hx
      have hc := congrArg (fun T : F →L[𝕜] F ↦ T (e x)) hconjLimit
      have : e (P x) = e x := by
        simpa [P, Q, ContinuousLinearMap.comp_apply, hx] using hc
      exact e.injective this
  exact ⟨hleft, rfl, hinitial, hfinal, hsupport, hmem⟩

/-- Complete raw-shell entry theorem.  Decreasing normalized projection families,
the two termwise support products, and the termwise unitary relation suffice to
construct the strong shell sum and its adjoint and to identify the complementary
unitary corner.  Finite products, finite conjugacy, and strong convergence are all
conclusions or internal derived facts, not hypotheses. -/
theorem exists_strongSums_unitaryCompletion_of_projectionShells
    (e : E ≃ₗᵢ[𝕜] F) (W : ℕ → E →L[𝕜] F)
    (U : ℕ → Submodule 𝕜 E) (V : ℕ → Submodule 𝕜 F)
    [∀ n, (U n).HasOrthogonalProjection]
    [∀ n, (V n).HasOrthogonalProjection]
    [(⨅ n, U n).HasOrthogonalProjection]
    [(⨅ n, V n).HasOrthogonalProjection]
    (hU : Antitone U) (hV : Antitone V)
    (hU0 : U 0 = ⊤) (hV0 : V 0 = ⊤)
    (hInitial : ∀ n, ((W n)†).comp (W n) = Submodule.projectionShell U n)
    (hFinal : ∀ n, (W n).comp ((W n)†) = Submodule.projectionShell V n)
    (hUnitary : ∀ n, (e : E →L[𝕜] F).comp (Submodule.projectionShell U n) = W n) :
    ∃ S : E →L[𝕜] F, ∃ T : F →L[𝕜] E,
      StronglyConverges (partialSum W) atTop S ∧
      StronglyConverges (partialSum fun n ↦ (W n)†) atTop T ∧
      ‖S‖ ≤ 1 ∧ ‖T‖ ≤ 1 ∧ T = S† ∧
      (S†).comp S = 1 - (⨅ n, U n).starProjection ∧
      S.comp (S†) = 1 - (⨅ n, V n).starProjection ∧
      (let P := (⨅ n, U n).starProjection
       let Q := (⨅ n, V n).starProjection
       let R := (e : E →L[𝕜] F).comp P
       (e : E →L[𝕜] F) = S + R ∧
         R = (e : E →L[𝕜] F).comp P ∧
         (R†).comp R = P ∧ R.comp (R†) = Q ∧
         R = (Q.comp R).comp P ∧
         (∀ x, x ∈ ⨅ n, U n ↔ e x ∈ ⨅ n, V n)) := by
  obtain ⟨S, T, hS, hT, hSnorm, hTnorm, hAdj, hProdU, hProdV⟩ :=
    exists_strongSums_of_projectionShells W U V hU hV hU0 hV0 hInitial hFinal
  have hfiniteComplement : ∀ N,
      (e : E →L[𝕜] F).comp (1 - (U N).starProjection) = partialSum W N :=
    comp_complement_eq_partialSum_of_shells (e : E →L[𝕜] F)
      (Submodule.projectionShell U) W U hUnitary
      (Submodule.partialSum_projectionShell U hU0)
  have hfiniteConjugacy : ∀ N,
      ((e : E →L[𝕜] F).comp (U N).starProjection).comp
        ((e : E →L[𝕜] F)†) = (V N).starProjection :=
    unitary_starProjection_conjugacy_of_projectionShells e W U V hU hV hU0 hV0
      hInitial hFinal hUnitary
  have hcompletion := unitaryCompletion_of_finite_relations e (partialSum W) S U V
    hU hV hS hfiniteComplement hfiniteConjugacy
  exact ⟨S, T, hS, hT, hSnorm, hTnorm, hAdj, hProdU, hProdV, hcompletion⟩

end ContinuousLinearMap
