import MathlibAnnex.Analysis.CStarAlgebra.State.KernelVectorApproximation
import MathlibAnnex.Analysis.CStarAlgebra.State.CompactMoment
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.SmallPath
import MathlibAnnex.Analysis.CStarAlgebra.LocalPathTransport
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactSandwichApproximation

/-!
# Protected pure-state transport from an approximate rank-one moment

C05 source, UNBUILT. The chosen rank-one test precedes the comparison
state and ALL later approximation requests. Exact vector realization of
the comparison state is not required: one vector for the union of the test
sets suffices. A single phase-aligned vector and unitary path are retained.
-/
set_option autoImplicit false
noncomputable section
open scoped ComplexOrder ComplexStarModule InnerProduct
namespace MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra
universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

private theorem unit_vector_coefficient_sub_le
    (x : H) (hx : ‖x‖ = 1) (S T : H →L[ℂ] H) :
    ‖inner ℂ x (S x) - inner ℂ x (T x)‖ ≤ ‖S - T‖ := by
  calc
    _ = ‖inner ℂ x ((S - T) x)‖ := by simp only [ContinuousLinearMap.sub_apply, inner_sub_right]
    _ ≤ ‖x‖ * ‖(S - T) x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖S - T‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((S - T).le_opNorm x) (norm_nonneg x)
    _ = _ := by rw [hx]; ring

/-- A norm-approximate rank-one preimage, not an exact one, suffices. -/
theorem Representation.exists_protected_state_transport_of_approx_rankOne
    (pi : Representation A H) (hpi : StarAlgHom.IsIrreducible pi)
    (phi : A →L[ℂ] ℂ) (xi : H) (hxi : ‖xi‖ = 1)
    (hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi))
    (hrank : ∀ tau : ℝ, 0 < tau →
      ∃ p0 : A, ‖pi p0 - InnerProductSpace.rankOne ℂ xi xi‖ < tau)
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ G : Finset A, ∃ delta : ℝ, 0 < delta ∧
      ∀ psi : A →L[ℂ] ℂ, psi ∈ stateSpace A → IsPureState A psi →
        (∀ a : A, pi a = 0 → psi a = 0) →
        (∀ a ∈ G, ‖phi a - psi a‖ < delta) →
        ∀ T : Finset A, ∀ eta : ℝ, 0 < eta →
          ∃ u : unitary A, ∃ p : Path 1 u,
            PathCentralOn p F epsilon ∧
              ∀ a ∈ T, ‖pull phi u a - psi a‖ < eta := by
  classical
  let M : ℝ := 1 + ∑ a ∈ F, ‖a‖
  have hM : 0 < M := by
    dsimp [M]
    have hs : 0 ≤ ∑ a ∈ F, ‖a‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hbound : ∀ a ∈ F, ‖a‖ ≤ M := by
    intro a ha
    have hs := Finset.single_le_sum (fun b (_ : b ∈ F) => norm_nonneg b) ha
    dsimp [M]
    linarith
  let e : ℝ := epsilon / (2 * M)
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨d, hd, hsmall⟩ := StarAlgHom.exists_small_unitary_path_apply_eq pi hpi he
  let kappa : ℝ := min 1 (d ^ 2 / 2)
  have hkappa : 0 < kappa := lt_min zero_lt_one (by positivity)
  obtain ⟨p0, hp0⟩ := hrank (kappa / 8) (by positivity)
  let P : H →L[ℂ] H := InnerProductSpace.rankOne ℂ xi xi
  have hPxi : inner ℂ xi (P xi) = 1 := by
    have hi : inner ℂ xi xi = 1 := inner_self_eq_one_of_norm_eq_one hxi
    simp [P, InnerProductSpace.rankOne_apply, hxi]
  have hfirst : ‖(1 : ℂ) - phi p0‖ < kappa / 8 := by
    rw [hcoeff p0, norm_sub_rev, ← hPxi]
    exact (unit_vector_coefficient_sub_le xi hxi (pi p0) P).trans_lt hp0
  let delta : ℝ := kappa / 4
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  refine ⟨{p0}, delta, hdelta, ?_⟩
  intro psi hpsi hpure hker hclose T eta heta
  let r : ℝ := min delta (eta / 2)
  have hr : 0 < r := lt_min hdelta (by positivity)
  obtain ⟨v, hv, happ⟩ :=
    pi.exists_unit_vector_approx_of_kernel psi hpsi hpure hker (insert p0 T) hr
  have hsecond : ‖phi p0 - psi p0‖ < delta := hclose p0 (by simp)
  have hthird : ‖psi p0 - inner ℂ v (pi p0 v)‖ < r := happ p0 (by simp)
  have hfourth : ‖inner ℂ v (pi p0 v) - inner ℂ v (P v)‖ < kappa / 8 :=
    (unit_vector_coefficient_sub_le v hv (pi p0) P).trans_lt hp0
  have hm : ‖(1 : ℂ) - inner ℂ v (P v)‖ < kappa := by
    have hsum : ‖(1 : ℂ) - inner ℂ v (P v)‖ ≤
        ‖1 - phi p0‖ + ‖phi p0 - psi p0‖ +
        ‖psi p0 - inner ℂ v (pi p0 v)‖ +
        ‖inner ℂ v (pi p0 v) - inner ℂ v (P v)‖ := by
      calc
        _ = ‖((1 - phi p0) + (phi p0 - psi p0)) +
              (psi p0 - inner ℂ v (pi p0 v)) +
              (inner ℂ v (pi p0 v) - inner ℂ v (P v))‖ := by congr 1; ring
        _ ≤ _ := by
          calc
            _ ≤ ‖(1 - phi p0) + (phi p0 - psi p0) +
                  (psi p0 - inner ℂ v (pi p0 v))‖ +
                  ‖inner ℂ v (pi p0 v) - inner ℂ v (P v)‖ := norm_add_le _ _
            _ ≤ (‖(1 - phi p0) + (phi p0 - psi p0)‖ +
                  ‖psi p0 - inner ℂ v (pi p0 v)‖) +
                  ‖inner ℂ v (pi p0 v) - inner ℂ v (P v)‖ := by
              gcongr
              exact norm_add_le _ _
            _ ≤ _ := by
              gcongr
              exact norm_add_le _ _
    have hrle : r ≤ delta := min_le_left _ _
    dsimp [delta] at hsecond hrle
    linarith
  obtain ⟨zeta, hzeta, hsame, hnear⟩ :=
    phase_align_of_rankOne_moment xi v hxi hv hd hm
  obtain ⟨u, p, hu, hp⟩ := hsmall xi zeta hxi hzeta hnear
  refine ⟨u, p, ?_, ?_⟩
  · intro t a ha
    obtain ⟨hi, hf⟩ := hp t a
    have hscale : e * ‖a‖ ≤ epsilon / 2 := by
      calc
        e * ‖a‖ ≤ e * M := mul_le_mul_of_nonneg_left (hbound a ha) he.le
        _ = epsilon / 2 := by dsimp [e]; field_simp
    constructor <;> linarith
  · intro a ha
    have hphiVec : phi = Representation.vectorFunctional pi xi := by
      ext b
      exact hcoeff b
    have hpull : pull phi u a = inner ℂ zeta (pi a zeta) := by
      rw [hphiVec]
      calc
        pull (Representation.vectorFunctional pi xi) u a =
            Representation.vectorFunctional pi xi
              (star (u : A) * a * (u : A)) := by simp [pull_apply, innerAt]
        _ = Representation.vectorFunctional pi (pi (u : A) xi) a :=
          (Representation.vectorFunctional_map_apply pi xi (u : A) a).symm
        _ = inner ℂ zeta (pi a zeta) := by rw [hu]; rfl
    rw [hpull, hsame (pi a), norm_sub_rev]
    have h := happ a (Finset.mem_insert_of_mem ha)
    have hrle : r ≤ eta / 2 := min_le_right _ _
    linarith

/-- The compact branch is supplied directly by the compact sandwich
construction. It works in finite or infinite dimensional H. -/
theorem Representation.exists_protected_state_transport_of_compact_image
    (pi : Representation A H) (hpi : StarAlgHom.IsIrreducible pi)
    (k : A) (hk : IsCompactOperator (pi k)) (hk0 : pi k ≠ 0)
    (phi : A →L[ℂ] ℂ) (xi : H) (hxi : ‖xi‖ = 1)
    (hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi))
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ G : Finset A, ∃ delta : ℝ, 0 < delta ∧
      ∀ psi : A →L[ℂ] ℂ, psi ∈ stateSpace A → IsPureState A psi →
        (∀ a : A, pi a = 0 → psi a = 0) →
        (∀ a ∈ G, ‖phi a - psi a‖ < delta) →
        ∀ T : Finset A, ∀ eta : ℝ, 0 < eta →
          ∃ u : unitary A, ∃ p : Path 1 u,
            PathCentralOn p F epsilon ∧
              ∀ a ∈ T, ‖pull phi u a - psi a‖ < eta := by
  exact pi.exists_protected_state_transport_of_approx_rankOne hpi phi xi hxi hcoeff
    (fun _ ht => pi.exists_approx_rankOne_of_compact_image hpi k hk hk0 xi hxi ht)
    F hepsilon

end MathlibAnnex.Analysis.CStarAlgebra
