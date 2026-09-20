import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.GramAssistedTwoLeg
import MathlibAnnex.Analysis.CStarAlgebra.LocalPathTransport

/-!
# Protected state transport from one supplied finite row

The row and its protection are explicit inputs. The theorem chooses its
moment tests and comparison radius before the comparison pure state and
before the later finite approximation request. The comparison vector here
is distinct from the internal same-ζ vector of the two-leg path theorem.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra

open MathlibAnnex.CStarAlgebra

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

theorem Representation.exists_protected_state_transport_of_row
    (pi : Representation A H) (hpi : StarAlgHom.IsIrreducible pi)
    (hno : pi.HasNoNonzeroCompactImage)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi)
    (hker : ∀ a : A, pi a = 0 → phi a = 0)
    (xi : H) (hxi : ‖xi‖ = 1)
    (hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi))
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {n : ℕ} (x : Fin n → A)
    (hq : ‖MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x‖ ≤ 1)
    (hqxi : pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) xi = xi)
    (hprotect : ∀ a ∈ F, ∀ h : A,
      ‖a * MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h -
        MathlibAnnex.CStarAlgebra.TensorAveraging.rowMap A x h * a‖ ≤
        ((epsilon / 2) / (8 * Real.pi)) * ‖h‖) :
    ∃ G : Finset A, ∃ delta : ℝ, 0 < delta ∧
      ∀ psi : A →L[ℂ] ℂ, psi ∈ stateSpace A → IsPureState A psi →
        (∀ a : A, pi a = 0 → psi a = 0) →
        (∀ a ∈ G, ‖phi a - psi a‖ < delta) →
        ∀ T : Finset A, ∀ eta : ℝ, 0 < eta →
          ∃ u : unitary A, ∃ p : Path 1 u,
            PathCentralOn p F epsilon ∧
              ∀ a ∈ T, ‖pull phi u a - psi a‖ < eta := by
  classical
  have hehalf : 0 < epsilon / 2 := by positivity
  obtain ⟨μ, hμ, hmove⟩ :=
    pi.exists_g_assisted_two_leg_local_path_finite
      hpi hno phi hphi hpure hker xi hxi hcoeff F hehalf x hq hqxi hprotect
  let G : Finset A := rowMomentTests x
  let delta : ℝ := μ / 2
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  refine ⟨G, delta, hdelta, ?_⟩
  intro psi hpsi hpurepsi hkerpsi hclose T eta heta
  let r : ℝ := min (μ / 2) (eta / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  let tests : Finset A := G ∪ T
  letI : FiniteDimensional ℂ (⊥ : Submodule ℂ H) := inferInstance
  obtain ⟨v, hv, _hvorth, happ⟩ :=
    pi.exists_unit_mem_orthogonal_approx hno psi hpsi hpurepsi hkerpsi
      (⊥ : Submodule ℂ H) tests hr
  have hcompare (a : A) (ha : a ∈ G) :
      ‖phi a - inner ℂ v (pi a v)‖ < μ := by
    have hp : ‖psi a - inner ℂ v (pi a v)‖ < r :=
      happ a (Finset.mem_union_left T ha)
    have ht : ‖phi a - psi a‖ < delta := hclose a ha
    calc
      ‖phi a - inner ℂ v (pi a v)‖ =
          ‖(phi a - psi a) + (psi a - inner ℂ v (pi a v))‖ := by ring
      _ ≤ ‖phi a - psi a‖ + ‖psi a - inner ℂ v (pi a v)‖ := norm_add_le _ _
      _ < delta + r := add_lt_add ht hp
      _ ≤ μ := by
        have hrle : r ≤ μ / 2 := min_le_left _ _
        dsimp [delta]
        linarith
  have hmom (i j : Fin n) :
      ‖phi (x i * star (x j)) -
        inner ℂ v (pi (x i * star (x j)) v)‖ < μ := by
    apply hcompare
    dsimp [G, rowMomentTests]
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    exact ⟨(i, j), by simp, rfl⟩
  have hqmom :
      ‖phi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) -
        inner ℂ v (pi (MathlibAnnex.CStarAlgebra.TensorAveraging.rowSquare A x) v)‖ < μ := by
    apply hcompare
    simp [G, rowMomentTests]
  obtain ⟨u, p, hu, hp⟩ := hmove v hv hmom hqmom
  refine ⟨u, p, ?_, ?_⟩
  · intro t a ha
    obtain ⟨hf, hi⟩ := hp t a ha
    constructor <;> linarith
  · intro a ha
    have hphiVec : phi = Representation.vectorFunctional pi xi := by
      ext b
      exact hcoeff b
    have hpull : pull phi u a = inner ℂ v (pi a v) := by
      rw [hphiVec]
      calc
        pull (Representation.vectorFunctional pi xi) u a =
            Representation.vectorFunctional pi xi
              (star (u : A) * a * (u : A)) := by
                simp [pull_apply, innerAt]
        _ = Representation.vectorFunctional pi (pi (u : A) xi) a :=
              (Representation.vectorFunctional_map_apply pi xi (u : A) a).symm
        _ = inner ℂ v (pi a v) := by rw [hu]; rfl
    have hvtest : ‖psi a - inner ℂ v (pi a v)‖ < r :=
      happ a (Finset.mem_union_right G ha)
    rw [hpull, norm_sub_rev]
    have hrle : r ≤ eta / 2 := min_le_right _ _
    linarith

end MathlibAnnex.Analysis.CStarAlgebra
