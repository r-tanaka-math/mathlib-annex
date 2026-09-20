import MathlibAnnex.Analysis.CStarAlgebra.State.CompactMoment
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.SmallPath
import MathlibAnnex.Analysis.CStarAlgebra.LocalPathTransport
import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder ComplexStarModule InnerProduct
namespace MathlibAnnex.Analysis.CStarAlgebra

open MathlibAnnex.CStarAlgebra

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [FiniteDimensional ℂ H]

theorem Representation.exists_small_path_pull_eq_of_full_finite
    (pi : Representation A H) (hinj : Function.Injective pi)
    (hsurj : Function.Surjective pi) (hpi : StarAlgHom.IsIrreducible pi)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (xi : H) (hxi : ‖xi‖ = 1)
    (hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi))
    {e : ℝ} (he : 0 < e) :
    ∃ p0 : A, ∃ delta : ℝ, 0 < delta ∧
      ∀ psi : A →L[ℂ] ℂ, psi ∈ stateSpace A → IsPureState A psi →
        ‖phi p0 - psi p0‖ < delta →
        ∃ u : unitary A, ∃ p : Path 1 u,
          pull phi u = psi ∧
          ∀ t : Set.Icc (0 : ℝ) 1, ∀ a : A,
            ‖star (p t : A) * a * (p t : A) - a‖ ≤ e * ‖a‖ ∧
            ‖(p t : A) * a * star (p t : A) - a‖ ≤ e * ‖a‖ := by
  obtain ⟨d, hd, hsmall⟩ :=
    StarAlgHom.exists_small_unitary_path_apply_eq pi hpi he
  obtain ⟨p0, hp0⟩ := hsurj (InnerProductSpace.rankOne ℂ xi xi)
  have hphiP : phi p0 = 1 := by
    have hinner : inner ℂ xi xi = 1 := inner_self_eq_one_of_norm_eq_one hxi
    calc
      phi p0 = inner ℂ xi (pi p0 xi) := hcoeff p0
      _ = inner ℂ xi ((InnerProductSpace.rankOne ℂ xi xi) xi) := by rw [hp0]
      _ = 1 := by simp [InnerProductSpace.rankOne_apply, hinner, hxi]
  let delta : ℝ := min 1 (d ^ 2 / 2)
  have hdelta : 0 < delta := lt_min zero_lt_one (by positivity)
  refine ⟨p0, delta, hdelta, ?_⟩
  intro psi hpsi hpure hclose
  obtain ⟨eta, heta, hetaCoeff⟩ :=
    representation_exists_exact_unit_vector_of_full_finite pi hinj hsurj
      psi hpsi hpure
  have hm : ‖(1 : ℂ) -
      inner ℂ eta ((InnerProductSpace.rankOne ℂ xi xi) eta)‖ < delta := by
    simpa [hphiP, hetaCoeff, hp0] using hclose
  obtain ⟨zeta, hzeta, hzetaCoeff, hnear⟩ :=
    phase_align_of_rankOne_moment xi eta hxi heta hd hm
  obtain ⟨u, p, hu, hp⟩ := hsmall xi zeta hxi hzeta hnear
  refine ⟨u, p, ?_, hp⟩
  ext a
  have hphiVec : phi = Representation.vectorFunctional pi xi := by
    ext b
    exact hcoeff b
  rw [hphiVec]
  calc
    pull (Representation.vectorFunctional pi xi) u a =
        Representation.vectorFunctional pi xi
          (star (u : A) * a * (u : A)) := by simp [pull_apply, innerAt]
    _ = Representation.vectorFunctional pi (pi (u : A) xi) a :=
        (Representation.vectorFunctional_map_apply pi xi (u : A) a).symm
    _ = inner ℂ zeta (pi a zeta) := by rw [hu]; rfl
    _ = inner ℂ eta (pi a eta) := hzetaCoeff (pi a)
    _ = psi a := (hetaCoeff a).symm

/-- In the full finite-dimensional image, one rank-one moment protects the
entire later state request. The correction has exact pull equality. -/
theorem Representation.exists_protected_state_transport_of_full_finite
    (pi : Representation A H) (hinj : Function.Injective pi)
    (hsurj : Function.Surjective pi) (hpi : StarAlgHom.IsIrreducible pi)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (xi : H) (hxi : ‖xi‖ = 1)
    (hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi))
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ G : Finset A, ∃ delta : ℝ, 0 < delta ∧
      ∀ psi : A →L[ℂ] ℂ, psi ∈ stateSpace A → IsPureState A psi →
        (∀ a ∈ G, ‖phi a - psi a‖ < delta) →
        ∀ T : Finset A, ∀ eta : ℝ, 0 < eta →
          ∃ u : unitary A, ∃ p : Path 1 u,
            PathCentralOn p F epsilon ∧
              ∀ a ∈ T, ‖pull phi u a - psi a‖ < eta := by
  classical
  let M : ℝ := 1 + ∑ a ∈ F, ‖a‖
  have hM : 0 < M := by
    dsimp [M]
    have hsum : 0 ≤ ∑ a ∈ F, ‖a‖ := Finset.sum_nonneg fun a _ => norm_nonneg a
    linarith
  have hbound : ∀ a ∈ F, ‖a‖ ≤ M := by
    intro a ha
    have hs : ‖a‖ ≤ ∑ b ∈ F, ‖b‖ :=
      Finset.single_le_sum (fun b _ => norm_nonneg b) ha
    dsimp [M]
    linarith
  let e : ℝ := epsilon / (2 * M)
  have he : 0 < e := div_pos hepsilon (mul_pos (by norm_num) hM)
  obtain ⟨p0, delta, hdelta, hlocal⟩ :=
    pi.exists_small_path_pull_eq_of_full_finite hinj hsurj hpi
      phi hphi xi hxi hcoeff he
  refine ⟨{p0}, delta, hdelta, ?_⟩
  intro psi hpsi hpure hclose T eta heta
  obtain ⟨u, p, heq, hp⟩ := hlocal psi hpsi hpure
    (hclose p0 (by simp))
  refine ⟨u, p, ?_, ?_⟩
  · intro t a ha
    obtain ⟨hi, hf⟩ := hp t a
    have hcoeffle : e * ‖a‖ ≤ epsilon / 2 := by
      calc
        e * ‖a‖ ≤ e * M :=
          mul_le_mul_of_nonneg_left (hbound a ha) he.le
        _ = epsilon / 2 := by
          dsimp [e]
          field_simp
    constructor <;> linarith
  · intro a _
    rw [heq, sub_self, norm_zero]
    exact heta

end MathlibAnnex.Analysis.CStarAlgebra
