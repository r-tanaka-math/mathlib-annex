import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.ContractiveStarSampling

/-!
# Simultaneous finite star-word sampling without loss of the norm bound

A finite word only visits finitely many suffix vectors.  Enlarge the input
finite set by those suffix vectors and use sharp two-sided interpolation once.
The same source element then realizes every requested word/vector test exactly.
This is a concrete polynomial-test theorem, not an all-tensor-dual closure theorem.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open MathlibAnnex.Analysis.CStarAlgebra

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

universe u v

variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- `false` chooses the operator, `true` its adjoint. -/
def starLetter (T : H →L[ℂ] H) (adj : Bool) : H →L[ℂ] H :=
  if adj then star T else T

/-- A displayed word acts from right to left, as operator multiplication does. -/
def starWordValue (T : H →L[ℂ] H) : List Bool → H → H
  | [], x => x
  | adj :: w, x => starLetter T adj (starWordValue T w x)

/-- The finite set of target suffix vectors needed to evaluate a word. -/
def starWordSupport (T : H →L[ℂ] H) (w : List Bool) (x : H) : Finset H := by
  classical
  exact match w with
  | [] => {x}
  | _ :: tail => insert (starWordValue T tail x) (starWordSupport T tail x)

/-- Agreement of both generators on target suffixes gives exact word action. -/
theorem starWordValue_eq_of_support
    (S T : H →L[ℂ] H) (w : List Bool) (x : H)
    (hf : ∀ y ∈ starWordSupport T w x, S y = T y)
    (hs : ∀ y ∈ starWordSupport T w x, (star S) y = (star T) y) :
    starWordValue S w x = starWordValue T w x := by
  classical
  revert hf hs
  induction w with
  | nil => intro _ _; rfl
  | cons adj tail ih =>
      intro hf hs
      have htail : starWordValue S tail x = starWordValue T tail x := by
        apply ih
        · intro y hy
          exact hf y (by simp only [starWordSupport, Finset.mem_insert]; exact Or.inr hy)
        · intro y hy
          exact hs y (by simp only [starWordSupport, Finset.mem_insert]; exact Or.inr hy)
      simp only [starWordValue, htail]
      have hy : starWordValue T tail x ∈ starWordSupport T (adj :: tail) x := by
        simp [starWordSupport]
      cases adj
      · simpa [starLetter] using hf _ hy
      · simpa [starLetter] using hs _ hy

/-- One sharp-norm source element matches an arbitrary finite collection of
star-words on arbitrary test vectors, simultaneously. -/
theorem exists_norm_le_finite_starWords_eq
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (T : H →L[ℂ] H) (tests : Finset (List Bool × H)) :
    ∃ a : A, ‖a‖ ≤ ‖T‖ ∧ ∀ p ∈ tests,
      starWordValue (pi a) p.1 p.2 = starWordValue T p.1 p.2 := by
  classical
  let s := tests.biUnion (fun p => starWordSupport T p.1 p.2)
  obtain ⟨a, ha, hf, hs⟩ := exists_norm_le_and_both_eq_finset pi hpi s T
  refine ⟨a, ha, ?_⟩
  intro p hp
  apply starWordValue_eq_of_support
  · intro y hy
    exact hf y (Finset.mem_biUnion.mpr ⟨p, hp, hy⟩)
  · intro y hy
    simpa only [map_star] using hs y (Finset.mem_biUnion.mpr ⟨p, hp, hy⟩)

/-- A finite collection of polynomial matrix-coefficient tests is preserved
by the same norm-controlled source element.  Coefficients and words are fixed
before the witness is selected. -/
theorem exists_norm_le_finite_wordMoments_eq
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (T : H →L[ℂ] H)
    {I J : Type*} [Fintype I] [Fintype J]
    (c : I → J → ℂ) (w : I → J → List Bool) (eta xi : I → J → H) :
    ∃ a : A, ‖a‖ ≤ ‖T‖ ∧ ∀ i,
      (∑ j, c i j * inner ℂ (eta i j) (starWordValue (pi a) (w i j) (xi i j))) =
      ∑ j, c i j * inner ℂ (eta i j) (starWordValue T (w i j) (xi i j)) := by
  classical
  let tests : Finset (List Bool × H) :=
    Finset.univ.image (fun ij : I × J => (w ij.1 ij.2, xi ij.1 ij.2))
  obtain ⟨a, ha, hwords⟩ := exists_norm_le_finite_starWords_eq pi hpi T tests
  refine ⟨a, ha, ?_⟩
  intro i
  apply Finset.sum_congr rfl
  intro j _
  have hmem : (w i j, xi i j) ∈ tests :=
    Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩
  rw [hwords _ hmem]

/-- The previously constructed single sample net is eventually exact on
every fixed finite word, not just on its two generators. -/
theorem contractiveStarSample_eventually_word_eq
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (T : H →L[ℂ] H) (w : List Bool) (x : H) :
    ∀ᶠ s : Finset H in atTop,
      starWordValue (pi (contractiveStarSample pi hpi T s)) w x =
        starWordValue T w x := by
  classical
  filter_upwards [eventually_ge_atTop (starWordSupport T w x)] with s hs
  apply starWordValue_eq_of_support
  · intro y hy
    exact (contractiveStarSample_spec pi hpi T s).2.1 y (hs hy)
  · intro y hy
    simpa only [map_star] using
      (contractiveStarSample_spec pi hpi T s).2.2 y (hs hy)

/-- Polynomial matrix coefficients converge along the original net. -/
theorem tendsto_contractiveStarSample_wordMoment
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (T : H →L[ℂ] H) (w : List Bool) (eta xi : H) :
    Tendsto (fun s => inner ℂ eta
      (starWordValue (pi (contractiveStarSample pi hpi T s)) w xi))
      atTop (𝓝 (inner ℂ eta (starWordValue T w xi))) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [contractiveStarSample_eventually_word_eq pi hpi T w xi] with s hs
  exact congrArg (inner ℂ eta) hs.symm

end MathlibAnnex.CStarAlgebra.TensorAveraging
