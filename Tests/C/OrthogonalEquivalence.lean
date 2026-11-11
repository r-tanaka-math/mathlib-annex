import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.OrthogonalEquivalence

/-! Typed consumers of equivalence between arbitrary orthogonal suprema. -/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra
open VonNeumannAlgebra

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The index type has an independent universe and no countability assumption. -/
example (M : VonNeumannAlgebra H) {ι : Type v}
    (p q : ι → M.toStarSubalgebra)
    (hp : ∀ i, IsStarProjection (p i)) (hq : ∀ i, IsStarProjection (q i))
    (horthp : Pairwise (fun i j ↦ p i * p j = 0))
    (horthq : Pairwise (fun i j ↦ q i * q j = 0))
    (heq : ∀ i, MurrayVonNeumannEquivalent (p i) (q i)) :
    MurrayVonNeumannEquivalent (iSupProjection M p hp) (iSupProjection M q hq) :=
  murrayVonNeumannEquivalent_iSupProjection
    (M := M) (p := p) (q := q) (hp := hp) (hq := hq)
    (horthp := horthp) (horthq := horthq) (heq := heq)

/-- The resulting witness belongs to the algebra subtype itself. -/
example (M : VonNeumannAlgebra H) {ι : Type v}
    (p q : ι → M.toStarSubalgebra)
    (hp : ∀ i, IsStarProjection (p i)) (hq : ∀ i, IsStarProjection (q i))
    (horthp : Pairwise (fun i j ↦ p i * p j = 0))
    (horthq : Pairwise (fun i j ↦ q i * q j = 0))
    (heq : ∀ i, MurrayVonNeumannEquivalent (p i) (q i)) :
    ∃ S : M.toStarSubalgebra, IsPartialIsometry S ∧
      star S * S = iSupProjection M p hp ∧ S * star S = iSupProjection M q hq :=
  (murrayVonNeumannEquivalent_iSupProjection M p q hp hq horthp horthq heq).exists_partial_isometry

/-- Empty families require no nonempty-index instance. -/
example (M : VonNeumannAlgebra H) (p q : Empty → M.toStarSubalgebra)
    (hp : ∀ i, IsStarProjection (p i)) (hq : ∀ i, IsStarProjection (q i)) :
    MurrayVonNeumannEquivalent (iSupProjection M p hp) (iSupProjection M q hq) := by
  apply murrayVonNeumannEquivalent_iSupProjection M p q hp hq
  · intro i
    cases i
  · intro i
    cases i
  · intro i
    cases i

/-- A zero family also permits an arbitrary index type. -/
example (M : VonNeumannAlgebra H) (ι : Type v) :
    MurrayVonNeumannEquivalent
      (iSupProjection M (fun _ : ι ↦ 0) (fun _ ↦ IsStarProjection.zero _))
      (iSupProjection M (fun _ : ι ↦ 0) (fun _ ↦ IsStarProjection.zero _)) := by
  apply murrayVonNeumannEquivalent_iSupProjection
  · intro i j hij
    exact zero_mul _
  · intro i j hij
    exact zero_mul _
  · intro i
    exact MurrayVonNeumannEquivalent.zero
