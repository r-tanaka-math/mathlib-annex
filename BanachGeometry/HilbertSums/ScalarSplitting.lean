/-
L² adapters used in the exact inverse comparison. The product is WithLp 2,
never the maximum-norm product. No finiteness assumption on the blocks is used.
-/
import BanachGeometry.HilbertSums.FrozenIsometry

noncomputable section
open scoped BigOperators
namespace BanachGeometry.HilbertSums

def scalarEvenL2 (t : ScalarL2) : ScalarL2 :=
  ⟨fun n => t (2 * n), mem_l2_of_summable_sq _
    ((l2_summable_sq t).comp_injective (by
      intro i j h
      change 2 * i = 2 * j at h
      omega))⟩

def scalarOddL2 (t : ScalarL2) : ScalarL2 :=
  ⟨fun n => t (2 * n + 1), mem_l2_of_summable_sq _
    ((l2_summable_sq t).comp_injective (by
      intro i j h
      change 2 * i + 1 = 2 * j + 1 at h
      omega))⟩

@[simp] theorem scalarEvenL2_apply (t : ScalarL2) (n : ℕ) :
    scalarEvenL2 t n = t (2 * n) := rfl

@[simp] theorem scalarOddL2_apply (t : ScalarL2) (n : ℕ) :
    scalarOddL2 t n = t (2 * n + 1) := rfl

theorem scalar_split_norm_sq (t : ScalarL2) :
    ‖scalarOddL2 t‖ ^ 2 + ‖scalarEvenL2 t‖ ^ 2 = ‖t‖ ^ 2 := by
  have he : Summable (fun n => ‖t (2 * n)‖ ^ 2) :=
    (l2_summable_sq t).comp_injective (by
      intro i j h
      change 2 * i = 2 * j at h
      omega)
  have ho : Summable (fun n => ‖t (2 * n + 1)‖ ^ 2) :=
    (l2_summable_sq t).comp_injective (by
      intro i j h
      change 2 * i + 1 = 2 * j + 1 at h
      omega)
  rw [l2_norm_sq, l2_norm_sq, l2_norm_sq]
  change (∑' n, ‖t (2 * n + 1)‖ ^ 2) + (∑' n, ‖t (2 * n)‖ ^ 2) = ∑' n, ‖t n‖ ^ 2
  calc
    _ = (∑' n, ‖t (2 * n)‖ ^ 2) + ∑' n, ‖t (2 * n + 1)‖ ^ 2 := add_comm _ _
    _ = _ := tsum_even_add_odd (f := fun n => ‖t n‖ ^ 2) he ho

variable {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℝ (G n)]

/-- Coordinatewise scalar multiplication along unit directions is an isometric lift. -/
def scalarDirectionL2 (ξ : ∀ n, G n) (hξ : ∀ n, ‖ξ n‖ = 1) (t : ScalarL2) : lp G 2 :=
  ⟨fun n => t n • ξ n, (lp.memℓp t).mono' (by
    intro n
    simp only [norm_smul, hξ n, mul_one, le_refl])⟩

@[simp] theorem scalarDirectionL2_apply (ξ : ∀ n, G n)
    (hξ : ∀ n, ‖ξ n‖ = 1) (t : ScalarL2) (n : ℕ) :
    scalarDirectionL2 ξ hξ t n = t n • ξ n := rfl

theorem scalarDirectionL2_norm (ξ : ∀ n, G n)
    (hξ : ∀ n, ‖ξ n‖ = 1) (t : ScalarL2) : ‖scalarDirectionL2 ξ hξ t‖ = ‖t‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simp only [l2_norm_sq, scalarDirectionL2_apply, norm_smul, hξ, mul_one]

end BanachGeometry.HilbertSums
