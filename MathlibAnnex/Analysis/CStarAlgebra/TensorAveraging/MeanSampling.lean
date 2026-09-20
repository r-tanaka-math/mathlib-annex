import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteRow
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Isometry sampling for the represented Haagerup mean

The map `B ↦ (s ↦ B(s⋆,s))` is a genuine contraction into the bounded
functions on the *discrete* isometry set.  This is the main-side kernel for
the KOS invariant mean.  It does not assert that such a mean exists or that
an arbitrary C-star bilinear form has already been normally extended.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped CStarAlgebra BoundedContinuousFunction

namespace MathlibAnnex.CStarAlgebra.TensorAveraging
variable (M : Type*) [CStarAlgebra M] [Nontrivial M]

/-- Isometries of a unital complex C-star algebra, with `s⋆s=1`. -/
def Isometry := {s : M // star s * s = 1}

instance : Nonempty (Isometry M) := ⟨⟨1, by simp⟩⟩
instance : TopologicalSpace (Isometry M) := ⊥
instance : DiscreteTopology (Isometry M) := ⟨rfl⟩

theorem norm_isometry (s : Isometry M) : ‖s.1‖ = 1 := by
  have h := CStarRing.norm_star_mul_self (x := s.1)
  rw [s.2, norm_one] at h
  nlinarith [norm_nonneg s.1]

/-- Curried bounded complex bilinear forms. -/
abbrev ContinuousBilinearForm := M →L[ℂ] (M →L[ℂ] ℂ)

theorem sample_bound (B : ContinuousBilinearForm M) (s : Isometry M) :
    ‖B (star s.1) s.1‖ ≤ ‖B‖ := by
  calc
    ‖B (star s.1) s.1‖ ≤ ‖B (star s.1)‖ * ‖s.1‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖B‖ * ‖star s.1‖) * ‖s.1‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖B‖ := by rw [norm_star, norm_isometry M s]; ring

/-- The `V(s⋆,s)` orientation from KOS Section 4. -/
def sample (B : ContinuousBilinearForm M) : Isometry M →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfDiscrete
    (fun s => B (star s.1) s.1) (2 * ‖B‖) (by
      intro s t
      rw [dist_eq_norm]
      calc
        ‖B (star s.1) s.1 - B (star t.1) t.1‖ ≤
            ‖B (star s.1) s.1‖ + ‖B (star t.1) t.1‖ := norm_sub_le _ _
        _ ≤ 2 * ‖B‖ := by linarith [sample_bound M B s, sample_bound M B t])

theorem sample_norm_le (B : ContinuousBilinearForm M) : ‖sample M B‖ ≤ ‖B‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg B)).2
  intro s
  exact sample_bound M B s

def sampleLinear : ContinuousBilinearForm M →ₗ[ℂ] (Isometry M →ᵇ ℂ) where
  toFun := sample M
  map_add' := by intro B C; apply BoundedContinuousFunction.ext; intro s; rfl
  map_smul' := by intro c B; apply BoundedContinuousFunction.ext; intro s; rfl

/-- Isometry sampling is a bounded complex-linear contraction. -/
def sampleCLM : ContinuousBilinearForm M →L[ℂ] (Isometry M →ᵇ ℂ) := by
  refine LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := ContinuousBilinearForm M) (F := Isometry M →ᵇ ℂ) (σ := RingHom.id ℂ)
    (sampleLinear M) 1 ?_
  intro B
  change ‖sample M B‖ ≤ (1 : ℝ) * ‖B‖
  simpa using sample_norm_le M B

/-- The bilinear form `φ(xy)` on the represented algebra. -/
def mulForm (φ : M →L[ℂ] ℂ) : ContinuousBilinearForm M :=
  (ContinuousLinearMap.compL ℂ M M ℂ φ).comp (ContinuousLinearMap.mul ℂ M)

/-- The orientation `V(s⋆,s)` makes the multiplication sample constant. -/
theorem sample_mulForm (φ : M →L[ℂ] ℂ) :
    sample M (mulForm M φ) = BoundedContinuousFunction.const (Isometry M) (φ 1) := by
  apply BoundedContinuousFunction.ext
  intro s
  change φ (star s.1 * s.1) = φ 1
  rw [s.2]

theorem mean_const (m : (Isometry M →ᵇ ℂ) →L[ℂ] ℂ)
    (hone : m (BoundedContinuousFunction.const (Isometry M) 1) = 1)
    (z : ℂ) : m (BoundedContinuousFunction.const (Isometry M) z) = z := by
  have heq : BoundedContinuousFunction.const (Isometry M) z =
      z • BoundedContinuousFunction.const (Isometry M) (1 : ℂ) := by
    apply BoundedContinuousFunction.ext
    intro s
    simp
  rw [heq, map_smul, hone, smul_eq_mul, mul_one]

/-- A normalized mean, if supplied, evaluates the represented multiplication
moment exactly.  The existence of the invariant mean remains separate. -/
theorem mean_sample_mulForm (m : (Isometry M →ᵇ ℂ) →L[ℂ] ℂ)
    (hone : m (BoundedContinuousFunction.const (Isometry M) 1) = 1)
    (φ : M →L[ℂ] ℂ) : m (sample M (mulForm M φ)) = φ 1 := by
  rw [sample_mulForm]
  exact mean_const M m hone (φ 1)

end MathlibAnnex.CStarAlgebra.TensorAveraging
