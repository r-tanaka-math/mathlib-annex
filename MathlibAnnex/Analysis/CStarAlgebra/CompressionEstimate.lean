import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
The uniform approximation estimate that transports exact finite-stage
compression identities to arbitrary source elements.
-/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.CStarAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- If compression is exact at an approximant `c`, a contractive functional
and a contractive projection-like element give the standard factor-two error
bound.  No bidual or representation is involved. -/
theorem norm_compression_sub_smul_le_two_mul
    (q b c : A) (phi : A →L[ℂ] ℂ)
    (hq : ‖q‖ ≤ 1) (hphi : ∀ a : A, ‖phi a‖ ≤ ‖a‖)
    (hexact : q * c * q = (phi c) • q) :
    ‖q * b * q - (phi b) • q‖ ≤ 2 * ‖b - c‖ := by
  have hid :
      q * b * q - (phi b) • q =
        q * (b - c) * q + (phi c - phi b) • q := by
    rw [mul_sub, sub_mul, sub_smul, hexact]
    abel
  have hfirst : ‖q * (b - c) * q‖ ≤ ‖b - c‖ := by
    calc
      ‖q * (b - c) * q‖ ≤ ‖q * (b - c)‖ * ‖q‖ := norm_mul_le _ _
      _ ≤ (‖q‖ * ‖b - c‖) * ‖q‖ := by
        gcongr
        exact norm_mul_le _ _
      _ ≤ (1 * ‖b - c‖) * 1 := by gcongr
      _ = ‖b - c‖ := by ring
  have hsecond : ‖(phi c - phi b) • q‖ ≤ ‖b - c‖ := by
    rw [norm_smul]
    calc
      ‖phi c - phi b‖ * ‖q‖ = ‖phi (c - b)‖ * ‖q‖ := by rw [map_sub]
      _ ≤ ‖c - b‖ * 1 := by gcongr; exact hphi (c - b)
      _ = ‖b - c‖ := by rw [norm_sub_rev, mul_one]
  rw [hid]
  exact (norm_add_le _ _).trans <| by
    simpa [two_mul] using add_le_add hfirst hsecond

end MathlibAnnex.Analysis.CStarAlgebra
