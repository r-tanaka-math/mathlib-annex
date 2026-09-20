import Mathlib.Analysis.InnerProductSpace.Adjoint
import MathlibAnnex.Analysis.InnerProductSpace.CommonFixed

/-!
Compression of a norm-convergent source flag inside a continuous Hilbert-space
representation. The conclusion is a matrix-coefficient identity on the common
fixed space; no bidual or transport of strong limits through representations is
used.
-/

set_option autoImplicit false

open Filter

namespace MathlibAnnex.Analysis.CStarAlgebra

variable {A H : Type*}
variable [NormedRing A] [NormedAlgebra ℂ A] [StarRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
If a compression error tends to zero in the source norm, then its matrix
coefficient vanishes on vectors fixed by every member of the flag. Continuity
of the representation is explicit; C*-representations supply it by standard
contractivity.
-/
theorem inner_map_eq_of_compression_tendsto
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : Continuous pi)
    (q : ℕ → A) (phi : A →ₗ[ℂ] ℂ) (b : A) (x y : H)
    (hq_star : ∀ n, star (q n) = q n)
    (hx : ∀ n, pi (q n) x = x) (hy : ∀ n, pi (q n) y = y)
    (hcompression :
      Tendsto (fun n ↦ q n * b * q n - (phi b) • q n) atTop (nhds 0)) :
    inner ℂ x (pi b y) = phi b * inner ℂ x y := by
  have hop :
      Tendsto (fun n ↦ pi (q n * b * q n - (phi b) • q n)) atTop (nhds 0) := by
    change Tendsto (pi ∘ fun n ↦ q n * b * q n - (phi b) • q n) atTop (nhds 0)
    simpa only [map_zero] using (hpi.tendsto 0).comp hcompression
  have happ :
      Tendsto (fun n ↦ pi (q n * b * q n - (phi b) • q n) y) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.apply ℂ H y).continuous.tendsto 0).comp hop
  have hinner :
      Tendsto
        (fun n ↦ inner ℂ x (pi (q n * b * q n - (phi b) • q n) y))
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.inner happ
  have hcoeff (n : ℕ) :
      inner ℂ x (pi (q n * b * q n - (phi b) • q n) y) =
        inner ℂ x (pi b y) - phi b * inner ℂ x y := by
    have hself : ContinuousLinearMap.adjoint (pi (q n)) = pi (q n) := by
      calc
        ContinuousLinearMap.adjoint (pi (q n)) = star (pi (q n)) := by
          rw [ContinuousLinearMap.star_eq_adjoint]
        _ = pi (star (q n)) := (map_star pi (q n)).symm
        _ = pi (q n) := by rw [hq_star n]
    calc
      inner ℂ x (pi (q n * b * q n - (phi b) • q n) y) =
          inner ℂ x (pi (q n) (pi b (pi (q n) y))) -
            inner ℂ x ((phi b) • pi (q n) y) := by
              simp only [map_sub, map_mul, map_smul, ContinuousLinearMap.sub_apply,
                ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, inner_sub_right]
      _ = inner ℂ x (pi (q n) (pi b y)) -
            inner ℂ x ((phi b) • y) := by rw [hy n]
      _ = inner ℂ (pi (q n) x) (pi b y) -
            inner ℂ x ((phi b) • y) := by
              simpa [hself] using
                (ContinuousLinearMap.adjoint_inner_right (pi (q n)) x (pi b y))
      _ = inner ℂ x (pi b y) - phi b * inner ℂ x y := by
            rw [hx n, inner_smul_right]
  have hconstant :
      Tendsto
        (fun _ : ℕ ↦ inner ℂ x (pi b y) - phi b * inner ℂ x y)
        atTop (nhds 0) :=
    hinner.congr' (Filter.Eventually.of_forall fun n ↦ hcoeff n)
  have hconst :
      Tendsto
        (fun _ : ℕ ↦ inner ℂ x (pi b y) - phi b * inner ℂ x y)
        atTop (nhds (inner ℂ x (pi b y) - phi b * inner ℂ x y)) :=
    tendsto_const_nhds
  have hz : inner ℂ x (pi b y) - phi b * inner ℂ x y = 0 :=
    tendsto_nhds_unique hconst hconstant
  exact sub_eq_zero.mp hz

/--
Operator form of compression onto a supplied orthogonal projection whose range
is contained in the common fixed space. This is the manuscript's compression
formula, still without moving a strong limit through `pi`.
-/
theorem projection_comp_map_comp_projection_eq
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : Continuous pi)
    (q : ℕ → A) (phi : A →ₗ[ℂ] ℂ) (b : A)
    (hq_star : ∀ n, star (q n) = q n)
    (hcompression :
      Tendsto (fun n ↦ q n * b * q n - (phi b) • q n) atTop (nhds 0))
    (P : H →L[ℂ] H) (hP_star : ContinuousLinearMap.adjoint P = P)
    (hP_idem : P * P = P)
    (hP_fixed : ∀ (n : ℕ) (z : H), pi (q n) (P z) = P z) :
    P * pi b * P = (phi b) • P := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_inner_left ℂ
  intro w
  have hcoeff := inner_map_eq_of_compression_tendsto pi hpi q phi b (P w) (P z)
    hq_star (fun n ↦ hP_fixed n w) (fun n ↦ hP_fixed n z) hcompression
  have hPPinner : inner ℂ (P w) (P z) = inner ℂ w (P z) := by
    have hPP : P (P z) = P z := by
      have := congrArg (fun T : H →L[ℂ] H ↦ T z) hP_idem
      simpa using this
    calc
      inner ℂ (P w) (P z) =
          inner ℂ w (ContinuousLinearMap.adjoint P (P z)) := by
            symm
            exact ContinuousLinearMap.adjoint_inner_right P w (P z)
      _ = inner ℂ w (P z) := by rw [hP_star, hPP]
  calc
    inner ℂ w ((P * pi b * P) z) = inner ℂ w (P (pi b (P z))) := rfl
    _ = inner ℂ (P w) (pi b (P z)) := by
      simpa [hP_star] using
        (ContinuousLinearMap.adjoint_inner_right P w (pi b (P z)))
    _ = phi b * inner ℂ (P w) (P z) := hcoeff
    _ = phi b * inner ℂ w (P z) := congrArg (fun c : ℂ ↦ phi b * c) hPPinner
    _ = inner ℂ w (((phi b) • P) z) := by
      simp [inner_smul_right]

/--
Compression formula for the actual orthogonal projection onto the common fixed
space of the represented flag.
-/
theorem commonFixedProjection_comp_map_comp_eq
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : Continuous pi)
    (q : ℕ → A) (phi : A →ₗ[ℂ] ℂ) (b : A)
    (hq_star : ∀ n, star (q n) = q n)
    (hcompression :
      Tendsto (fun n ↦ q n * b * q n - (phi b) • q n) atTop (nhds 0)) :
    let P := MathlibAnnex.Analysis.InnerProductSpace.commonFixedProjection
      (fun n ↦ pi (q n))
    P * pi b * P = (phi b) • P := by
  let Q : ℕ → H →L[ℂ] H := fun n ↦ pi (q n)
  let P := MathlibAnnex.Analysis.InnerProductSpace.commonFixedProjection Q
  exact projection_comp_map_comp_projection_eq pi hpi q phi b hq_star hcompression P
    (MathlibAnnex.Analysis.InnerProductSpace.adjoint_commonFixedProjection Q)
    (MathlibAnnex.Analysis.InnerProductSpace.commonFixedProjection_idempotent Q)
    (fun n z ↦ MathlibAnnex.Analysis.InnerProductSpace.commonFixedProjection_apply_fixed Q n z)

/--
A compression projection is rank one when the chosen vector is cyclic for the
whole representation.  The density hypothesis is essential: without it this
does not identify an ambient common-fixed projection of arbitrary
multiplicity.
-/
theorem projection_eq_rankOne_of_dense_orbit
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (phi : A →ₗ[ℂ] ℂ)
    (P : H →L[ℂ] H) (eta : H)
    (hPeta : P eta = eta)
    (hcompression : ∀ b : A, P * pi b * P = (phi b) • P)
    (hphi : ∀ b : A, phi b = inner ℂ eta (pi b eta))
    (hdense : DenseRange (fun b : A ↦ pi b eta)) :
    P = InnerProductSpace.rankOne ℂ eta eta := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using hdense.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih b =>
      have happ := congrArg (fun T : H →L[ℂ] H ↦ T eta) (hcompression b)
      have hPb : P (pi b eta) = phi b • eta := by
        simpa [hPeta] using happ
      calc
        P (pi b eta) = phi b • eta := hPb
        _ = inner ℂ eta (pi b eta) • eta := by rw [hphi b]
        _ = InnerProductSpace.rankOne ℂ eta eta (pi b eta) := by
          rw [InnerProductSpace.rankOne_apply]

end MathlibAnnex.Analysis.CStarAlgebra
