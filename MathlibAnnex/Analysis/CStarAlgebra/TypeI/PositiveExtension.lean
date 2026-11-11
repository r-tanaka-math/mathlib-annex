import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import MathlibAnnex.Analysis.CStarAlgebra.Intertwiner
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CompactIdealMaximality

/-!
# Positive bimodule extensions of cyclic representations

A state extension and its GNS representation give an actual positive unital
map on the ambient algebra. Its restriction is the prescribed cyclic
representation of the closed subalgebra. The two bimodule identities follow
from the isometric intertwiner and its adjoint.

The last theorem composes this construction with a supplied positive
bimodule map on all bounded operators. Only positivity, the restriction
equation and bimodularity are needed there. No normality of the auxiliary
map, separability, or irreducibility is assumed.

The existence of a suitable type III representation and of its auxiliary
expectation is a separate mathematical problem. These theorems construct
the ambient map once those particular inputs are available.
-/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w z

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

namespace Representation

/-- Compression of a representation along a linear isometry, as an actual
positive continuous linear map. The ambient representation need not leave
the range of the isometry invariant. -/
def compression (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) :
    A →P[ℂ] (H →L[ℂ] H) :=
  PositiveContinuousLinearMap.mk₀
    (LinearMap.mkContinuous
      { toFun := fun a =>
          U.toContinuousLinearMap.adjoint ∘L (rho a ∘L U.toContinuousLinearMap)
        map_add' := by
          intro a b
          simp only [map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
        map_smul' := by
          intro c a
          simp only [map_smul, ContinuousLinearMap.smul_comp,
            ContinuousLinearMap.comp_smul, RingHom.id_apply] }
      1 (fun a => by
        change ‖U.toContinuousLinearMap.adjoint ∘L
          (rho a ∘L U.toContinuousLinearMap)‖ ≤ 1 * ‖a‖
        simpa only [one_mul] using
          (norm_isometry_compression_le U (rho a)).trans
            (NonUnitalStarAlgHom.norm_apply_le rho a)))
    (by
      intro a ha
      change 0 ≤ U.toContinuousLinearMap.adjoint ∘L
        (rho a ∘L U.toContinuousLinearMap)
      apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
      simpa only [ContinuousLinearMap.comp_assoc] using
        (ContinuousLinearMap.nonneg_iff_isPositive.mp
          (map_nonneg rho ha)).adjoint_conj U.toContinuousLinearMap)

@[simp]
theorem compression_apply (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (a : A) :
    compression rho U a =
      U.toContinuousLinearMap.adjoint ∘L (rho a ∘L U.toContinuousLinearMap) := rfl

/-- Compression preserves the unit even when the isometry is not onto. -/
@[simp]
theorem compression_one (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) :
    compression rho U 1 = 1 := by
  rw [compression_apply, map_one]
  simpa only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using
    U.adjoint_comp_self

/-- The existing isometry-compression bound and representation
contractivity give the exact constant one. -/
theorem norm_compression_le (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (a : A) :
    ‖compression rho U a‖ ≤ ‖a‖ :=
  (norm_isometry_compression_le U (rho a)).trans
    (NonUnitalStarAlgHom.norm_apply_le rho a)

/-- An intertwining isometry makes compression a bimodule map over the
represented subalgebra. The left identity uses the existing adjoint
intertwiner theorem; no strong-limit multiplication is involved. -/
theorem compression_mul_mul
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (pi : Representation D H) (rho : Representation A K) (U : H →ₗᵢ[ℂ] K)
    (hU : ∀ (d : D) x, U (pi d x) = rho (d : A) (U x))
    (d e : D) (a : A) :
    compression rho U ((d : A) * a * (e : A)) =
      pi d * compression rho U a * pi e := by
  have hinter : StarAlgHom.Intertwines pi (rho.comp D.subtype)
      U.toContinuousLinearMap := by
    intro b
    ext x
    exact hU b x
  have hleft (b : D) (y : K) :
      U.toContinuousLinearMap.adjoint (rho (b : A) y) =
        pi b (U.toContinuousLinearMap.adjoint y) :=
    congrArg (fun T : K →L[ℂ] H => T y) (hinter.adjoint b)
  apply ContinuousLinearMap.ext
  intro x
  change U.toContinuousLinearMap.adjoint
      (rho ((d : A) * a * (e : A)) (U x)) =
    pi d (U.toContinuousLinearMap.adjoint (rho a (U (pi e x))))
  simp only [map_mul, ContinuousLinearMap.mul_apply]
  rw [hleft, ← hU e x]

/-- Every cyclic representation of a closed common-unit subalgebra has an
actual positive unital contractive extension with its bimodule equations.
The GNS state is constructed from the unit cyclic vector, and the ambient
state extension is supplied by the existing general state-extension theorem.
Neither a state-extension witness nor an isometry is an input hypothesis. -/
theorem exists_positive_bimodule_extension
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    [PartialOrder D] [StarOrderedRing D]
    (pi : Representation D H) (xi : H) (hxi : ‖xi‖ = 1)
    (hcyclic : DenseRange (StarAlgHom.orbitMap pi xi)) :
    ∃ P : A →P[ℂ] (H →L[ℂ] H),
      P 1 = 1 ∧ (∀ a : A, P (star a) = star (P a)) ∧
      (∀ a : A, ‖P a‖ ≤ ‖a‖) ∧
      (∀ d : D, P (d : A) = pi d) ∧
      ∀ (d e : D) (a : A),
        P ((d : A) * a * (e : A)) = pi d * P a * pi e := by
  let phi : D →L[ℂ] ℂ := vectorFunctional pi xi
  have hphi : phi ∈ stateSpace D := vectorFunctional_mem_stateSpace pi xi hxi
  have hA : (1 : A) ≠ 0 := by
    intro hzero
    have hD : (1 : D) = 0 := Subtype.ext hzero
    have hbad : (1 : ℂ) = 0 := by
      calc
        1 = phi 1 := hphi.2.symm
        _ = phi 0 := congrArg phi hD
        _ = 0 := map_zero phi
    exact one_ne_zero hbad
  letI : Nontrivial A := ⟨⟨1, 0, hA⟩⟩
  obtain ⟨psi, hpsi, hext⟩ := exists_state_extension_of_mem_stateSpace D phi hphi
  let rho := (positiveLinearMapOfMemStateSpace psi hpsi).gnsStarAlgHom
  let eta := stateGNSVector psi hpsi
  have hcoeff (d : D) : inner ℂ xi (pi d xi) =
      inner ℂ eta ((rho.comp D.subtype) d eta) := by
    calc
      inner ℂ xi (pi d xi) = phi d := rfl
      _ = psi (d : A) := (hext d).symm
      _ = inner ℂ eta ((rho.comp D.subtype) d eta) :=
        (inner_gnsStarAlgHom_stateGNSVector psi hpsi (d : A)).symm
  obtain ⟨U, -, hU⟩ := exists_isometry_of_eq_vector_state
    pi (rho.comp D.subtype) xi eta hcyclic hcoeff
  refine ⟨compression rho U, compression_one rho U,
    (fun a => map_star (compression rho U) a), norm_compression_le rho U, ?_, ?_⟩
  · intro d
    exact isometry_compression_eq_of_intertwines U (pi d) (rho (d : A)) (hU d)
  · intro d e a
    exact compression_mul_mul D pi rho U hU d e a

section PositiveTarget

variable {B : Type z} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Composition with a positive bimodule map on the bounded operators
gives the ambient-algebra map used in factor-extension arguments.

Continuity of the auxiliary map follows from positivity between C*-algebras.
Its normality is neither assumed nor concluded. The restriction equation at
the subalgebra unit supplies unitality, so a second unit hypothesis is also
unnecessary. -/
theorem exists_positive_bimodule_extension_of_positive_map
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    [PartialOrder D] [StarOrderedRing D]
    (pi : Representation D H) (xi : H) (hxi : ‖xi‖ = 1)
    (hcyclic : DenseRange (StarAlgHom.orbitMap pi xi))
    (sigma : D →⋆ₐ[ℂ] B) (E : (H →L[ℂ] H) →ₚ[ℂ] B)
    (hEpi : ∀ d : D, E (pi d) = sigma d)
    (hEbimodule : ∀ (d e : D) (T : H →L[ℂ] H),
      E (pi d * T * pi e) = sigma d * E T * sigma e) :
    ∃ P : A →P[ℂ] B,
      P 1 = 1 ∧ (∀ a : A, P (star a) = star (P a)) ∧
      (∀ d : D, P (d : A) = sigma d) ∧
      ∀ (d e : D) (a : A),
        P ((d : A) * a * (e : A)) = sigma d * P a * sigma e := by
  obtain ⟨Q, hQone, -, -, hQD, hQbimodule⟩ :=
    exists_positive_bimodule_extension D pi xi hxi hcyclic
  let Ec : (H →L[ℂ] H) →P[ℂ] B := PositiveContinuousLinearMap.ofClass E
  let P : A →P[ℂ] B := Ec.comp Q
  have hEone : E 1 = 1 := by simpa only [map_one] using hEpi (1 : D)
  refine ⟨P, ?_, (fun a => map_star P a), ?_, ?_⟩
  · change E (Q 1) = 1
    rw [hQone, hEone]
  · intro d
    change E (Q (d : A)) = sigma d
    rw [hQD, hEpi]
  · intro d e a
    change E (Q ((d : A) * a * (e : A))) = sigma d * E (Q a) * sigma e
    rw [hQbimodule, hEbimodule]

end PositiveTarget
end Representation
end MathlibAnnex.Analysis.CStarAlgebra
