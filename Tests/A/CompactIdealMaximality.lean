import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CompactIdealMaximality

set_option autoImplicit false
open Set
open MathlibAnnex.CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w z
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type w} {K : ι → Type z}
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
variable [∀ i, CompleteSpace (K i)]

-- The approximation element lives in A and can be outside D. Actual
-- isometric intertwiners retain the restriction data on every Hilbert space.
example (D : NonUnitalStarSubalgebra ℂ A) [NonUnitalCStarAlgebra D]
    (pi : NonUnitalCStarRepresentation D H)
    (rho : ∀ i, NonUnitalCStarRepresentation A (K i))
    (U : ∀ i, H →ₗᵢ[ℂ] K i)
    (hU : ∀ (i : ι) (d : D) (x : H), U i (pi d x) = rho i (d : A) (U i x))
    (b : D)
    (hb : (b : A) ∈ closure (⋃ i, {a : A | IsCompactOperator (rho i a)})) :
    IsCompactOperator (pi b) := by
  apply isCompactOperator_of_mem_closure_iUnion_compactPreimageIdeal D pi rho U hU b
  have hcarrier (i : ι) : (compactPreimageIdeal (rho i) : Set A) =
      {a : A | IsCompactOperator (rho i a)} := by
    ext a
    exact mem_compactPreimageIdeal (rho i) a
  simpa only [hcarrier] using hb

-- This is the kernel-intersection conclusion for the constructed chain bound.
example [Nonempty ι]
    (D : NonUnitalStarSubalgebra ℂ A) [NonUnitalCStarAlgebra D]
    (pi : NonUnitalCStarRepresentation D H)
    (hfree : ∀ d : D, IsCompactOperator (pi d) → pi d = 0)
    (rho : ∀ i, NonUnitalCStarRepresentation A (K i))
    (hdir : Directed (· ≤ ·) (fun i => compactPreimageIdeal (rho i)))
    (U : ∀ i, H →ₗᵢ[ℂ] K i)
    (hU : ∀ (i : ι) (d : D) (x : H), U i (pi d x) = rho i (d : A) (U i x))
    (b : D) (hb : (b : A) ∈ compactPreimageDirectedSup rho hdir) : pi b = 0 := by
  apply map_eq_zero_of_mem_closure_iUnion_compactPreimageIdeal D pi hfree rho U hU b
  rwa [← coe_compactPreimageDirectedSup rho hdir]

-- Strict inclusion uses an actual nonzero compact image, not merely
-- nonzeroness of the representation or equality of two kernels.
example (pi : NonUnitalCStarRepresentation A H)
    (hnz : ∃ a : A, IsCompactOperator (pi a) ∧ pi a ≠ 0) :
    pi.kernelIdeal < compactPreimageIdeal pi :=
  pi.kernelIdeal_lt_compactPreimageIdeal hnz

-- Concrete state extensions discharge every isometry hypothesis in the
-- kernel-intersection statement; the ambient approximants need not lie in D.
example {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (D : StarSubalgebra ℂ B) [IsClosed (D : Set B)]
    [PartialOrder D] [StarOrderedRing D]
    (phi : D →L[ℂ] ℂ) (hphi : phi ∈ stateSpace D)
    (hfree : ∀ d : D,
      IsCompactOperator ((positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom d) →
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom d = 0)
    (psi : ι → B →L[ℂ] ℂ) (hpsi : ∀ i, psi i ∈ stateSpace B)
    (hext : ∀ (i : ι) (d : D), psi i d = phi d)
    (b : D)
    (hb : (b : B) ∈ closure (⋃ i, (compactPreimageIdeal
      (positiveLinearMapOfMemStateSpace (psi i) (hpsi i)).gnsStarAlgHom.toNonUnitalStarAlgHom :
        Set B))) :
    (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom b = 0 := by
  exact gns_map_eq_zero_of_mem_closure_iUnion_compactPreimageIdeal
    D phi hphi hfree psi hpsi hext b hb

end MathlibAnnex.Analysis.CStarAlgebra
