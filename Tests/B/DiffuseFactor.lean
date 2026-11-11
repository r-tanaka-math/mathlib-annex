import MathlibAnnex.Analysis.CStarAlgebra.TypeI.DiffuseFactor

/-!
# Typed consumers for a diffuse non-type-I GNS factor

The test data remain explicit. The consumers include the original
normal-compression supremum statement and the final selected-state
endpoint, without a normality premise on the auxiliary positive map.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProduct
open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.CStarAlgebra.Representation

universe u v w

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

example (rho : Representation A H) :
    (NonUnitalCStarRepresentation.IsNondegenerate rho.toNonUnitalStarAlgHom) :=
  isNondegenerate_toNonUnitalStarAlgHom rho

example (rho : Representation A H) :
    VonNeumannAlgebra.generated (NonUnitalCStarRepresentation.unitization rho.toNonUnitalStarAlgHom).range =
      VonNeumannAlgebra.generated rho.range :=
  generated_unitization_toNonUnitalStarAlgHom rho

example (M : VonNeumannAlgebra H) (sigma : A →⋆ₐ[ℂ] M.toStarSubalgebra)
    (hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun a : A => ContinuousLinearMapWOT.ofCLM
        (sigma a : H →L[ℂ] H)))) :
    VonNeumannAlgebra.generated (M.toStarSubalgebra.subtype.comp sigma).range = M :=
  generated_eq_of_wot_dense M sigma hdense

-- The actual compression used in the factor endpoint still has the
-- existing LUB-existence and preservation theorem, with no abstract normality class.
example (rho : Representation A K) (U : H →ₗᵢ[ℂ] K)
    (M : VonNeumannAlgebra H) (hsource : ∀ a : A, compression rho U a ∈ M)
    (s : Set (VonNeumannAlgebra.generated rho.range).toStarSubalgebra)
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ a ∈ s, 0 ≤ a) (hbdd : BddAbove s) :
    ∃ T : (VonNeumannAlgebra.generated rho.range).toStarSubalgebra,
      0 ≤ T ∧ IsLUB s T ∧
        IsLUB (generatedCompression rho U M hsource '' s)
          (generatedCompression rho U M hsource T) :=
  exists_isLUB_image_generatedCompression rho U M hsource s hne hdir hpos hbdd

variable (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
variable [PartialOrder D] [StarOrderedRing D]
variable (M : VonNeumannAlgebra H) (hM : M.IsTypeII1)
variable (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
variable (hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
  closure (Set.range (fun d : D => ContinuousLinearMapWOT.ofCLM
    (sigma d : H →L[ℂ] H))))

include D M hM sigma hdense

example (rho : Representation A K)
    (hfactor : (VonNeumannAlgebra.generated rho.range).IsFactor)
    (U : H →ₗᵢ[ℂ] K) (xi : H) (hxi : xi ≠ 0)
    (hU : ∀ (d : D) x, U ((sigma d : H →L[ℂ] H) x) = rho (d : A) (U x))
    (hsource : ∀ a : A, compression rho U a ∈ M) :
    ¬ (VonNeumannAlgebra.generated rho.range).IsTypeI :=
  not_isTypeI_generated_of_isTypeII1_compression
    D M hM sigma hdense rho hfactor U xi hxi hU hsource

variable (xi : H) (hxi : ‖xi‖ = 1)
variable (hcyclic : DenseRange
  (StarAlgHom.orbitMap (M.toStarSubalgebra.subtype.comp sigma) xi))

include xi hxi hcyclic

example (P : A →P[ℂ] M.toStarSubalgebra)
    (hPD : ∀ d : D, P (d : A) = sigma d)
    (hPbi : ∀ (d e : D) (a : A),
      P ((d : A) * a * (e : A)) = sigma d * P a * sigma e)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hcoeff : ∀ a : A, phi a = inner ℂ xi ((P a : H →L[ℂ] H) xi))
    (hfactor : (VonNeumannAlgebra.generated
      (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsFactor) :
    ¬ (VonNeumannAlgebra.generated
      (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsTypeI :=
  not_isTypeI_gns_of_isTypeII1_of_positive_bimodule
    D M hM sigma hdense xi hxi hcyclic P hPD hPbi phi hphi hcoeff hfactor

variable (E : (H →L[ℂ] H) →ₚ[ℂ] M.toStarSubalgebra)
variable (hED : ∀ d : D, E (sigma d : H →L[ℂ] H) = sigma d)
variable (hEbi : ∀ (d e : D) (T : H →L[ℂ] H),
  E ((sigma d : H →L[ℂ] H) * T * (sigma e : H →L[ℂ] H)) =
    sigma d * E T * sigma e)

include E hED hEbi

-- Select one genuine state and preserve factor and non-type-I conclusions
-- for exactly the same GNS representation.
example :
    ∃ (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A),
      (VonNeumannAlgebra.generated
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsFactor ∧
      ¬ (VonNeumannAlgebra.generated
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsTypeI := by
  obtain ⟨P, phi, hphi, _hPone, _hPD, _hPbi, _hcoeff, _hext, hfactor, hnotI⟩ :=
    exists_positive_bimodule_non_typeI_factor_extension_of_positive_map
      D M hM sigma hdense xi hxi hcyclic E hED hEbi
  exact ⟨phi, hphi, hfactor, hnotI⟩

-- All retained equations remain available with that selected state.
example :
    ∃ (P : A →P[ℂ] M.toStarSubalgebra) (phi : A →L[ℂ] ℂ)
        (hphi : phi ∈ stateSpace A),
      P 1 = 1 ∧
      (∀ d : D, P (d : A) = sigma d) ∧
      (∀ (d e : D) (a : A), P ((d : A) * a * (e : A)) = sigma d * P a * sigma e) ∧
      (∀ a : A, phi a = inner ℂ xi ((P a : H →L[ℂ] H) xi)) ∧
      (phi : A → ℂ) ∈ (positiveBimoduleVectorFunctionalSet D M sigma xi).extremePoints ℝ ∧
      (VonNeumannAlgebra.generated
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsFactor ∧
      ¬ (VonNeumannAlgebra.generated
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsTypeI :=
  exists_positive_bimodule_non_typeI_factor_extension_of_positive_map
    D M hM sigma hdense xi hxi hcyclic E hED hEbi

