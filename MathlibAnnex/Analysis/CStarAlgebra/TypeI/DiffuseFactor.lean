/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.CStarAlgebra.TypeI.ExtremalExtension
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.MinimalColumnTransfer

/-!
# A non-type-I factor from a diffuse positive bimodule test

The existing extreme-extension theorem produces a state with a genuine
factor GNS algebra. Here the II₁ test algebra rules out type I for that
particular generated algebra. The actual GNS intertwining isometry gives
the normal compression from the frozen `NormalCompression` provider.
The common test-algebra representations give the constructed central
corner lift from `CompressionCorner`, used by the minimal-column
contradiction in `MinimalColumnTransfer`.

The displayed auxiliary map on all bounded operators is only assumed
positive and bimodular with the prescribed restriction. Its normality is
not a hypothesis. The source algebra and all Hilbert spaces remain
arbitrary in size. The final theorem retains the actual state, positive
extension, restriction equations, extremality, and generated factor.

This is the bridge consuming a concrete diffuse test and auxiliary map.
CAR.TraceBimoduleMap constructs the auxiliary map used for the CAR specialization.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra.Representation

universe u v w

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Forgetting the unitality field does not make a unital representation
degenerate: the original unit tests the common kernel directly. -/
theorem isNondegenerate_toNonUnitalStarAlgHom (rho : Representation A H) :
    (NonUnitalCStarRepresentation.IsNondegenerate rho.toNonUnitalStarAlgHom) := by
  intro x hx
  have h : rho (1 : A) x = 0 := hx 1
  simpa only [map_one, one_apply_eq_self] using h

/-- Unitizing the forgotten unital representation does not change the
concrete generated von Neumann algebra on the same Hilbert space. The
existing original-range centralizer theorem supplies the entire argument. -/
theorem generated_unitization_toNonUnitalStarAlgHom (rho : Representation A H) :
    VonNeumannAlgebra.generated (NonUnitalCStarRepresentation.unitization rho.toNonUnitalStarAlgHom).range =
      VonNeumannAlgebra.generated rho.range := by
  apply SetLike.coe_injective
  change Set.centralizer
      (Set.centralizer (Set.range (NonUnitalCStarRepresentation.unitization rho.toNonUnitalStarAlgHom))) =
    Set.centralizer (Set.centralizer (Set.range rho))
  exact congrArg (fun S : Set (H →L[ℂ] H) ↦ Set.centralizer S)
    (NonUnitalCStarRepresentation.centralizer_range_unitization rho.toNonUnitalStarAlgHom)

/-- A unital test map with weakly dense concrete range generates the
specified algebra itself. This proves both inclusions in the original
operator carrier before any compression transport is applied. -/
theorem generated_eq_of_wot_dense
    (M : VonNeumannAlgebra H) (sigma : A →⋆ₐ[ℂ] M.toStarSubalgebra)
    (hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun a : A => ContinuousLinearMapWOT.ofCLM
        (sigma a : H →L[ℂ] H)))) :
    VonNeumannAlgebra.generated (M.toStarSubalgebra.subtype.comp sigma).range = M := by
  let tau : Representation A H := M.toStarSubalgebra.subtype.comp sigma
  apply le_antisymm
  · apply VonNeumannAlgebra.generated_le tau.range M
    rintro T ⟨a, rfl⟩
    exact (sigma a).property
  · intro T hT
    apply (VonNeumannAlgebra.mem_generated_iff_mem_wotClosure tau.range T).mpr
    have hsource : Set.range (fun a : A => ContinuousLinearMapWOT.ofCLM
        (sigma a : H →L[ℂ] H)) ⊆
        ContinuousLinearMapWOT.ofCLM '' (tau.range : Set (H →L[ℂ] H)) := by
      rintro _ ⟨a, rfl⟩
      exact ⟨tau a, ⟨a, rfl⟩, rfl⟩
    exact closure_mono hsource (hdense T hT)

/-- A represented ambient factor cannot be type I when its actual
isometric compression has the specified II₁ target and an intertwined,
weakly dense common-unit test algebra.

The compression is the previously constructed positive normal map on the
entire generated algebra. Both test representations are proved
nondegenerate, and their generated algebras are identified here. The
central-corner inverse and its bounded strong continuity are constructed
inside the consumed transfer theorem, without an extra lift hypothesis. -/
theorem not_isTypeI_generated_of_isTypeII1_compression
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    [PartialOrder D] [StarOrderedRing D]
    (M : VonNeumannAlgebra H) (hM : M.IsTypeII1)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun d : D => ContinuousLinearMapWOT.ofCLM
        (sigma d : H →L[ℂ] H))))
    (rho : Representation A K)
    (hfactor : (VonNeumannAlgebra.generated rho.range).IsFactor)
    (U : H →ₗᵢ[ℂ] K) (xi : H) (hxi : xi ≠ 0)
    (hU : ∀ (d : D) x, U ((sigma d : H →L[ℂ] H) x) = rho (d : A) (U x))
    (hsource : ∀ a : A, compression rho U a ∈ M) :
    ¬ (VonNeumannAlgebra.generated rho.range).IsTypeI := by
  let tau : Representation D H := M.toStarSubalgebra.subtype.comp sigma
  let rhoD : Representation D K := rho.comp D.subtype
  have htau : (NonUnitalCStarRepresentation.IsNondegenerate tau.toNonUnitalStarAlgHom) :=
    isNondegenerate_toNonUnitalStarAlgHom tau
  have hrhoD : (NonUnitalCStarRepresentation.IsNondegenerate rhoD.toNonUnitalStarAlgHom) :=
    isNondegenerate_toNonUnitalStarAlgHom rhoD
  have htarget :
      VonNeumannAlgebra.generated (NonUnitalCStarRepresentation.unitization tau.toNonUnitalStarAlgHom).range = M :=
    (generated_unitization_toNonUnitalStarAlgHom tau).trans
      (generated_eq_of_wot_dense M sigma hdense)
  have hlarge :
      VonNeumannAlgebra.generated (NonUnitalCStarRepresentation.unitization rhoD.toNonUnitalStarAlgHom).range ≤
        VonNeumannAlgebra.generated rho.range := by
    rw [generated_unitization_toNonUnitalStarAlgHom rhoD]
    apply VonNeumannAlgebra.generated_mono
    rintro T ⟨d, rfl⟩
    exact ⟨(d : A), rfl⟩
  have transfer := not_isTypeI_of_isTypeII1_generated_compression
    rhoD.toNonUnitalStarAlgHom hrhoD tau.toNonUnitalStarAlgHom htau
    (VonNeumannAlgebra.generated rho.range) hlarge
  rw [htarget] at transfer
  apply transfer hM hfactor (generatedCompression rho U M hsource) U hxi
  · intro T
    exact generatedCompression_apply_coe rho U M hsource T
  · intro d
    apply ContinuousLinearMap.ext
    intro x
    exact (hU d x).symm

/-- For an actual positive bimodule extension and its vector state, the
existing pointed GNS isometry supplies every compression input. Once the
GNS algebra is known to be a factor, the displayed II₁ test makes it
non-type-I. No GNS isometry, inverse, or normal extension is assumed. -/
theorem not_isTypeI_gns_of_isTypeII1_of_positive_bimodule
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    [PartialOrder D] [StarOrderedRing D]
    (M : VonNeumannAlgebra H) (hM : M.IsTypeII1)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun d : D => ContinuousLinearMapWOT.ofCLM
        (sigma d : H →L[ℂ] H))))
    (xi : H) (hxi : ‖xi‖ = 1)
    (hcyclic : DenseRange
      (StarAlgHom.orbitMap (M.toStarSubalgebra.subtype.comp sigma) xi))
    (P : A →P[ℂ] M.toStarSubalgebra)
    (hPD : ∀ d : D, P (d : A) = sigma d)
    (hPbi : ∀ (d e : D) (a : A),
      P ((d : A) * a * (e : A)) = sigma d * P a * sigma e)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hcoeff : ∀ a : A, phi a = inner ℂ xi ((P a : H →L[ℂ] H) xi))
    (hfactor : (VonNeumannAlgebra.generated
      (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsFactor) :
    ¬ (VonNeumannAlgebra.generated
      (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsTypeI := by
  let rho := (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom
  obtain ⟨U, _hpoint, hU, hcompression⟩ :=
    exists_isometry_compression_eq_of_positive_bimodule
      D M sigma xi hcyclic P hPD hPbi phi hphi hcoeff
  have hsource (a : A) : compression rho U a ∈ M := by
    rw [hcompression]
    exact (P a).property
  have hxi0 : xi ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hxi
    exact zero_ne_one hxi
  exact not_isTypeI_generated_of_isTypeII1_compression
    D M hM sigma hdense rho hfactor U xi hxi0 hU hsource

/-- A concrete cyclic weakly dense II₁ test and a positive bimodule map on
its bounded operators produce a genuine non-type-I factor state of the
ambient algebra. All extension equations and the selected extremality are
retained together with that state.

The auxiliary positive map is a displayed mathematical input, with no
normality premise. In the CAR application that input must come from the
assigned concrete CAR provider; it is not supplied by this theorem. -/
theorem exists_positive_bimodule_non_typeI_factor_extension_of_positive_map
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    [PartialOrder D] [StarOrderedRing D]
    (M : VonNeumannAlgebra H) (hM : M.IsTypeII1)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun d : D => ContinuousLinearMapWOT.ofCLM
        (sigma d : H →L[ℂ] H))))
    (xi : H) (hxi : ‖xi‖ = 1)
    (hcyclic : DenseRange
      (StarAlgHom.orbitMap (M.toStarSubalgebra.subtype.comp sigma) xi))
    (E : (H →L[ℂ] H) →ₚ[ℂ] M.toStarSubalgebra)
    (hED : ∀ d : D, E (sigma d : H →L[ℂ] H) = sigma d)
    (hEbi : ∀ (d e : D) (T : H →L[ℂ] H),
      E ((sigma d : H →L[ℂ] H) * T * (sigma e : H →L[ℂ] H)) =
        sigma d * E T * sigma e) :
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
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsTypeI := by
  obtain ⟨P, phi, hphi, hPone, hPD, hPbi, hcoeff, hext, hfactor⟩ :=
    exists_positive_bimodule_factor_extension_of_positive_map
      D M hM.1 sigma hdense xi hxi hcyclic E hED hEbi
  exact ⟨P, phi, hphi, hPone, hPD, hPbi, hcoeff, hext, hfactor,
    not_isTypeI_gns_of_isTypeII1_of_positive_bimodule
      D M hM sigma hdense xi hxi hcyclic P hPD hPbi phi hphi hcoeff hfactor⟩

end MathlibAnnex.Analysis.CStarAlgebra.Representation

