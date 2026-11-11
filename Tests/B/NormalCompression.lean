import MathlibAnnex.Analysis.CStarAlgebra.TypeI.NormalCompression

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped CStarAlgebra ComplexOrder
open MathlibAnnex.Analysis.CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

example (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (a : A) :
    star (Representation.compression rho U a) * Representation.compression rho U a ≤
      Representation.compression rho U (star a * a) :=
  Representation.star_mul_compression_le rho U a

example (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, Representation.compression rho U a ∈ M)
    (T : (VonNeumannAlgebra.generated rho.range).toStarSubalgebra) :
    star (Representation.generatedCompression rho U M hsource T) *
        Representation.generatedCompression rho U M hsource T ≤
      Representation.generatedCompression rho U M hsource (star T * T) :=
  Representation.star_mul_generatedCompression_le rho U M hsource T

example (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, Representation.compression rho U a ∈ M)
    {T : K →L[ℂ] K} (hT : T ∈ VonNeumannAlgebra.generated rho.range) :
    U.toContinuousLinearMap.adjoint ∘L (T ∘L U.toContinuousLinearMap) ∈ M :=
  Representation.compression_mem_of_mem_generated rho U M hsource hT

example (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, Representation.compression rho U a ∈ M) :
    (VonNeumannAlgebra.generated rho.range).toStarSubalgebra →P[ℂ] M.toStarSubalgebra :=
  Representation.generatedCompression rho U M hsource

example (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, Representation.compression rho U a ∈ M) :
    Representation.generatedCompression rho U M hsource 1 = 1 :=
  Representation.generatedCompression_one rho U M hsource

example (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, Representation.compression rho U a ∈ M) (a : A) :
    (Representation.generatedCompression rho U M hsource
      ⟨rho a, VonNeumannAlgebra.subset_generated rho.range ⟨a, rfl⟩⟩ : H →L[ℂ] H) =
        Representation.compression rho U a :=
  Representation.generatedCompression_generator_coe rho U M hsource a

example (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, Representation.compression rho U a ∈ M)
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (hU : ∀ (d : D) x, U ((sigma d : H →L[ℂ] H) x) = rho (d : A) (U x))
    (d e : D) (T : (VonNeumannAlgebra.generated rho.range).toStarSubalgebra) :
    Representation.generatedCompression rho U M hsource
      (⟨rho (d : A), VonNeumannAlgebra.subset_generated rho.range ⟨(d : A), rfl⟩⟩ * T *
        ⟨rho (e : A), VonNeumannAlgebra.subset_generated rho.range ⟨(e : A), rfl⟩⟩) =
      sigma d * Representation.generatedCompression rho U M hsource T * sigma e :=
  Representation.generatedCompression_mul_mul rho U M hsource D sigma hU d e T

example (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, Representation.compression rho U a ∈ M)
    (s : Set (VonNeumannAlgebra.generated rho.range).toStarSubalgebra)
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ a ∈ s, 0 ≤ a) (hbdd : BddAbove s) :
    ∃ T : (VonNeumannAlgebra.generated rho.range).toStarSubalgebra,
      0 ≤ T ∧ IsLUB s T ∧
      IsLUB (Representation.generatedCompression rho U M hsource '' s)
        (Representation.generatedCompression rho U M hsource T) :=
  Representation.exists_isLUB_image_generatedCompression rho U M hsource s hne hdir hpos hbdd

example (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, Representation.compression rho U a ∈ M)
    (s : Set (VonNeumannAlgebra.generated rho.range).toStarSubalgebra)
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ a ∈ s, 0 ≤ a) (hbdd : BddAbove s)
    {T : (VonNeumannAlgebra.generated rho.range).toStarSubalgebra} (hT : IsLUB s T) :
    IsLUB (Representation.generatedCompression rho U M hsource '' s)
      (Representation.generatedCompression rho U M hsource T) :=
  Representation.isLUB_image_generatedCompression rho U M hsource s hne hdir hpos hbdd hT
