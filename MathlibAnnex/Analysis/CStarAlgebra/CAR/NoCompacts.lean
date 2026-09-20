import MathlibAnnex.Analysis.CStarAlgebra.CompactPreimage
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Adapters
import MathlibAnnex.Analysis.CStarAlgebra.CAR.Simplicity
import MathlibAnnex.Analysis.CStarAlgebra.PureStateGNS.PureIrreducible

/-!
# Absence of compact operators in irreducible CAR representations

Simplicity makes every nonzero unital representation faithful.  Pulling the
compact operators back to a closed two-sided ideal then excludes every
nonzero compact image, using the already proved infinite-dimensionality of
the completed CAR algebra.
-/

set_option autoImplicit false

open MathlibAnnex.Analysis.CStarAlgebra

namespace MathlibAnnex.CStarAlgebra.CAR

universe v

variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A nonzero irreducible unital representation of the completed CAR algebra
is faithful. -/
theorem representation_injective
    (rho : Representation Limit H) (hrho : rho.IsIrreducible) :
    Function.Injective rho := by
  letI : Nontrivial H := Representation.nontrivial_of_isNonzero rho hrho.1
  exact rho.toRingHom.injective

/-- No nonzero element of the completed CAR algebra can have compact image in
a nonzero irreducible representation. -/
theorem eq_zero_of_isCompactOperator_image
    (rho : Representation Limit H) (hrho : rho.IsIrreducible)
    {a : Limit} (ha : IsCompactOperator (rho a)) : a = 0 := by
  exact MathlibAnnex.CStarAlgebra.eq_zero_of_isCompactOperator_of_injective
    not_finiteDimensional isSimpleCStarAlgebra_limit.2 rho
    (representation_injective rho hrho) ha

/-- The canonical GNS representation of a pure CAR state has no nonzero
compact operator in its represented range.  This is the concrete
no-compacts input used by the local pure-state approximation argument. -/
theorem eq_zero_of_isCompactOperator_pureGNS_image
    (phi : Limit →L[ℂ] ℂ) (hphi : phi ∈ MathlibAnnex.CStarAlgebra.stateSpace Limit)
    (hpure : MathlibAnnex.CStarAlgebra.IsPureState Limit phi) {a : Limit}
    (ha : IsCompactOperator
      ((MathlibAnnex.CStarAlgebra.positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom a)) :
    a = 0 := by
  let f := MathlibAnnex.CStarAlgebra.positiveLinearMapOfMemStateSpace phi hphi
  let xi : f.GNS := f.gnsCyclicVector
  have hxi : ‖xi‖ = 1 := PositiveLinearMap.norm_gnsCyclicVector f
    (MathlibAnnex.CStarAlgebra.positiveLinearMapOfMemStateSpace_one phi hphi)
  have hxi_ne : xi ≠ 0 := by
    intro hzero
    simpa [hzero] using hxi
  letI : Nontrivial f.GNS := nontrivial_of_ne xi 0 hxi_ne
  have hirr : Representation.IsIrreducible f.gnsStarAlgHom :=
    (Representation.isIrreducible_iff_starAlgHom f.gnsStarAlgHom).2
      (MathlibAnnex.CStarAlgebra.isIrreducible_pureState_gnsStarAlgHom phi hphi hpure)
  exact eq_zero_of_isCompactOperator_image f.gnsStarAlgHom hirr ha

/-- Range formulation of the preceding theorem: a compact operator belonging
to a pure CAR GNS image is the zero operator. -/
theorem eq_zero_of_mem_range_pureGNS_of_isCompactOperator
    (phi : Limit →L[ℂ] ℂ) (hphi : phi ∈ MathlibAnnex.CStarAlgebra.stateSpace Limit)
    (hpure : MathlibAnnex.CStarAlgebra.IsPureState Limit phi)
    {T : (MathlibAnnex.CStarAlgebra.positiveLinearMapOfMemStateSpace phi hphi).GNS →L[ℂ]
      (MathlibAnnex.CStarAlgebra.positiveLinearMapOfMemStateSpace phi hphi).GNS}
    (hT : T ∈ Set.range
      (MathlibAnnex.CStarAlgebra.positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom)
    (hcompact : IsCompactOperator T) : T = 0 := by
  obtain ⟨a, rfl⟩ := hT
  rw [eq_zero_of_isCompactOperator_pureGNS_image phi hphi hpure hcompact,
    map_zero]

end MathlibAnnex.CStarAlgebra.CAR
