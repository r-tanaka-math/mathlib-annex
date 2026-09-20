import MathlibAnnex.Analysis.CStarAlgebra.CompactModel
import MathlibAnnex.Analysis.CStarAlgebra.PureStateGNS.Ideal

/-!
# Consequences of ideal-separating pure GNS representations

The representation-capture hypothesis remains explicit.  The pure GNS
representation used to test a proper closed ideal is constructed in
`MathlibAnnex.CStarAlgebra.GNS.Ideal`; no KOS input occurs here.
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder

namespace MathlibAnnex.CStarAlgebra

open MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A faithful displayed irreducible representation which captures every
irreducible representation (in particular every canonical pure GNS
representation) forces ordinary closed-two-sided-ideal simplicity. -/
theorem isSimpleCStarAlgebra_of_uniqueIrreducibleModel [Nontrivial A]
    (pi : Representation A H)
    (hmodel : Representation.IsUniqueIrreducibleModel.{u, v, u} pi) :
    IsSimpleCStarAlgebra A := by
  refine ⟨inferInstance, ?_⟩
  intro I hclosed
  by_cases hI : I = ⊤
  · exact Or.inr hI
  · left
    apply le_antisymm
    · intro x hx
      obtain ⟨phi, hphi, _hpure, hirr, hann⟩ :=
        exists_irreducibleGNS_annihilating I hI hclosed
      let f : A →ₚ[ℂ] ℂ := positiveLinearMapOfMemStateSpace phi hphi
      obtain ⟨U, hU⟩ := hmodel.2.2 f.GNS f.gnsStarAlgHom hirr
      have hpi : pi x = 0 := by
        apply ContinuousLinearMap.ext
        intro y
        apply U.injective
        calc
          U (pi x y) = f.gnsStarAlgHom x (U y) := hU x y
          _ = 0 := by rw [hann x hx]; rfl
          _ = U 0 := (map_zero U).symm
      have hxzero : x = 0 := hmodel.1 (by simpa using hpi)
      exact hxzero
    · exact bot_le

end MathlibAnnex.CStarAlgebra
