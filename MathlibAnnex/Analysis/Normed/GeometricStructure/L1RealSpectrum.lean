/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.Normed.GeometricStructure.L1RealPair
import MathlibAnnex.Analysis.Normed.GeometricStructure.SpectrumTriviality

/-!
# The real ℓ¹ geometric and primitive spectra

Closedness of pairs makes the component relation equality. The existing
concrete spectrum interfaces then identify both spectra with the original GSS.
There is no claim that this GSS is topologizable: closedness of every pair is
strictly weaker than the required finite-union law.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped lp

namespace NormedSpace

/-- The real ℓ¹ component relation is equality. -/
theorem geometricStructureClosure_l1_real_related_iff_eq
    (I J : GeometricStructureSpace ℝ ℓ¹(ℕ, ℝ)) :
    (geometricStructureClosure ℝ ℓ¹(ℕ, ℝ)).Related I J ↔ I = J :=
  ((geometricStructureClosure ℝ ℓ¹(ℕ, ℝ)).forall_related_iff_eq_iff).2
    (fun I J _ => isClosed_pair_geometricStructureClosure_l1_real I J) I J

/-- Each real ℓ¹ component is an actual singleton subset of the GSS. -/
theorem component_geometricStructureClosure_l1_real_eq_singleton
    (I : GeometricStructureSpace ℝ ℓ¹(ℕ, ℝ)) :
    (geometricStructureClosure ℝ ℓ¹(ℕ, ℝ)).component I = {I} :=
  (geometricStructureClosure ℝ ℓ¹(ℕ, ℝ)).component_eq_singleton
    geometricStructureClosure_l1_real_related_iff_eq I

/-- The primitive spectrum family consists of exactly the original GSS subsets. -/
theorem primitiveGeometricSpectrumFamily_l1_real_eq :
    primitiveGeometricSpectrumFamily ℝ ℓ¹(ℕ, ℝ) = geometricStructureFamily ℝ ℓ¹(ℕ, ℝ) :=
  primitiveGeometricSpectrumFamily_eq_of_related_iff_eq ℝ ℓ¹(ℕ, ℝ)
    geometricStructureClosure_l1_real_related_iff_eq

/-- The real ℓ¹ GSS-to-primitive-spectrum homeomorphism. -/
def geometricStructureHomeomorphPrimitiveSpectrumL1Real :
    ClosureSpace.Homeomorph (geometricStructureClosure ℝ ℓ¹(ℕ, ℝ))
      (primitiveGeometricSpectrumClosure ℝ ℓ¹(ℕ, ℝ)) :=
  geometricStructureHomeomorphPrimitiveSpectrumOfRelatedEq ℝ ℓ¹(ℕ, ℝ)
    geometricStructureClosure_l1_real_related_iff_eq

/-- The real ℓ¹ geometric-spectrum-to-GSS homeomorphism. -/
def geometricSpectrumHomeomorphGeometricStructureL1Real :
    ClosureSpace.Homeomorph (geometricSpectrumClosure ℝ ℓ¹(ℕ, ℝ))
      (geometricStructureClosure ℝ ℓ¹(ℕ, ℝ)) :=
  geometricSpectrumHomeomorphGeometricStructureOfRelatedEq ℝ ℓ¹(ℕ, ℝ)
    geometricStructureClosure_l1_real_related_iff_eq

/-- In the real ℓ¹ case gamma is bijective, not only surjective. -/
theorem geometricSpectrumToPrimitive_l1_real_bijective :
    Function.Bijective (geometricSpectrumToPrimitive ℝ ℓ¹(ℕ, ℝ)) :=
  geometricSpectrumToPrimitive_bijective_of_related_iff_eq ℝ ℓ¹(ℕ, ℝ)
    geometricStructureClosure_l1_real_related_iff_eq

end NormedSpace
