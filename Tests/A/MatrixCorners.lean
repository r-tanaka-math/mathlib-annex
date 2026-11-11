/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.MatrixCorners

noncomputable section
set_option autoImplicit false

open MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

example (v z : A) (i j : Bool) :
    star (hereditaryMatrixEntry v i j z) = hereditaryMatrixEntry v j i (star z) :=
  star_hereditaryMatrixEntry v i j z

example {c v z w : A} (hc : IsSelfAdjoint c)
    (hv : star v * v * c = c) (hcv : c * v = 0)
    (hz : z ∈ hereditarySubalgebra c) (hw : w ∈ hereditarySubalgebra c)
    (i j k l : Bool) :
    hereditaryMatrixEntry v i j z * hereditaryMatrixEntry v k l w =
      if j = k then hereditaryMatrixEntry v i l (z * w) else 0 :=
  hereditaryMatrixEntry_mul hc hv hcv hz hw i j k l

example {c v z : A} (hc : IsSelfAdjoint c) (hv : star v * v * c = c)
    (hz : z ∈ hereditarySubalgebra c) (i j : Bool) :
    ‖hereditaryMatrixEntry v i j z‖ = ‖z‖ :=
  norm_hereditaryMatrixEntry hc hv hz i j

example {a v z : A} (hv : v ∈ hereditarySubalgebra a)
    (hz : z ∈ hereditarySubalgebra a) (i j : Bool) :
    hereditaryMatrixEntry v i j z ∈ hereditarySubalgebra a :=
  hereditaryMatrixEntry_mem hv hz i j

-- Both off-diagonal entries and both siblings use this one transport.
example {c v w z : A} (hc : IsSelfAdjoint c) (hv : star v * v * c = c)
    (hw : w ∈ hereditarySubalgebra c) (hz : z ∈ hereditarySubalgebra c)
    (i j : Bool) :
    v * hereditaryMatrixEntry w i j z * star v =
      hereditaryMatrixEntry (v * w * star v) i j (v * z * star v) :=
  conjugate_hereditaryMatrixEntry hc hv hw hz i j

example {c v d w : A} (hc : IsSelfAdjoint c) (hv : star v * v * c = c)
    (hd : d ∈ hereditarySubalgebra c) (hw : w ∈ hereditarySubalgebra c)
    (hwd : star w * w * d = d) :
    star (v * w * star v) * (v * w * star v) * (v * d * star v) =
      v * d * star v :=
  conjugate_link_fix hc hv hd hw hwd

example {c v d w : A} (hv : star v * v * c = c)
    (hw : w ∈ hereditarySubalgebra c) (hdw : d * w = 0) :
    (v * d * star v) * (v * w * star v) = 0 :=
  conjugate_link_mul_eq_zero hv hw hdw
