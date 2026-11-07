/- Quantitative Hilbert models assembled from the concrete Hilbert construction and
the specialized free-space complete-continuity criterion. This module gives the
coordinate-locality route; the general increment criterion is proved separately in
LipschitzFreeSpace/Localization/GeneralCriterion.
Execution evidence is recorded in the external receipts. -/
import BanachGeometry.LipschitzFreeSpace.HilbertLocality

noncomputable section
namespace BanachGeometry.HilbertSums
open Nonlinear HilbertFreeSpace

/-- Each field is filled by the actual B construction and the reduced generic upstream port. -/
def coordinateHilbertFreeSpaceData (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) :
    QuantitativeHilbertData c freeBundle hilbertBundle :=
  hilbertFreeSpaceDataOfLocality c hc (hilbertEquiv c hc hc') (hilbertEquiv_zero c hc hc') (norm_hilbertEquiv c hc hc')
    (fun z z' => (hilbertEquiv_bounds c hc hc' z z').1)
    (fun z z' => (hilbertEquiv_bounds c hc hc' z z').2)
    (hilbertDefect_localOrthogonality c hc hc')

/-- Unconditional quantitative Hilbert-model existence in its stated type; execution evidence is external. -/
theorem exists_quantitativeHilbertData_via_coordinates : HasQuantitativeHilbertModels := by
  intro c hc hc'
  exact ⟨freeBundle, hilbertBundle, ⟨coordinateHilbertFreeSpaceData c hc hc'⟩⟩

end BanachGeometry.HilbertSums
