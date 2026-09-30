import H0mework.Chemistry.LAlanineBandFlowReplay.Arithmetic
import H0mework.Chemistry.LAlanineBandFlowReplay.Consumer
import H0mework.Chemistry.LAlanineBandCall001.FieldField
import H0mework.Chemistry.LAlanineBandCall033.FieldField
import H0mework.Chemistry.LAlanineBandFlow.SeedEnclosure
import H0mework.Chemistry.LAlanineBandSource.Certified

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandActual

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap WholeBandSource WholeBandGeometry
open WholeBandReplay Set
noncomputable section

theorem first_initial_field (d : Direction) (x : Point)
    (inside : InRectangle (callBox (initialCallAt 0 d 0)) x) :
    FieldHolds (recordedCallField (initialCallAt 0 d 0)) x :=
  certified_actual_field (.inr d) x inside

theorem first_tube_field (d : Direction) (x : Point)
    (inside : InRectangle (callBox (tubeCallAt 0 d 0)) x) :
    FieldHolds (recordedCallField (tubeCallAt 0 d 0)) x := by
  fin_cases d
  · exact WholeBandCache.Call1.actual_field x inside
  · exact WholeBandCache.Call33.actual_field x inside

theorem source_first_step (d : Direction) : LocalStepLaw 0 d 0 :=
  steps_from_source_fields 0 d 0 (first_initial_field d) (first_tube_field d)

theorem cell0_seed_in_initial (d : Direction) (p : Point) (inside : p ∈ cellDomain 0) :
    InRectangle (initialBox 0 d 0) (cellSeed 0 p) := by
  fin_cases d
  · exact WholeBandSeed.cell_seed_in_initial 0 p inside
  · change InRectangle (initialBox 0 1 0) (cellSeed 0 p)
    rw [← common_initial 0]
    exact WholeBandSeed.cell_seed_in_initial 0 p inside

/-- The actual source seed generates both local curves and their certified source endpoints. -/
theorem source_cell0_first_curves (d : Direction) (p : Point) (inside : p ∈ cellDomain 0) :
    ∃ curve : ℝ → Point, curve 0 = cellSeed 0 p ∧
      (∀ t ∈ Icc 0 (stepSize : ℝ),
        HasDerivWithinAt curve (TrueTubeTrace.signedGradient (sign d) (curve t)) (Icc 0 (stepSize : ℝ)) t ∧
          InRectangle (tubeBox 0 d 0) (curve t)) ∧
      InRectangle (endpointBox 0 d 0) (curve stepSize) :=
  source_first_step d (cellSeed 0 p) (cell0_seed_in_initial d p inside)

theorem source_cell0_first_reenters (d : Direction) (p : Point) (inside : p ∈ cellDomain 0) :
    ∃ curve : ℝ → Point, curve 0 = cellSeed 0 p ∧
      (∀ t ∈ Icc 0 (stepSize : ℝ),
        HasDerivWithinAt curve (TrueTubeTrace.signedGradient (sign d) (curve t)) (Icc 0 (stepSize : ℝ)) t ∧
          InRectangle (tubeBox 0 d 0) (curve t)) ∧
      InRectangle (initialBox 0 d 1) (curve stepSize) := by
  obtain ⟨curve, starts, evolves, target⟩ := source_cell0_first_curves d p inside
  refine ⟨curve, starts, evolves, ?_⟩
  have join : endpointBox 0 d 0 = initialBox 0 d 1 := endpoint_next_initial 0 d (0 : Fin 15)
  exact join ▸ target

end
end LAlanine40K2025.BasinRefinement.WholeBandActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
