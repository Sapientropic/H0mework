import H0mework.Chemistry.LAlanineBandFlowReplay.Consumer
import H0mework.Chemistry.LAlanineTrueTubeWhole.ContinuationWindow
import H0mework.Chemistry.LAlanineTrueTubeWhole.ChecksTiming

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuation

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap WholeBandSource WholeBandReplay
open TrueTubeContinuation TrueTubeWholeChecks Set
noncomputable section

/-- The common source step is recognized on the existing window curve, without selecting a new flow. -/
theorem step_on_source_window (c : FullBandCell) (d : Direction) (initial : Point) (i : Step)
    (arithmetic : RowArithmetic c d i)
    (initialField : ∀ x, InRectangle (callBox (initialCallAt c d i)) x →
      FieldHolds (recordedCallField (initialCallAt c d i)) x)
    (tubeField : ∀ x, InRectangle (callBox (tubeCallAt c d i)) x →
      FieldHolds (recordedCallField (tubeCallAt c d i)) x)
    (atInitial : InRectangle (initialBox c d i) (windowCurve d initial (stepOffset i))) :
    (∀ t ∈ Icc 0 (stepSize : ℝ),
      InRectangle (tubeBox c d i) (windowCurve d initial (t + stepOffset i))) ∧
    InRectangle (endpointBox c d i) (windowCurve d initial (stepOffset i + stepSize)) := by
  obtain ⟨curve, starts, evolves, endpoint⟩ :=
    step_from_arithmetic_and_fields c d i arithmetic initialField tubeField _ atInitial
  have identification := windowCurve_local_identification d initial curve (stepOffset i) stepSize
    (stepOffset_nonneg i) (by simpa only [source_step_and_sign.1] using stepOffset_end_le i)
    (fun t ht => by simpa only [source_step_and_sign.2] using (evolves t ht).1)
    (fun t ht => WholeBandReplay.tube_in_sourceCube arithmetic _ (evolves t ht).2) starts
  constructor
  · intro t ht
    have same : curve t = windowCurve d initial (t + stepOffset i) := identification ht
    rw [← same]
    exact (evolves t ht).2
  · have atEnd := identification
      (show (stepSize : ℝ) ∈ Icc 0 (stepSize : ℝ) from
        ⟨(Rat.cast_pos.mpr arithmetic.positive_step).le, le_rfl⟩)
    change curve stepSize = windowCurve d initial ((stepSize : ℝ) + stepOffset i) at atEnd
    rw [add_comm (stepOffset i), ← atEnd]
    exact endpoint

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
