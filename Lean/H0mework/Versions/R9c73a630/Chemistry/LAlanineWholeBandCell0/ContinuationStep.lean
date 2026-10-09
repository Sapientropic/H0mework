import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.Step
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.Consumer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ContinuationWindow
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTubeWhole.ChecksTiming

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Continuation

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap WholeBandSource WholeBandReplay
open TrueTubeContinuation TrueTubeWholeChecks Set
noncomputable section

/-- The common source step is recognized on the existing window curve, without selecting a new flow. -/
theorem step_on_source_window (d : Direction) (initial : Point) (i : Step)
    (arithmetic : RowArithmetic 0 d i)
    (initialField : ∀ x, InRectangle (callBox (initialCallAt 0 d i)) x →
      FieldHolds (recordedCallField (initialCallAt 0 d i)) x)
    (tubeField : ∀ x, InRectangle (callBox (tubeCallAt 0 d i)) x →
      FieldHolds (recordedCallField (tubeCallAt 0 d i)) x)
    (atInitial : InRectangle (initialBox 0 d i) (windowCurve d initial (stepOffset i))) :
    (∀ t ∈ Icc 0 (stepSize : ℝ),
      InRectangle (tubeBox 0 d i) (windowCurve d initial (t + stepOffset i))) ∧
    InRectangle (endpointBox 0 d i) (windowCurve d initial (stepOffset i + stepSize)) :=
  WholeBandContinuation.step_on_source_window 0 d initial i arithmetic initialField tubeField atInitial

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Continuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
