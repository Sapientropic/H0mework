import H0mework.Chemistry.LAlanineTrueTubeWhole.ContinuationWindow
import H0mework.Chemistry.LAlanineTrueTubeWhole.ChecksSupport
import H0mework.Chemistry.LAlanineTrueTubeWhole.SourceData
import H0mework.Chemistry.LAlanineTrueTube.ActualRealization

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeContinuation

open SourceGaussianModel SourceSignedEvaluator TrueTubeSource TrueTubeActual TrueTubeTrace
open TrueTubeWholeSource TrueTubeWholeChecks ContinuousGradient Set
noncomputable section

private theorem first_call_box (d : Direction) : callBox (tubeCallAt d 0) = tubeBox d 0 := by
  fin_cases d <;> rfl

theorem window_preserves_first_curve (d : Direction) (initial : InitialAt d) :
    EqOn (firstCurve d initial) (windowCurve d initial.val) (Icc 0 (stepSize : ℝ)) := by
  have identification := windowCurve_local_identification d initial.val (firstCurve d initial)
    0 stepSize le_rfl (by rw [TrueTubeChecks.step_value]; norm_num)
    (fun t ht => ((firstCurve_spec d initial).2.1 t ht).1)
    (fun t ht => call_in_sourceCube (tubeCallAt d 0) _
      (first_call_box d ▸ ((firstCurve_spec d initial).2.1 t ht).2))
    (by rw [(firstCurve_spec d initial).1, windowCurve_starts])
  simpa only [add_zero] using identification

theorem window_preserves_first_target (d : Direction) (initial : InitialAt d) :
    windowCurve d initial.val stepSize = (firstTarget d initial).val := by
  exact (window_preserves_first_curve d initial
    ⟨Rat.cast_nonneg.mpr TrueTubeChecks.step_positive.le, le_rfl⟩).symm

end
end LAlanine40K2025.BasinRefinement.TrueTubeContinuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
