import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.ContinuationChain
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.FieldsDirection1
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceRawPath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Continuation

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap WholeBandSource WholeBandReplay
open TrueTubeContinuation TrueTubeWholeChecks ContinuousGradient Set
noncomputable section

theorem positive_window_chain (initial : Point) (inside : InRectangle (initialBox 0 1 0) initial) :
    WindowChain 1 initial :=
  window_chain_from_fields 1 WholeBandCell0Fields.direction1_actual_field initial inside

theorem raw_positive_eq_window (initial : Point) (t : ℝ) (time : 0 ≤ t) :
    TrueFlowDifferential.rawFlow initial t = windowCurve 1 initial t := by
  apply LAlanineTrueTube.Signed.full_right
  · rw [windowCurve_starts, windowCurve_starts]
  · exact time

theorem positive_raw_tubes (initial : Point) (inside : InRectangle (initialBox 0 1 0) initial)
    (i : Step) (t : ℝ) (time : t ∈ Icc 0 (stepSize : ℝ)) :
    InRectangle (tubeBox 0 1 i) (TrueFlowDifferential.rawFlow initial (t + stepOffset i)) := by
  rw [raw_positive_eq_window _ _ (by linarith [stepOffset_nonneg i, time.1])]
  exact (positive_window_chain initial inside).tubes i t time

theorem positive_raw_fields (initial : Point) (inside : InRectangle (initialBox 0 1 0) initial)
    (i : Step) (t : ℝ) (time : t ∈ Icc 0 (stepSize : ℝ)) :
    FieldHolds (recordedCallField (tubeCallAt 0 1 i))
      (TrueFlowDifferential.rawFlow initial (t + stepOffset i)) := by
  rw [raw_positive_eq_window _ _ (by linarith [stepOffset_nonneg i, time.1])]
  exact (positive_window_chain initial inside).fields i t time

theorem positive_raw_endpoints (initial : Point) (inside : InRectangle (initialBox 0 1 0) initial)
    (i : Step) : InRectangle (endpointBox 0 1 i)
      (TrueFlowDifferential.rawFlow initial (stepOffset i + (stepSize : ℝ))) := by
  have stepPositive : 0 < (stepSize : ℝ) := Rat.cast_pos.mpr (cellArithmetic0 1 i).positive_step
  rw [raw_positive_eq_window _ _ (by linarith [stepOffset_nonneg i])]
  exact (positive_window_chain initial inside).endpoints i

theorem positive_raw_next_initial (initial : Point) (inside : InRectangle (initialBox 0 1 0) initial)
    (i : Fin 15) : InRectangle (initialBox 0 1 i.succ)
      (TrueFlowDifferential.rawFlow initial (stepOffset i.castSucc + (stepSize : ℝ))) :=
  (cellAdjacency0 1 i) ▸ positive_raw_endpoints initial inside i.castSucc

theorem positive_raw_residence (initial : Point) (inside : InRectangle (initialBox 0 1 0) initial)
    (t : ℝ) (time : t ∈ Icc (0 : ℝ) (1/2)) : TrueFlowDifferential.rawFlow initial t ∈ sourceCube := by
  rw [raw_positive_eq_window _ _ time.1]
  exact (positive_window_chain initial inside).residence t time

theorem positive_raw_final (initial : Point) (inside : InRectangle (initialBox 0 1 0) initial) :
    InRectangle (endpointBox 0 1 15) (TrueFlowDifferential.rawFlow initial (1/2 : ℝ)) := by
  rw [raw_positive_eq_window _ _ (by norm_num)]
  exact (positive_window_chain initial inside).final_endpoint

theorem positive_elapsed_start (i : Step) : (elapsedStart 0 1 i : ℝ) = stepOffset i := by
  have value : elapsedStart 0 1 i = sign 1 * (i.val : ℚ) * stepSize := (cellArithmetic0 1 i).time_start
  rw [value]
  simp only [Rat.cast_mul, Rat.cast_natCast, source_step_and_sign.2, TrueTubeChecks.directions.2,
    one_mul, stepOffset, source_step_and_sign.1]

theorem positive_elapsed_stop (i : Step) :
    (elapsedStop 0 1 i : ℝ) = stepOffset i + (stepSize : ℝ) := by
  have value : elapsedStop 0 1 i = sign 1 * ((i.val : ℚ) + 1) * stepSize := (cellArithmetic0 1 i).time_stop
  rw [value]
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, source_step_and_sign.2, TrueTubeChecks.directions.2,
    Rat.cast_one, one_mul, stepOffset, source_step_and_sign.1]
  ring

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Continuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
