import H0mework.Chemistry.LAlanineWholeBandCell0.FieldsAll
import H0mework.Chemistry.LAlanineBandContinuation.Full
import H0mework.Chemistry.LAlanineWholeBandCell0.ContinuationReadout
import H0mework.Chemistry.LAlanineWholeBandCell0.ContinuationPositive

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Continuation

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap WholeBandSource WholeBandReplay
open WholeBandGeometry TrueTubeContinuation TrueTubeWholeChecks ContinuousGradient Set
noncomputable section

theorem cell0_full_starts (p : WholeBandActual.Cell0Point) :
    TrueFlowDifferential.rawFlow (cellSeed 0 p.val) 0 = cellSeed 0 p.val :=
  WholeBandContinuation.full_starts 0 p.val

theorem cell0_full_original (p : WholeBandActual.Cell0Point) :
    IsIntegralCurveOn (TrueFlowDifferential.rawFlow (cellSeed 0 p.val))
      (fun _ => sourceGradient) (Icc (-(1/2 : ℝ)) (1/2)) :=
  WholeBandContinuation.full_original 0 WholeBandCell0Fields.all_actual_fields p.val p.property

theorem cell0_full_sourceCube (p : WholeBandActual.Cell0Point) (t : ℝ)
    (time : t ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    TrueFlowDifferential.rawFlow (cellSeed 0 p.val) t ∈ sourceCube :=
  WholeBandContinuation.full_sourceCube 0 WholeBandCell0Fields.all_actual_fields p.val p.property t time

theorem cell0_full_tubes (p : WholeBandActual.Cell0Point) (d : Direction) (i : Step) (t : ℝ)
    (time : t ∈ Icc 0 (stepSize : ℝ)) :
    InRectangle (tubeBox 0 d i)
      (TrueFlowDifferential.rawFlow (cellSeed 0 p.val) ((sign d : ℝ) * (t + stepOffset i))) :=
  WholeBandContinuation.full_tubes 0 WholeBandCell0Fields.all_actual_fields p.val p.property d i t time

theorem cell0_full_fields (p : WholeBandActual.Cell0Point) (d : Direction) (i : Step) (t : ℝ)
    (time : t ∈ Icc 0 (stepSize : ℝ)) :
    FieldHolds (recordedCallField (tubeCallAt 0 d i))
      (TrueFlowDifferential.rawFlow (cellSeed 0 p.val) ((sign d : ℝ) * (t + stepOffset i))) :=
  WholeBandContinuation.full_fields 0 WholeBandCell0Fields.all_actual_fields p.val p.property d i t time

theorem cell0_full_field_cover (p : WholeBandActual.Cell0Point) (t : ℝ)
    (time : t ∈ Icc (-(1/2 : ℝ)) (1/2)) : ∃ d : Direction, ∃ i : Step,
    InRectangle (tubeBox 0 d i) (TrueFlowDifferential.rawFlow (cellSeed 0 p.val) t) ∧
    FieldHolds (recordedCallField (tubeCallAt 0 d i)) (TrueFlowDifferential.rawFlow (cellSeed 0 p.val) t) :=
  WholeBandContinuation.full_field_cover 0 WholeBandCell0Fields.all_actual_fields p.val p.property t time

theorem cell0_full_endpoints (p : WholeBandActual.Cell0Point) (d : Direction) (i : Step) :
    InRectangle (endpointBox 0 d i)
      (TrueFlowDifferential.rawFlow (cellSeed 0 p.val) (elapsedStop 0 d i)) :=
  WholeBandContinuation.full_endpoints 0 WholeBandCell0Fields.all_actual_fields p.val p.property d i

theorem cell0_full_next_initial (p : WholeBandActual.Cell0Point) (d : Direction) (i : Fin 15) :
    InRectangle (initialBox 0 d i.succ)
      (TrueFlowDifferential.rawFlow (cellSeed 0 p.val) (elapsedStop 0 d i.castSucc)) :=
  WholeBandContinuation.full_next_initial 0 WholeBandCell0Fields.all_actual_fields p.val p.property d i

theorem cell0_full_actual_caps (p : WholeBandActual.Cell0Point) :
    InRectangle (endpointBox 0 0 15) (TrueFlowDifferential.rawFlow (cellSeed 0 p.val) (-(1/2 : ℝ))) ∧
    InRectangle (endpointBox 0 1 15) (TrueFlowDifferential.rawFlow (cellSeed 0 p.val) (1/2 : ℝ)) :=
  WholeBandContinuation.full_actual_caps 0 WholeBandCell0Fields.all_actual_fields p.val p.property

theorem cell0_full_agrees_with_first (p : WholeBandActual.Cell0Point) :
    EqOn (WholeBandActual.fullFlow p) (TrueFlowDifferential.rawFlow (cellSeed 0 p.val)) WholeBandActual.firstWindow :=
  WholeBandActual.fullFlow_eq_sourceRaw p

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Continuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
