import H0mework.Chemistry.LAlanineWholeBandCell1.FieldsAll
import H0mework.Chemistry.LAlanineBandContinuation.Full

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell1Actual

open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandContinuation TrueFlowDifferential
open SourceSignedEvaluator IntervalParameterMap ContinuousGradient Set
noncomputable section

abbrev Cell1Point := {p : Point // p ∈ cellDomain 1}

theorem cell1_source_fields : ∀ d, DirectionFields 1 d := WholeBandCell1Fields.all_actual_fields

theorem cell1_full_original (p : Cell1Point) :
    IsIntegralCurveOn (rawFlow (cellSeed 1 p.val)) (fun _ => sourceGradient) (Icc (-(1/2 : ℝ)) (1/2)) :=
  full_original 1 cell1_source_fields p.val p.property

theorem cell1_full_field_cover (p : Cell1Point) (t : ℝ) (time : t ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    ∃ d : Direction, ∃ i : Step,
      InRectangle (tubeBox 1 d i) (rawFlow (cellSeed 1 p.val) t) ∧
      FieldHolds (recordedCallField (tubeCallAt 1 d i)) (rawFlow (cellSeed 1 p.val) t) :=
  full_field_cover 1 cell1_source_fields p.val p.property t time

theorem cell1_full_initials (p : Cell1Point) (d : Direction) (i : Step) :
    InRectangle (initialBox 1 d i) (rawFlow (cellSeed 1 p.val) (elapsedStart 1 d i)) :=
  full_initials 1 cell1_source_fields p.val p.property d i

theorem cell1_full_endpoints (p : Cell1Point) (d : Direction) (i : Step) :
    InRectangle (endpointBox 1 d i) (rawFlow (cellSeed 1 p.val) (elapsedStop 1 d i)) :=
  full_endpoints 1 cell1_source_fields p.val p.property d i

theorem cell1_full_next_initial (p : Cell1Point) (d : Direction) (i : Fin 15) :
    InRectangle (initialBox 1 d i.succ) (rawFlow (cellSeed 1 p.val) (elapsedStop 1 d i.castSucc)) :=
  full_next_initial 1 cell1_source_fields p.val p.property d i

theorem cell1_full_caps (p : Cell1Point) :
    InRectangle (endpointBox 1 0 15) (rawFlow (cellSeed 1 p.val) (-(1/2 : ℝ))) ∧
    InRectangle (endpointBox 1 1 15) (rawFlow (cellSeed 1 p.val) (1/2 : ℝ)) :=
  full_actual_caps 1 cell1_source_fields p.val p.property

end
end LAlanine40K2025.BasinRefinement.WholeBandCell1Actual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
