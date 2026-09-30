import H0mework.Chemistry.LAlanineBandSource.Restriction
import H0mework.Chemistry.LAlanineTrueTube.ChecksSelfMap

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandReplay

open WholeBandSource SourceRectangle SourceSignedEvaluator IntervalParameterMap TrueTubeTrace
noncomputable section

/-- One projection of the common source, with no analytic success field. -/
structure Inputs where
  initial : Rectangle
  tube : Rectangle
  endpoint : Rectangle
  initialCall : Rectangle
  tubeCall : Rectangle
  firstField : FieldBox
  tubeField : FieldBox
  direction : ℚ
  step : ℚ
  start : ℚ
  stop : ℚ

def rowInput (c : FullBandCell) (d : Direction) (i : Step) : Inputs :=
  ⟨initialBox c d i, tubeBox c d i, endpointBox c d i,
    callBox (initialCallAt c d i), callBox (tubeCallAt c d i),
    recordedCallField (initialCallAt c d i), recordedCallField (tubeCallAt c d i),
    sign d, stepSize, elapsedStart c d i, elapsedStop c d i⟩

def signedTube (r : Inputs) := signedGradientPair r.direction r.tubeField
def signedInitial (r : Inputs) := signedGradientPair r.direction r.firstField
def acceleration (r : Inputs) := accelerationPair r.tubeField
def picardImage (r : Inputs) := vectorAdd r.initial (vectorScale (0, r.step) (signedTube r))
def eulerEndpoint (r : Inputs) := vectorAdd r.initial (vectorScale (point r.step) (signedTube r))
def secondEndpoint (r : Inputs) :=
  vectorAdd (vectorAdd r.initial (vectorScale (point r.step) (signedInitial r)))
    (vectorScale (point (r.step ^ 2 / 2)) (acceleration r))
def meetEndpoint (r : Inputs) : VectorPair := fun axis =>
  (max (eulerEndpoint r axis).1 (secondEndpoint r axis).1,
    min (eulerEndpoint r axis).2 (secondEndpoint r axis).2)

structure InputArithmetic (r : Inputs) (i : Step) : Prop where
  initial_join : ∀ axis, r.initialCall axis = r.initial axis
  tube_join : ∀ axis, r.tubeCall axis = r.tube axis
  initial_ordered : ∀ axis, (r.initial axis).1 ≤ (r.initial axis).2
  tube_ordered : ∀ axis, (r.tube axis).1 ≤ (r.tube axis).2
  endpoint_ordered : ∀ axis, (r.endpoint axis).1 ≤ (r.endpoint axis).2
  signed_ordered : ∀ axis, (signedTube r axis).1 ≤ (signedTube r axis).2
  acceleration_ordered : ∀ axis, (acceleration r axis).1 ≤ (acceleration r axis).2
  strict_picard : ∀ axis, (r.tube axis).1 < (picardImage r axis).1 ∧
    (picardImage r axis).2 < (r.tube axis).2
  exact_meet : ∀ axis, meetEndpoint r axis = r.endpoint axis
  strict_second : ∀ axis, (eulerEndpoint r axis).1 < (secondEndpoint r axis).1 ∧
    (secondEndpoint r axis).2 < (eulerEndpoint r axis).2
  contraction : r.step * fieldNormBound r.tubeField < 1
  initial_cube : ∀ axis, SourceFiniteData.boxCentre axis - SourceFiniteData.boxRadius ≤
    (r.initial axis).1 ∧ (r.initial axis).2 ≤ SourceFiniteData.boxCentre axis + SourceFiniteData.boxRadius
  tube_cube : ∀ axis, SourceFiniteData.boxCentre axis - SourceFiniteData.boxRadius ≤
    (r.tube axis).1 ∧ (r.tube axis).2 ≤ SourceFiniteData.boxCentre axis + SourceFiniteData.boxRadius
  positive_step : 0 < r.step
  unit : |r.direction| = 1 ∧ r.direction * r.direction = 1
  time_start : r.start = r.direction * i.val * r.step
  time_stop : r.stop = r.direction * (i.val + 1) * r.step

abbrev RowArithmetic (c : FullBandCell) (d : Direction) (i : Step) :=
  InputArithmetic (rowInput c d i) i

theorem second_endpoint_eq {r : Inputs} {i : Step} (h : InputArithmetic r i) :
    secondEndpoint r = r.endpoint := by
  funext axis
  rw [← h.exact_meet axis]
  exact Prod.ext (max_eq_right (h.strict_second axis).1.le).symm
    (min_eq_right (h.strict_second axis).2.le).symm

end
end LAlanine40K2025.BasinRefinement.WholeBandReplay
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
