import H0mework.Chemistry.LAlanineBandContinuation.DifferentialActual
import H0mework.Chemistry.LAlanineBandContinuation.Separation

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.FlowBounds
open WholeBandSource WholeBandReplay WholeBandTransverse WholeBandContinuation
open WholeBandContinuationDifferential WholeBandCell0Differential SourceSignedEvaluator TrueFlowGeometry

noncomputable def normalInput (r : Inputs) : ℚ := ∑ a : Fin 3,
  min (seedNormalQ a * (r.tubeField.gradient a).1)
    (seedNormalQ a * (r.tubeField.gradient a).2)

theorem normalInput_source (c : FullBandCell) (d : Direction) (i : Step) :
    normalInput (rowInput c d i) = normalLower (tubeCallAt c d i) := rfl

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.FlowBounds
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
