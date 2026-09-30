import H0mework.Chemistry.LAlanineBandTaylor006.CenterBounds
import H0mework.Chemistry.LAlanineBandTaylor006.HullDensityData
import H0mework.Chemistry.LAlanineBandHighJet.Reports

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile006
open SourceFiniteData SourceSignedEvaluator WholeBandSource
noncomputable def fourthBounds : JetIndex → Pair := HighJet.densityBounds 1 Sample013.densityRows
noncomputable def restrictedField (f : FullBandCall) : IntervalParameterMap.FieldBox :=
  Taylor.fieldEnclosure Sample012.center (callBox f) Sample012.bounds fourthBounds
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeBandGenerated.Tile006
