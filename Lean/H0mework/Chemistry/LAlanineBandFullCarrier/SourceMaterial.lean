import H0mework.Chemistry.LAlanineBandAttractor.SourceA007Flow
import H0mework.Chemistry.LAlanineBandGlobalSource.FlowRecognition
import H0mework.Chemistry.LAlanineBandMaterial.Family
import H0mework.Chemistry.LAlanineBandCalculation.Actual
import H0mework.Chemistry.LAlanineBandFlowBounds.Producer
import H0mework.Chemistry.LAlanineBandSpatial.AtlasCover
import H0mework.Chemistry.LAlanineBandSpatial.AtlasVolume
import H0mework.Chemistry.LAlanineBandSpatial.AtlasConservationBalance
import H0mework.Chemistry.LAlanineBandSpatial.AtlasFaceRegular
import H0mework.Chemistry.LAlanineBandSpatial.AtlasSeamImages
import H0mework.Chemistry.LAlanineBandSpatial.AtlasSeamFaceIdentity

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandFullCarrier.Source
open SourceGaussianModel SourceFiniteData SourceSignedEvaluator WholeBandSource WholeBandGenerated
open WholeBandGeometry WholeBandContinuation WholeBandContinuationParameter WholeBandAtlas IntervalParameterMap
noncomputable section

/-- Actual source values, their shared calculation family, and the one physical carrier. -/
structure BandMaterial where
  evaluations : HighJet.Tile → TileEvaluation
  gaussianProgram : Basis → List HighJet.TermCode
  density : Matrix Basis Basis ℚ
  boxes : FullBandCall → Rectangle
  original : FullBandCall → FieldBox
  reported : FullBandCall → FieldBox
  domains : FullBandCell → Set Point
  maps : FullBandCell → Point → Point
  jacobians : FullBandCell → Point → Point →L[ℝ] Point
  parameterCarrier : Set Point
  parameterMap : Point → Point
  physicalCarrier : Set Point
  globalFlow : Point → ℝ → Point
  criticalPoint : Point
  attractingRegion : Set Point

def material : BandMaterial where
  evaluations := WholeBandGenerated.evaluations
  gaussianProgram := HighJet.registeredProgram
  density := densityMatrix
  boxes := callBox
  original := Calculation.originalField
  reported := recordedCallField
  domains := cellDomain
  maps := sourceParameterMap
  jacobians := trueJacobian
  parameterCarrier := bandDomain
  parameterMap := bandMap
  physicalCarrier := bandImage
  globalFlow := GlobalSource.flow
  criticalPoint := WholeBandAttractor.Atom007.actualZero.point
  attractingRegion := WholeBandAttractor.Atom007.attractingNeighborhood

theorem material_evaluations_sound (t : HighJet.Tile) : TileEvaluationSound t (material.evaluations t) :=
  evaluations_sound t

theorem material_actual_fields (f : FullBandCall) (x : Point) (inside : InRectangle (material.boxes f) x) :
    FieldHolds (material.reported f) x := all_actual_fields f x inside

theorem material_original_fields (f : FullBandCall) (x : Point) (inside : InRectangle (material.boxes f) x) :
    FieldHolds (material.original f) x := Calculation.all_original_fields f x inside

theorem fields : WholeBandAtlas.Fields := fun c d i role x hx => material_actual_fields (callAt c d i role) x hx

theorem bounds : WholeBandAtlas.Bounds := FlowBounds.all_cell_bounds
theorem positive : WholeBandAtlas.Normals := FlowBounds.all_positive_reports

end
end LAlanine40K2025.BasinRefinement.WholeBandFullCarrier.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
