import H0mework.Chemistry.LAlanineTrueFlowBoundary.SourceFaces
import H0mework.Chemistry.LAlanineTrueFlowBoundary.SourceCapFlux

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowBoundary

structure TrueFlowBoundaryClosure : Prop where
  localDerivative : type_of% localExtension_strictDerivative
  localAgreement : type_of% localExtension_agrees
  localCharts : type_of% actual_local_extension
  frontierImage : type_of% true_boundary_image
  sixFaces : type_of% true_boundary_eq_six_faces
  facesNonempty : type_of% trueSpatialFace_nonempty
  facesOnBoundary : type_of% trueSpatialFace_subset_boundary
  facePointOnBoundary : type_of% trueFaceMap_mem_boundary
  sourceCorner : type_of% true_source_corner_on_boundary
  sideBoundaryFlux : type_of% true_side_boundary_flux
  faceDerivativeInjective : type_of% trueFaceDerivative_injective
  tangentIndependent : type_of% trueFaceTangents_linearIndependent
  tangentCrossNonzero : type_of% trueFaceTangents_cross_ne_zero
  orientedAreaNonzero : type_of% trueOrientedArea_ne_zero
  sideFluxWithArea : type_of% trueSideFlux_zero_with_area
  orientedAreaAdjugate : type_of% trueOrientedArea_eq_adjugate
  capFluxDeterminant : type_of% trueCapFlux_eq_oriented_det
  capFluxNonzero : type_of% trueCapFlux_ne_zero

theorem sourceGeneratedTrueFlowBoundaryClosure : TrueFlowBoundaryClosure where
  localDerivative := localExtension_strictDerivative
  localAgreement := localExtension_agrees
  localCharts := actual_local_extension
  frontierImage := true_boundary_image
  sixFaces := true_boundary_eq_six_faces
  facesNonempty := trueSpatialFace_nonempty
  facesOnBoundary := trueSpatialFace_subset_boundary
  facePointOnBoundary := trueFaceMap_mem_boundary
  sourceCorner := true_source_corner_on_boundary
  sideBoundaryFlux := true_side_boundary_flux
  faceDerivativeInjective := trueFaceDerivative_injective
  tangentIndependent := trueFaceTangents_linearIndependent
  tangentCrossNonzero := trueFaceTangents_cross_ne_zero
  orientedAreaNonzero := trueOrientedArea_ne_zero
  sideFluxWithArea := trueSideFlux_zero_with_area
  orientedAreaAdjugate := trueOrientedArea_eq_adjugate
  capFluxDeterminant := trueCapFlux_eq_oriented_det
  capFluxNonzero := trueCapFlux_ne_zero

end LAlanine40K2025.BasinRefinement.TrueFlowBoundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
