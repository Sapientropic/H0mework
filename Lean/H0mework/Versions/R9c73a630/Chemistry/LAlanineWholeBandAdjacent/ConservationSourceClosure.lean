import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandAdjacent.ConservationConsumer

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.BandConservationSource

open AdjacentConservation
structure BandConservationClosure : Prop where
  coreEvolution : type_of% WholeBandConservation.evolvingJacobian_determinant_evolution
  coreIntegral : type_of% WholeBandConservation.actual_time_integral_eq_det_difference
  coreRetime : type_of% WholeBandConservation.retime_sourceResponse
  coreOrientation : type_of% WholeBandConservation.actualJacobian_det_pos
  coreChart : type_of% WholeBandConservation.actual_local_extension_on_time_slab
  oldMatrix : type_of% WholeBandConservation.cell0_evolving_source_same
  oldRate : type_of% WholeBandConservation.cell0_volume_rate_same
  oldEvolution : type_of% WholeBandConservation.cell0_determinant_evolution_from_shared
  oldIntegral : type_of% WholeBandConservation.cell0_time_integral_from_shared
  oldOrientation : type_of% WholeBandConservation.cell0_positive_orientation_from_shared
  jointRetime : type_of% joint_evolvingJacobian_eq_retimed
  jointIntegral : type_of% joint_actual_time_integral
  jointOrientation : type_of% jointJacobian_det_pos
  localChart : type_of% actual_local_extension
  boundaryImage : type_of% actual_boundary_image
  sixFaces : type_of% actual_boundary_eq_six_faces
  faceNonempty : type_of% actualSpatialFace_nonempty
  faceDerivative : type_of% actualFaceMap_hasFDerivWithinAt
  faceRank : type_of% actualFaceDerivative_rank_two
  tangentsIndependent : type_of% actualFaceTangents_linearIndependent
  areaNonzero : type_of% actualOrientedArea_ne_zero
  sideFlux : type_of% actual_side_boundary_flux
  capDet : type_of% actualCapFlux_eq_oriented_det
  upperSign : type_of% actual_upper_cap_flux_pos
  lowerSign : type_of% actual_lower_cap_flux_neg
  pullbackIntegrable : type_of% laplacianPullback_integrable
  sliceIntegral : type_of% actual_slice_integral_eq_caps
  capIntegrable : type_of% actualCapFlux_sum_integrable
  spatialBalance : type_of% actual_spatial_laplacian_eq_cap_flux
  seamParameters : type_of% seamParameters_same
  seamIncidence : type_of% rightSeam_inside
  seamDerivative : type_of% rightSeamMap_actual_derivative
  seamMap : type_of% actualSeamMaps_same
  seamArea : type_of% actualSeamAreas_cancel
  seamFlux : type_of% actualSeamFluxes_cancel

theorem sourceGeneratedBandConservationClosure : BandConservationClosure where
  coreEvolution := WholeBandConservation.evolvingJacobian_determinant_evolution
  coreIntegral := WholeBandConservation.actual_time_integral_eq_det_difference
  coreRetime := WholeBandConservation.retime_sourceResponse
  coreOrientation := WholeBandConservation.actualJacobian_det_pos
  coreChart := WholeBandConservation.actual_local_extension_on_time_slab
  oldMatrix := WholeBandConservation.cell0_evolving_source_same
  oldRate := WholeBandConservation.cell0_volume_rate_same
  oldEvolution := WholeBandConservation.cell0_determinant_evolution_from_shared
  oldIntegral := WholeBandConservation.cell0_time_integral_from_shared
  oldOrientation := WholeBandConservation.cell0_positive_orientation_from_shared
  jointRetime := joint_evolvingJacobian_eq_retimed
  jointIntegral := joint_actual_time_integral
  jointOrientation := jointJacobian_det_pos
  localChart := actual_local_extension
  boundaryImage := actual_boundary_image
  sixFaces := actual_boundary_eq_six_faces
  faceNonempty := actualSpatialFace_nonempty
  faceDerivative := actualFaceMap_hasFDerivWithinAt
  faceRank := actualFaceDerivative_rank_two
  tangentsIndependent := actualFaceTangents_linearIndependent
  areaNonzero := actualOrientedArea_ne_zero
  sideFlux := actual_side_boundary_flux
  capDet := actualCapFlux_eq_oriented_det
  upperSign := actual_upper_cap_flux_pos
  lowerSign := actual_lower_cap_flux_neg
  pullbackIntegrable := laplacianPullback_integrable
  sliceIntegral := actual_slice_integral_eq_caps
  capIntegrable := actualCapFlux_sum_integrable
  spatialBalance := actual_spatial_laplacian_eq_cap_flux
  seamParameters := seamParameters_same
  seamIncidence := rightSeam_inside
  seamDerivative := rightSeamMap_actual_derivative
  seamMap := actualSeamMaps_same
  seamArea := actualSeamAreas_cancel
  seamFlux := actualSeamFluxes_cancel

end LAlanine40K2025.BasinRefinement.BandConservationSource

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
