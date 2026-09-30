import H0mework.Chemistry.LAlanineWholeBandCell0.SpatialIntegral
import H0mework.Chemistry.LAlanineWholeBandCell0.BoundaryFaces
import H0mework.Chemistry.LAlanineWholeBandCell0.BoundaryCapFlux
import H0mework.Chemistry.LAlanineWholeBandCell0.ConservationSpatialBalance
import H0mework.Chemistry.LAlanineWholeBandCell0.CrossNoFold

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0SpatialSource

open WholeBandCell0Spatial WholeBandCell0Boundary WholeBandCell0Conservation WholeBandCrossGeometry

structure WholeBandCell0SpatialClosure : Prop where
  derivativeRecognition : type_of% cell0_actualDerivative_eq_trueJacobian
  mapContinuous : type_of% cell0ParameterMap_continuousOn
  imageCompact : type_of% cell0_truePatch_compact
  imageNonempty : type_of% cell0_truePatch_nonempty
  imageMeasurable : type_of% cell0_truePatch_measurable
  volumeFinite : type_of% cell0_truePatch_volume_lt_top
  volumePositive : type_of% cell0_truePatch_volume_pos
  integral : type_of% cell0_true_spatial_integral_commutes
  integrability : type_of% cell0_true_spatial_integrable_iff
  nonnegativeIntegral : type_of% cell0_true_spatial_lintegral_commutes
  volumeJacobian : type_of% cell0_true_volume_eq_jacobian_lintegral
  localExtensions : type_of% cell0_actual_local_extension
  boundaryImage : type_of% cell0_true_boundary_image
  sixFaces : type_of% cell0_true_boundary_eq_six_faces
  faceNonempty : type_of% cell0_trueSpatialFace_nonempty
  faceBoundary : type_of% cell0_trueSpatialFace_subset_boundary
  faceDerivative : type_of% cell0_trueFaceMap_hasFDerivWithinAt
  faceRank : type_of% cell0_trueFaceDerivative_rank_two
  faceIndependent : type_of% cell0_trueFaceTangents_linearIndependent
  areaNonzero : type_of% cell0_trueOrientedArea_ne_zero
  sideZero : type_of% cell0_trueSideFlux_zero
  areaCofactor : type_of% cell0_trueOrientedArea_eq_adjugate
  capDeterminant : type_of% cell0_trueCapFlux_eq_oriented_det
  capNonzero : type_of% cell0_trueCapFlux_ne_zero
  determinantEvolution : type_of% cell0_evolvingJacobian_determinant_evolution
  retimedActual : type_of% cell0_evolvingJacobian_eq_retimed
  initialJacobian : type_of% cell0_evolvingJacobian_zero
  timeFTC : type_of% cell0_actual_time_integral_eq_det_difference
  trajectoryCaps : type_of% cell0_actual_time_integral_eq_cap_flux
  seedDeterminant : type_of% cell0_seedFlowDerivative_det
  positiveJacobian : type_of% cell0_trueJacobian_det_pos
  upperCapPositive : type_of% cell0_true_upper_cap_flux_pos
  lowerCapNegative : type_of% cell0_true_lower_cap_flux_neg
  orientedIntegral : type_of% cell0_true_spatial_integral_oriented
  capRecognition : type_of% cell0_actualCapFlux_eq_trueFaceFlux
  pullbackIntegrability : type_of% cell0_actualLaplacianPullback_integrable
  sliceCaps : type_of% cell0_actual_slice_integral_eq_caps
  capIntegrability : type_of% cell0_actualCapFlux_sum_integrable
  spatialBalance : type_of% cell0_true_spatial_laplacian_eq_cap_flux
  cell16Domain : type_of% cell16_domain_is_original
  actualMeeting : type_of% cell0_cell16_actual_meeting_classification
  sourceSeparation : type_of% cell0_cell16_source_separation
  disjointImages : type_of% cell0_cell16_actual_images_disjoint
  pairInjective : type_of% paidPairMap_injective
  pairRange : type_of% paidPairMap_range

theorem sourceGeneratedWholeBandCell0SpatialClosure : WholeBandCell0SpatialClosure where
  derivativeRecognition := cell0_actualDerivative_eq_trueJacobian
  mapContinuous := cell0ParameterMap_continuousOn
  imageCompact := cell0_truePatch_compact
  imageNonempty := cell0_truePatch_nonempty
  imageMeasurable := cell0_truePatch_measurable
  volumeFinite := cell0_truePatch_volume_lt_top
  volumePositive := cell0_truePatch_volume_pos
  integral := cell0_true_spatial_integral_commutes
  integrability := cell0_true_spatial_integrable_iff
  nonnegativeIntegral := cell0_true_spatial_lintegral_commutes
  volumeJacobian := cell0_true_volume_eq_jacobian_lintegral
  localExtensions := cell0_actual_local_extension
  boundaryImage := cell0_true_boundary_image
  sixFaces := cell0_true_boundary_eq_six_faces
  faceNonempty := cell0_trueSpatialFace_nonempty
  faceBoundary := cell0_trueSpatialFace_subset_boundary
  faceDerivative := cell0_trueFaceMap_hasFDerivWithinAt
  faceRank := cell0_trueFaceDerivative_rank_two
  faceIndependent := cell0_trueFaceTangents_linearIndependent
  areaNonzero := cell0_trueOrientedArea_ne_zero
  sideZero := cell0_trueSideFlux_zero
  areaCofactor := cell0_trueOrientedArea_eq_adjugate
  capDeterminant := cell0_trueCapFlux_eq_oriented_det
  capNonzero := cell0_trueCapFlux_ne_zero
  determinantEvolution := cell0_evolvingJacobian_determinant_evolution
  retimedActual := cell0_evolvingJacobian_eq_retimed
  initialJacobian := cell0_evolvingJacobian_zero
  timeFTC := cell0_actual_time_integral_eq_det_difference
  trajectoryCaps := cell0_actual_time_integral_eq_cap_flux
  seedDeterminant := cell0_seedFlowDerivative_det
  positiveJacobian := cell0_trueJacobian_det_pos
  upperCapPositive := cell0_true_upper_cap_flux_pos
  lowerCapNegative := cell0_true_lower_cap_flux_neg
  orientedIntegral := cell0_true_spatial_integral_oriented
  capRecognition := cell0_actualCapFlux_eq_trueFaceFlux
  pullbackIntegrability := cell0_actualLaplacianPullback_integrable
  sliceCaps := cell0_actual_slice_integral_eq_caps
  capIntegrability := cell0_actualCapFlux_sum_integrable
  spatialBalance := cell0_true_spatial_laplacian_eq_cap_flux
  cell16Domain := cell16_domain_is_original
  actualMeeting := cell0_cell16_actual_meeting_classification
  sourceSeparation := cell0_cell16_source_separation
  disjointImages := cell0_cell16_actual_images_disjoint
  pairInjective := paidPairMap_injective
  pairRange := paidPairMap_range

end LAlanine40K2025.BasinRefinement.WholeBandCell0SpatialSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
