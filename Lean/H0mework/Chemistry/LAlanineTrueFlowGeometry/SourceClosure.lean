import H0mework.Chemistry.LAlanineTrueFlowGeometry.SpatialIntegral

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometry

structure TrueFlowGeometryClosure : Prop where
  normalIsCross : type_of% seedNormal_eq_cross
  normalOrthogonal : type_of% seedNormal_dot_basis
  initialTransverse : type_of% original_gradient_transverse
  allCallLower : type_of% all_calls_transverse
  allCallTransverse : type_of% actual_call_transverse
  fullTransverse : type_of% fullFlow_transverse
  seedWidth : type_of% actual_seed_width_positive
  seedFrameInjective : type_of% seedFlowDerivative_injective
  seedRecovery : type_of% seed_coordinates_of_eq
  responseInjective : type_of% initialFlowDerivative_injective
  gradientTransport : type_of% initialFlowDerivative_gradient
  factorization : type_of% trueJacobian_flow_factorization
  jacobianInjective : type_of% trueJacobian_injective
  responseInverseRecognition : type_of% initialFlowDerivativeEquiv_coe
  jacobianInverseRecognition : type_of% trueJacobianEquiv_coe
  jacobianDeterminant : type_of% trueJacobian_det_ne_zero
  sectionInitial : type_of% fullFlow_plane_start
  sectionMonotone : type_of% fullFlow_plane_strictMono
  sameTime : type_of% fullFlow_meeting_time_eq
  parameterInjective : type_of% trueParameterMap_injOn
  uniqueDerivative : type_of% actualDerivative_eq_trueJacobian
  imageCompact : type_of% truePatch_compact
  imageNonempty : type_of% truePatch_nonempty
  imageMeasurable : type_of% truePatch_measurable
  spatialIntegral : type_of% true_spatial_integral_commutes
  integrability : type_of% true_spatial_integrable_iff
  nonnegativeIntegral : type_of% true_spatial_lintegral_commutes
  volumeJacobian : type_of% true_volume_eq_jacobian_lintegral
  volumePositive : type_of% truePatch_volume_pos
  volumeFinite : type_of% truePatch_volume_lt_top

theorem sourceGeneratedTrueFlowGeometryClosure : TrueFlowGeometryClosure where
  normalIsCross := seedNormal_eq_cross
  normalOrthogonal := seedNormal_dot_basis
  initialTransverse := original_gradient_transverse
  allCallLower := all_calls_transverse
  allCallTransverse := actual_call_transverse
  fullTransverse := fullFlow_transverse
  seedWidth := actual_seed_width_positive
  seedFrameInjective := seedFlowDerivative_injective
  seedRecovery := seed_coordinates_of_eq
  responseInjective := initialFlowDerivative_injective
  gradientTransport := initialFlowDerivative_gradient
  factorization := trueJacobian_flow_factorization
  jacobianInjective := trueJacobian_injective
  responseInverseRecognition := initialFlowDerivativeEquiv_coe
  jacobianInverseRecognition := trueJacobianEquiv_coe
  jacobianDeterminant := trueJacobian_det_ne_zero
  sectionInitial := fullFlow_plane_start
  sectionMonotone := fullFlow_plane_strictMono
  sameTime := fullFlow_meeting_time_eq
  parameterInjective := trueParameterMap_injOn
  uniqueDerivative := actualDerivative_eq_trueJacobian
  imageCompact := truePatch_compact
  imageNonempty := truePatch_nonempty
  imageMeasurable := truePatch_measurable
  spatialIntegral := true_spatial_integral_commutes
  integrability := true_spatial_integrable_iff
  nonnegativeIntegral := true_spatial_lintegral_commutes
  volumeJacobian := true_volume_eq_jacobian_lintegral
  volumePositive := truePatch_volume_pos
  volumeFinite := truePatch_volume_lt_top

end LAlanine40K2025.BasinRefinement.TrueFlowGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
