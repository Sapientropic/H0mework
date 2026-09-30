import H0mework.Chemistry.LAlanineTrueFlowConservation.SourceSpatialBalance

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowConservation

structure TrueFlowConservationClosure : Prop where
  entryEvolution : type_of% evolvingJacobian_variational
  sourceTrace : type_of% sourceHessian_trace
  determinantEvolution : type_of% evolvingJacobian_determinant_evolution
  actualMatrix : type_of% evolvingJacobian_is_actual
  actualDeterminant : type_of% evolvingJacobian_det_is_actual
  determinantContinuous : type_of% evolvingJacobian_det_continuous
  rateContinuous : type_of% signedVolumeRate_continuousOn
  timeDeterminantBalance : type_of% actual_time_integral_eq_det_difference
  retimedSeed : type_of% retime_seed
  retimedSeedFrame : type_of% retime_seedDerivative
  retimedResponse : type_of% retime_initialDerivative
  retimedMatrix : type_of% evolvingJacobian_eq_retimed
  capAddress : type_of% retime_eq_cap
  capDeterminant : type_of% capFlux_eq_evolvingJacobian
  timeCapBalance : type_of% actual_time_integral_eq_cap_flux
  seedDeterminant : type_of% seedFlowDerivative_det
  seedOrientation : type_of% seedFlowDerivative_det_pos
  initialMatrix : type_of% evolvingJacobian_zero
  evolvingOrientation : type_of% evolvingJacobian_det_pos
  jacobianOrientation : type_of% trueJacobian_det_pos
  upperCapOrientation : type_of% true_upper_cap_flux_pos
  lowerCapOrientation : type_of% true_lower_cap_flux_neg
  canonicalOrientation : type_of% actualDerivative_det_pos
  orientedChangeVariables : type_of% true_spatial_integral_oriented
  capRecognition : type_of% actualCapFlux_eq_trueFaceFlux
  pullbackIntegrable : type_of% actualLaplacianPullback_integrable
  sliceBalance : type_of% actual_slice_integral_eq_caps
  capSumIntegrable : type_of% actualCapFlux_sum_integrable
  spatialBalance : type_of% true_spatial_laplacian_eq_cap_flux

theorem sourceGeneratedTrueFlowConservationClosure : TrueFlowConservationClosure where
  entryEvolution := evolvingJacobian_variational
  sourceTrace := sourceHessian_trace
  determinantEvolution := evolvingJacobian_determinant_evolution
  actualMatrix := evolvingJacobian_is_actual
  actualDeterminant := evolvingJacobian_det_is_actual
  determinantContinuous := evolvingJacobian_det_continuous
  rateContinuous := signedVolumeRate_continuousOn
  timeDeterminantBalance := actual_time_integral_eq_det_difference
  retimedSeed := retime_seed
  retimedSeedFrame := retime_seedDerivative
  retimedResponse := retime_initialDerivative
  retimedMatrix := evolvingJacobian_eq_retimed
  capAddress := retime_eq_cap
  capDeterminant := capFlux_eq_evolvingJacobian
  timeCapBalance := actual_time_integral_eq_cap_flux
  seedDeterminant := seedFlowDerivative_det
  seedOrientation := seedFlowDerivative_det_pos
  initialMatrix := evolvingJacobian_zero
  evolvingOrientation := evolvingJacobian_det_pos
  jacobianOrientation := trueJacobian_det_pos
  upperCapOrientation := true_upper_cap_flux_pos
  lowerCapOrientation := true_lower_cap_flux_neg
  canonicalOrientation := actualDerivative_det_pos
  orientedChangeVariables := true_spatial_integral_oriented
  capRecognition := actualCapFlux_eq_trueFaceFlux
  pullbackIntegrable := actualLaplacianPullback_integrable
  sliceBalance := actual_slice_integral_eq_caps
  capSumIntegrable := actualCapFlux_sum_integrable
  spatialBalance := true_spatial_laplacian_eq_cap_flux

end LAlanine40K2025.BasinRefinement.TrueFlowConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
