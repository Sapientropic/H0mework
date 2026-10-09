import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCellDifferential.Nondegenerate

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0DifferentialSource

open WholeBandCell0Differential

structure WholeBandCell0DifferentialClosure : Prop where
  analyticBounds : type_of% cell0_analytic_bounds
  actualHessian : type_of% cell0_hessian_norm
  nearbyCube : type_of% path_near_cell0_in_cube
  pathHessian : type_of% cell0_pathHessian_norm
  volterraContractive : type_of% cell0_volterraHessian_norm_lt_one
  originalIntegral : type_of% cell0_rawPath_integral_equation
  initialResponse : type_of% cell0_rawPath_hasStrictFDerivAt
  responseIntegral : type_of% cell0_sourceResponse_integral_equation
  primitiveRecognition : type_of% cell0_responseCurve_is_actual
  responseVariational : type_of% cell0_sourceResponse_variational
  actualVariational : type_of% cell0_initialFlowDerivative_variational
  initialDerivative : type_of% cell0_initialFlow_hasStrictFDerivAt
  initialIdentity : type_of% cell0_initialFlowDerivative_zero
  responseInjective : type_of% cell0_initialFlowDerivative_injective
  gradientTransport : type_of% cell0_gradient_transport
  scaledPath : type_of% cell0_scaledActualPath_apply
  scaledIntegral : type_of% cell0_scaledActualPath_integral_equation
  scaledBound : type_of% cell0_scaledVolterra_norm_bound
  scaledResponse : type_of% cell0_scaledSolution_hasStrictFDerivAt
  scaledRecognition : type_of% cell0_scaledSolution_eq_rawPath
  parameterInput : type_of% cell0_parameterInput_hasFDerivAt
  endpointRecognition : type_of% cell0_scaled_endpoint_is_parameterMap
  actualParameterDerivative : type_of% cell0_actualMap_hasFDerivWithinAt
  domainRectangle : type_of% cell0_domain_eq_Icc
  domainWidths : type_of% cell0_axis_strict
  domainUnique : type_of% cell0_domain_uniqueDiffOn
  seedWidth : type_of% cell0_seed_width_positive
  seedInjective : type_of% cell0_seedFlowDerivative_injective
  timeColumn : type_of% cell0_trueJacobian_time_column
  seedColumns : type_of% cell0_trueJacobian_seed_column
  decomposition : type_of% cell0_trueJacobian_decomposition
  factorization : type_of% cell0_trueJacobian_flow_factorization
  jacobianInjective : type_of% cell0_trueJacobian_injective
  determinant : type_of% cell0_trueJacobian_det_ne_zero
  responseEquivRecognition : type_of% cell0_initialFlowDerivativeEquiv_coe
  jacobianEquivRecognition : type_of% cell0_trueJacobianEquiv_coe
  canonicalDerivative : type_of% cell0_trueJacobian_eq_fderivWithin

theorem sourceGeneratedWholeBandCell0DifferentialClosure : WholeBandCell0DifferentialClosure where
  analyticBounds := cell0_analytic_bounds
  actualHessian := cell0_hessian_norm
  nearbyCube := path_near_cell0_in_cube
  pathHessian := cell0_pathHessian_norm
  volterraContractive := cell0_volterraHessian_norm_lt_one
  originalIntegral := cell0_rawPath_integral_equation
  initialResponse := cell0_rawPath_hasStrictFDerivAt
  responseIntegral := cell0_sourceResponse_integral_equation
  primitiveRecognition := cell0_responseCurve_is_actual
  responseVariational := cell0_sourceResponse_variational
  actualVariational := cell0_initialFlowDerivative_variational
  initialDerivative := cell0_initialFlow_hasStrictFDerivAt
  initialIdentity := cell0_initialFlowDerivative_zero
  responseInjective := cell0_initialFlowDerivative_injective
  gradientTransport := cell0_gradient_transport
  scaledPath := cell0_scaledActualPath_apply
  scaledIntegral := cell0_scaledActualPath_integral_equation
  scaledBound := cell0_scaledVolterra_norm_bound
  scaledResponse := cell0_scaledSolution_hasStrictFDerivAt
  scaledRecognition := cell0_scaledSolution_eq_rawPath
  parameterInput := cell0_parameterInput_hasFDerivAt
  endpointRecognition := cell0_scaled_endpoint_is_parameterMap
  actualParameterDerivative := cell0_actualMap_hasFDerivWithinAt
  domainRectangle := cell0_domain_eq_Icc
  domainWidths := cell0_axis_strict
  domainUnique := cell0_domain_uniqueDiffOn
  seedWidth := cell0_seed_width_positive
  seedInjective := cell0_seedFlowDerivative_injective
  timeColumn := cell0_trueJacobian_time_column
  seedColumns := cell0_trueJacobian_seed_column
  decomposition := cell0_trueJacobian_decomposition
  factorization := cell0_trueJacobian_flow_factorization
  jacobianInjective := cell0_trueJacobian_injective
  determinant := cell0_trueJacobian_det_ne_zero
  responseEquivRecognition := cell0_initialFlowDerivativeEquiv_coe
  jacobianEquivRecognition := cell0_trueJacobianEquiv_coe
  canonicalDerivative := cell0_trueJacobian_eq_fderivWithin

end LAlanine40K2025.BasinRefinement.WholeBandCell0DifferentialSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
