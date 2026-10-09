import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceSeedColumns
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceSideFlux
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceNontrivial

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

noncomputable section

structure TrueFlowDifferentialClosure : Prop where
  sourceMargin : type_of% source_margin_real
  sourceBudget : type_of% actual_volterra_budget
  originalPath : type_of% rawPath_eq_actualPath
  integralEquation : type_of% actualPath_integral_equation
  strictInitialDerivative : type_of% rawPath_hasStrictFDerivAt
  initialResponse : type_of% sourceResponse_integral_equation
  initialValue : type_of% sourceResponse_starts
  actualVariational : type_of% sourceResponse_actual_variational
  fixedTimeDerivative : type_of% initialFlow_hasStrictFDerivAt
  zeroTimeIdentity : type_of% initialFlowDerivative_zero
  parameterOccurrence : type_of% trueParameterMap_is_actual
  parameterDerivative : type_of% actualMap_hasFDerivWithinAt
  timeColumn : type_of% trueJacobian_time_column
  seedColumns : type_of% trueJacobian_seed_column
  decomposition : type_of% trueJacobian_decomposition
  faceDerivative : type_of% trueFaceMap_hasFDerivWithinAt
  faceTangents : type_of% trueFaceTangent_eq_column
  sideTangent : type_of% trueSideTangent_is_gradient
  sideFlux : type_of% trueSideFlux_zero
  nonemptyParameters : type_of% parameter_domain_nonempty
  nonzeroResponse : type_of% sourceResponse_ne_zero
  positiveTimeColumn : type_of% time_column_positive_at_seed
  nonzeroJacobian : type_of% trueJacobian_ne_zero_at_seed

theorem sourceGeneratedTrueFlowDifferentialClosure : TrueFlowDifferentialClosure where
  sourceMargin := source_margin_real
  sourceBudget := actual_volterra_budget
  originalPath := rawPath_eq_actualPath
  integralEquation := actualPath_integral_equation
  strictInitialDerivative := rawPath_hasStrictFDerivAt
  initialResponse := sourceResponse_integral_equation
  initialValue := sourceResponse_starts
  actualVariational := sourceResponse_actual_variational
  fixedTimeDerivative := initialFlow_hasStrictFDerivAt
  zeroTimeIdentity := initialFlowDerivative_zero
  parameterOccurrence := trueParameterMap_is_actual
  parameterDerivative := actualMap_hasFDerivWithinAt
  timeColumn := trueJacobian_time_column
  seedColumns := trueJacobian_seed_column
  decomposition := trueJacobian_decomposition
  faceDerivative := trueFaceMap_hasFDerivWithinAt
  faceTangents := trueFaceTangent_eq_column
  sideTangent := trueSideTangent_is_gradient
  sideFlux := trueSideFlux_zero
  nonemptyParameters := parameter_domain_nonempty
  nonzeroResponse := sourceResponse_ne_zero
  positiveTimeColumn := time_column_positive_at_seed
  nonzeroJacobian := trueJacobian_ne_zero_at_seed

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
