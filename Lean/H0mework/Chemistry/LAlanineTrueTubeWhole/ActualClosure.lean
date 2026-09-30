import H0mework.Chemistry.LAlanineTrueTubeWhole.ActualFullFlow
import H0mework.Chemistry.LAlanineTrueTubeWhole.ErrorActual
import H0mework.Chemistry.LAlanineTrueTube.ErrorStarts

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeActual

noncomputable section

structure WholeContinuationClosure : Prop where
  allFields : type_of% TrueTubeWholeMatrix.all_actual_call_fields
  localSteps : type_of% actual_step
  starts : type_of% wholeDirectionalFlow_starts
  original : type_of% wholeDirectionalFlow_original
  stays : type_of% wholeDirectionalFlow_stays
  initials : type_of% wholeDirectionalFlow_initials
  tubes : type_of% wholeDirectionalFlow_tubes
  endpoints : type_of% wholeDirectionalFlow_endpoints
  finalEndpoint : type_of% wholeDirectionalFlow_last
  firstPreserved : type_of% wholeDirectionalFlow_preserves_first
  fullOriginal : type_of% fullFlow_original
  fullStarts : type_of% fullFlow_starts
  fullStays : type_of% fullFlow_stays
  zeroDerivative : type_of% fullFlow_zero_derivative
  coverage : type_of% TrueTubeWholeChecks.sixteen_intervals_cover
  secondReentry : type_of% installed_target_reenters
  finiteInitial : type_of% TrueTubeError.finiteTrajectory_same_initial
  finiteDefect : type_of% TrueTubeError.actual_defect_norm_le
  commonField : type_of% TrueTubeHullMatrix.actual_source_field
  commonLipschitz : type_of% TrueTubeHull.common_lipschitz
  amplification : type_of% TrueTubeHull.half_window_amplification
  directionalError : type_of% TrueTubeWholeError.directional_error
  fullError : type_of% TrueTubeWholeError.full_error
  zeroError : type_of% TrueTubeWholeError.zero_error

theorem sourceGeneratedWholeContinuationClosure : WholeContinuationClosure where
  allFields := TrueTubeWholeMatrix.all_actual_call_fields
  localSteps := actual_step
  starts := wholeDirectionalFlow_starts
  original := wholeDirectionalFlow_original
  stays := wholeDirectionalFlow_stays
  initials := wholeDirectionalFlow_initials
  tubes := wholeDirectionalFlow_tubes
  endpoints := wholeDirectionalFlow_endpoints
  finalEndpoint := wholeDirectionalFlow_last
  firstPreserved := wholeDirectionalFlow_preserves_first
  fullOriginal := fullFlow_original
  fullStarts := fullFlow_starts
  fullStays := fullFlow_stays
  zeroDerivative := fullFlow_zero_derivative
  coverage := TrueTubeWholeChecks.sixteen_intervals_cover
  secondReentry := installed_target_reenters
  finiteInitial := TrueTubeError.finiteTrajectory_same_initial
  finiteDefect := TrueTubeError.actual_defect_norm_le
  commonField := TrueTubeHullMatrix.actual_source_field
  commonLipschitz := TrueTubeHull.common_lipschitz
  amplification := TrueTubeHull.half_window_amplification
  directionalError := TrueTubeWholeError.directional_error
  fullError := TrueTubeWholeError.full_error
  zeroError := TrueTubeWholeError.zero_error

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeActual
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
