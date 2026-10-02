import H0mework.Versions.R2.Physics.Material.CartanAssembly
import H0mework.Versions.R2.Physics.ConstrainedCauchy.FixedFirstAssemblyP286ConnectionEvaluatorNormalForm
import H0mework.Physics.SafeCauchy.FixedClassicalCandidateFamily
import H0mework.Physics.SafeCauchy.FixedJointGlobalFiveSectorClosure

/-! Contact and physical source qualification of the whole-field Cartan
successor. Each retained nonzero coefficient is read on this same actual. -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace SaturationMonoid.PhysicsCore.Stage9C.Material

open ProofFreeRicherAnholonomicSource
open StageNineCClassicalWorldAcceptance
open StageNineConnectionSectorSourceBalance
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathGLCoframe
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyFirstAssemblyP286ConnectionEvaluatorNormalForm
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeClassicalWorldCandidateFamily
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalFiveSectorClosure
open StageNineDiracDualFormNativeFixedP506JointActionOriginPhysicalClosure
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzActionCanonicalPairUpdate
open StageNineP286ActionCauchySplit
open StageNineP286JointYangMillsGradientFlow
open StageNineSourceGeneratedMatterSpinActionUpdate
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineTopologicalLorentzThreeFormDuality
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7ExteriorBreakingYukawa

noncomputable section

private abbrev Source := positiveSmoothUnifiedSource
private abbrev SafeFinal := firstGravityCurrent.configuration

theorem firstAssemblyCartanActual_scalar_eq_safeFinal :
    firstAssemblyCartanActual.scalar = SafeFinal.scalar := rfl

theorem firstAssemblyCartanActual_matter_eq_safeFinal :
    firstAssemblyCartanActual.matter = SafeFinal.matter := rfl

theorem firstAssemblyCartanActual_conjugateMatter_eq_safeFinal :
    firstAssemblyCartanActual.conjugateMatter = SafeFinal.conjugateMatter := rfl

theorem firstAssemblyCartanActual_coframe_origin_eq_safeFinal :
    firstAssemblyCartanActual.coframe 0 = SafeFinal.coframe 0 := by
  change firstAssemblyGeneratedGravityFinal.coframe 0 = SafeFinal.coframe 0
  rw [show firstAssemblyGeneratedGravityFinal =
      sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailGLPathOperator
        Source firstAssemblyGeneratedP286Stage by rfl]
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailGLPathOperator_coframe,
    cartanECSynchronizedGravityTailGLCoframePathField_zero]
  unfold cartanECSynchronizedGravityTailCoframePathAnchor
    cartanECSynchronizedGravityTailBase
  rw [sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contact]
  exact congrFun (p286JointYangMillsEulerStep_coframe Source SafeFinal) 0

theorem firstAssemblyCartanActual_dynamicScalarSourceContact :
    DynamicScalarSourceContactAtOrigin Source firstAssemblyCartanActual := by
  change firstAssemblyCartanActual.scalar 0 = _
  rw [firstAssemblyCartanActual_scalar_eq_safeFinal]
  exact safeFinalClassicalWorldCandidateActual_dynamicScalarSourceContact

theorem firstAssemblyCartanActual_temporalHyperchargeMatterCurrent :
    p286MatterCurrentCoefficient Source firstAssemblyCartanActual
      (p286TemporalGaugeOneForm hyperchargeCoordinate) 0 = -1 := by
  calc
    _ = p286MatterCurrentCoefficient Source SafeFinal
        (p286TemporalGaugeOneForm hyperchargeCoordinate) 0 := by
      apply p286MatterCurrentCoefficient_eq_of_origin_contacts
      · exact firstAssemblyCartanActual_coframe_origin_eq_safeFinal
      · exact congrFun firstAssemblyCartanActual_matter_eq_safeFinal 0
      · exact congrFun firstAssemblyCartanActual_conjugateMatter_eq_safeFinal 0
    _ = -1 :=
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_temporalHyperchargeMatterCurrent

theorem firstAssemblyCartanActual_matterCurrentNonzeroAt_origin :
    MatterCurrentNonzeroAt Source firstAssemblyCartanActual 0 := by
  refine ⟨p286TemporalGaugeOneForm hyperchargeCoordinate, ?_⟩
  rw [firstAssemblyCartanActual_temporalHyperchargeMatterCurrent]
  norm_num

theorem firstAssemblyCartanActual_matterSpin_eq_half :
    lorentzMatterSpinSourceCoefficient Source firstAssemblyCartanActual
      (canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1)) 0 =
        1 / 2 := by
  apply spinProbeResponse_eq_half_of_origin
  · exact firstAssemblyCartanActual_coframe_origin_eq_safeFinal.trans
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_coframe_origin_one
  · rw [firstAssemblyCartanActual_matter_eq_safeFinal]
    exact fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_matter_origin_probe
  · rw [firstAssemblyCartanActual_conjugateMatter_eq_safeFinal]
    exact fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_conjugateMatter_origin_probe

theorem firstAssemblyCartanActual_matterSpinNonzeroAt_origin :
    MatterSpinNonzeroAt Source firstAssemblyCartanActual 0 := by
  refine ⟨canonicalLorentzSpatialBivectorOneForm (spinDirection 0 1), ?_⟩
  rw [firstAssemblyCartanActual_matterSpin_eq_half]
  norm_num

theorem firstAssemblyCartanActual_stressOrSpinNonzeroAt_origin :
    StressOrSpinNonzeroAt Source firstAssemblyCartanActual 0 :=
  Or.inr firstAssemblyCartanActual_matterSpinNonzeroAt_origin

theorem firstAssemblyCartanActual_sourceVacuum_nonzero :
    sourceGeneratedVacuumBase Source ≠ 0 :=
  positive_sourceGeneratedVacuumBase_nonzero

theorem firstAssemblyCartanActual_sourceYukawaMass_nonzero :
    exteriorYukawaMassMap (sourceGeneratedVacuumBase Source) ≠ 0 :=
  fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_yukawaMass

end
end SaturationMonoid.PhysicsCore.Stage9C.Material
