import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceReferenceContact
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeNativeSymbol
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeContactRead
import Lean.Elab.Command
import Lean.Util.FoldConsts
open Lean Elab Command
private def usedConstants (info : ConstantInfo) : Array Name := Id.run do
  let mut deps := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    deps := deps ++ value.getUsedConstants
  match info with
  | .inductInfo value => deps := deps ++ value.ctors.toArray
  | .recInfo value =>
      for rule in value.rules do deps := deps ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return deps

private def completeClosure (env : Environment) (cache : IO.Ref (NameMap (Array Name)))
    (roots : List Name) : IO NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      seen := seen.insert name
      let memo ← cache.get
      let children ← match memo.find? name with
        | some deps => pure deps
        | none => do
          let deps := match env.checked.get.find? name with
            | some info => usedConstants info
            | none => #[]
          cache.modify (fun old => old.insert name deps)
          pure deps
      pending := children.toList ++ pending
  return seen

private def checkClosure (env : Environment) (cache : IO.Ref (NameMap (Array Name))) (roots : List Name) : CommandElabM (Nat × Nat × Nat) := do
  let closure ← liftIO (completeClosure env cache roots)
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut opaqueCount := 0
  let mut axiomCount := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError m!"UNKNOWN_NODE {name}"
    if info.isUnsafe then throwError m!"UNSAFE_NODE {name}"
    if info.isPartial then throwError m!"PARTIAL_NODE {name}"
    match info with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
      unless (info.value? (allowOpaque := true)).isSome do throwError m!"UNREAD_VALUE {name}"
    | _ => pure ()
    if let .opaqueInfo _ := info then opaqueCount := opaqueCount + 1
    if let .axiomInfo _ := info then
      axiomCount := axiomCount + 1
      unless allowed.contains name do throwError m!"UNAUTHORIZED_AXIOM {name}"
  let forbidden := #[
    `SaturationMonoid.StandardModelConstraint.alphaEMIntegerDenominator,
    `SaturationMonoid.StandardModelConstraint.alphaEMFromIntegerConstraint,
    `SaturationMonoid.StandardModelConstraint.gutWeakMixingInformationRatio,
    `SaturationMonoid.StandardModelConstraint.alphaStrongDisplayed]
  for name in forbidden do
    if closure.contains name then throwError m!"TARGET_CONTAMINATION {name}"
  return (closure.size, opaqueCount, axiomCount)





set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalModeContactAudit
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
attribute [local irreducible] actualC actualA physicalTime sourcePoleRead sourceProjection
  rawReader jointResolvent jointGenerator

open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory Set


open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential

open PreparationVacuumOriginalGreenFeedback

open PreparationVacuumPhysicalAbelZeroRead Filter
open scoped Topology

open PreparationVacuumPhysicalConstraint114 PreparationVacuumSourceFieldFamily
open PreparationVacuumLowerClassical PreparationVacuumOriginalDensity
open SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumFockGauge PreparationVacuumActualFieldQuantization
open GaussHistoryHilbert
open GaussNativeMatter
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _

open PreparationVacuumPhysicalColorCharge PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard CanonicalGradedCharge GaussFockLabel GaussFockPair
open SourceQuantumFockGauge GaussCoreLabel NativeHistoryGrade QuantizationCheck.Fermion

open PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherChart PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge
open PreparationVacuumFieldConstraintResponse PreparationVacuumNoetherOrdinaryWard
local instance : NormedAlgebra ℝ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] noetherReader noetherForm sourceApprox sourceTestApprox

open PreparationVacuumPhysicalColorWard
local instance : NormedAlgebra ℚ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] sourcePolePrepared sourceExcitedProjection

open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation


open LowEnergy.PreparationVacuumPhysicalModeContact
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology Interval ContDiff
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory Set
open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential
open PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalAbelZeroRead Filter
open scoped Topology
open PreparationVacuumPhysicalConstraint114 PreparationVacuumSourceFieldFamily
open PreparationVacuumLowerClassical PreparationVacuumOriginalDensity
open SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumFockGauge PreparationVacuumActualFieldQuantization
open GaussHistoryHilbert
open GaussNativeMatter
open PreparationVacuumPhysicalColorCharge PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard CanonicalGradedCharge GaussFockLabel GaussFockPair
open SourceQuantumFockGauge GaussCoreLabel NativeHistoryGrade QuantizationCheck.Fermion
open PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherChart PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge
open PreparationVacuumFieldConstraintResponse PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumPhysicalColorWard
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory Set
open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential
open PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalAbelZeroRead Filter
open scoped Topology
open PreparationVacuumPhysicalConstraint114 PreparationVacuumSourceFieldFamily
open PreparationVacuumLowerClassical PreparationVacuumOriginalDensity
open SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumFockGauge PreparationVacuumActualFieldQuantization
open GaussHistoryHilbert
open GaussNativeMatter
open PreparationVacuumPhysicalColorCharge PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard CanonicalGradedCharge GaussFockLabel GaussFockPair
open SourceQuantumFockGauge GaussCoreLabel NativeHistoryGrade QuantizationCheck.Fermion
open PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherChart PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge
open PreparationVacuumFieldConstraintResponse PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumPhysicalColorWard
open PreparationVacuumNonlinearFieldCurve
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory Set
open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential
open PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalAbelZeroRead Filter
open scoped Topology
open PreparationVacuumPhysicalConstraint114 PreparationVacuumSourceFieldFamily
open PreparationVacuumLowerClassical PreparationVacuumOriginalDensity
open SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumFockGauge PreparationVacuumActualFieldQuantization
open GaussHistoryHilbert
open GaussNativeMatter
open PreparationVacuumPhysicalColorCharge PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard CanonicalGradedCharge GaussFockLabel GaussFockPair
open SourceQuantumFockGauge GaussCoreLabel NativeHistoryGrade QuantizationCheck.Fermion
open PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherChart PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge
open PreparationVacuumFieldConstraintResponse PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumPhysicalColorWard
open PreparationVacuumNonlinearFieldCurve
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation

theorem checked_sourceReferenceContact_generated :
    stateContact (Fin.castAdd 6 (2:Fin 3)) 1 LowEnergy.PreparationVacuumPhysicalModeContact.sourceReferenceState=
      -(gaugeScale/2 : ℝ) • fieldDirection LowEnergy.PreparationVacuumPhysicalModeContact.sourceModeField  := LowEnergy.PreparationVacuumPhysicalModeContact.sourceReferenceContact_generated

theorem checked_sourceEmittedContact_generated (z : SourceCoordinateSlice) :
    stateContact (Fin.castAdd 6 (2:Fin 3)) 1 (sourceState z)=
      -(gaugeScale/2 : ℝ) • fieldDirection LowEnergy.PreparationVacuumPhysicalModeContact.sourceModeField+LowEnergy.PreparationVacuumPhysicalModeContact.sourceModeDeviation z  := LowEnergy.PreparationVacuumPhysicalModeContact.sourceEmittedContact_generated z

theorem checked_sourceNativeContactSymbol_generated (p : PhysicalMomentum) (z : physicalChart) :
    LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeContactSymbol p z.val=
      -(gaugeScale/2 : ℝ) • sourceModeSymbol (sourceState z.val)+LowEnergy.PreparationVacuumPhysicalModeContact.sourceModeDeviationSymbol p z.val  := LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeContactSymbol_generated p z

theorem checked_sourceNativeSample_mode (p : PhysicalMomentum) (a b : QuantumTest) (z : SourceCoordinateSlice) :
    PreparationVacuumNativeLocalWard.nativeSample (Fin.castAdd 6 (2:Fin 3)) 1 0 p a b (0,z)=
      -(gaugeScale/2 : ℝ) • (rawSample (gaugeField 1 0) p a b (0,z)-rawSample (gaugeField 2 1) p a b (0,z))+
        LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationSample p a b z  := LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeSample_mode p a b z

theorem checked_sourceNativeForm_mode (p : PhysicalMomentum) (a b : QuantumTest) :
    PreparationVacuumNativeLocalWard.nativeForm (Fin.castAdd 6 (2:Fin 3)) 1 0 p a b 0=
      -(gaugeScale/2 : ℝ) • (rawForm (gaugeField 1 0) p a b 0-rawForm (gaugeField 2 1) p a b 0)+LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationForm p a b  := LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeForm_mode p a b

theorem checked_sourceNativeReader_mode (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    PreparationVacuumNativeLocalWard.nativeReader (Fin.castAdd 6 (2:Fin 3)) 1 0 p F 0=
      (-(gaugeScale/2 : ℝ) : ℂ) • (PreparationVacuumRawJointFeedback.rawReader (gaugeField 1 0) p F 0-
        PreparationVacuumRawJointFeedback.rawReader (gaugeField 2 1) p F 0)+LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationReader p F  := LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeReader_mode p F

theorem checked_sourceContactKernel_mode (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) :
    LowEnergy.PreparationVacuumPhysicalModeContact.sourceContactKernel q pL pR t=
      (-(gaugeScale/2 : ℝ) : ℂ) • (sourceGaugeZeroHistoryKernel q pL pR 1 0 t-
        sourceGaugeZeroHistoryKernel q pL pR 2 1 t)+LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationKernel q pL pR t  := LowEnergy.PreparationVacuumPhysicalModeContact.sourceContactKernel_mode q pL pR t

theorem checked_sourceActualMode_contact_deviation (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    (gaugeScale/2 : ℝ) • (sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 1 0)-
      sourcePoleActionEuler q pL pR left right 0 t (gaugeSlot 2 1))=
      sourcePoleRead q.epsilon q.precision pL pR left right (LowEnergy.PreparationVacuumPhysicalModeContact.sourceContactKernel q pL pR t)-
        sourcePoleRead q.epsilon q.precision pL pR left right (LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationKernel q pL pR t)  := LowEnergy.PreparationVacuumPhysicalModeContact.sourceActualMode_contact_deviation q pL pR left right t nonrealL nonrealR

end LowEnergy.PreparationPhysicalModeContactAudit
elab (name := H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalModeContact.auditCommand) "#audit_moving_pole_gauss_return" : command => do
  let env ← getEnv
  let cache ← liftIO (IO.mkRef ({} : NameMap (Array Name)))
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceReferenceContact,
    `H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeNativeSymbol,
    `H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeContactRead]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[``LowEnergy.PreparationVacuumPhysicalModeContact.sourceReferenceState,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceModeField,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceReferenceContact_generated,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceModeDeviation,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceEmittedContact_generated,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeContactSymbol,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceModeDeviationSymbol,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeContactSymbol_generated,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationSample,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationForm,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeSample_mode,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeForm_mode,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationReader,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeReader_mode,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceContactKernel,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationKernel,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceContactKernel_mode,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceActualMode_contact_deviation]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[``LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceReferenceContact_generated,
    ``LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceEmittedContact_generated,
    ``LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceNativeContactSymbol_generated,
    ``LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceNativeSample_mode,
    ``LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceNativeForm_mode,
    ``LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceNativeReader_mode,
    ``LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceContactKernel_mode,
    ``LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceActualMode_contact_deviation]
  let roots := owned ++ tests.toList
  let closure ← liftIO (completeClosure env cache roots)
  let anchors := #[``LowEnergy.PreparationVacuumPhysicalModeContact.sourceReferenceState,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceModeField,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceModeDeviation,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeContactSymbol,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceModeDeviationSymbol,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationSample,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationForm,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationReader,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceContactKernel,
    ``LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationKernel]
  for name in anchors do
    unless closure.contains name do throwError m!"MISSING_SOURCE {name}"
  let consumers := #[(``LowEnergy.PreparationVacuumPhysicalModeContact.sourceEmittedContact_generated,``LowEnergy.PreparationVacuumPhysicalModeContact.sourceReferenceContact_generated),
    (``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeContactSymbol_generated,``LowEnergy.PreparationVacuumPhysicalModeContact.sourceEmittedContact_generated),
    (``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeSample_mode,``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeContactSymbol_generated),
    (``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeForm_mode,``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeSample_mode),
    (``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeReader_mode,``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeForm_mode),
    (``LowEnergy.PreparationVacuumPhysicalModeContact.sourceContactKernel_mode,``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeReader_mode),
    (``LowEnergy.PreparationVacuumPhysicalModeContact.sourceActualMode_contact_deviation,``LowEnergy.PreparationVacuumPhysicalModeContact.sourceContactKernel_mode),
    (``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeContactSymbol_generated,``LowEnergy.PreparationVacuumRestModeCoupling.sourceModeSymbol_generated),
    (``LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeSample_mode,``LowEnergy.PreparationVacuumRestModeCoupling.sourceModeSymbol_generated),
    (``LowEnergy.PreparationVacuumPhysicalModeContact.sourceActualMode_contact_deviation,``LowEnergy.PreparationVacuumPhysicalGradeZeroRead.sourceGaugeCurrent_zeroHistory)]
  for (mouth, producer) in consumers do
    let reached ← liftIO (completeClosure env cache [mouth])
    unless reached.contains producer do throwError m!"UNCONSUMED_SOURCE {mouth}: {producer}"
  let (nodes, opaques, axioms) ← checkClosure env cache roots
  if let some path ← liftIO (IO.getEnv "ALPHA_PHYSICAL_MODE_CONTACT_OUTPUT") then
    let project := closure.toArray.filter fun name =>
      match owner name with
      | none => false
      | some moduleName => !(#["Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop", "Qq", "Plausible", "ImportGraph", "ProofWidgets"].any
          (fun head => head.isPrefixOf moduleName.toString))
    liftIO <| IO.FS.writeFile path <| (Json.mkObj [
      ("owned",toJson (owned.map Name.toString)), ("public_roots",toJson mouths.size),
      ("nodes",toJson nodes), ("opaque_all_read",toJson opaques), ("axioms",toJson axioms),
      ("anchors",toJson (anchors.map Name.toString)),
      ("consumers",toJson (consumers.map fun p => (p.1.toString,p.2.toString))),
      ("actual_tests",toJson (tests.map Name.toString)),
      ("project",toJson (project.map fun n => (n.toString,(owner n).map Name.toString)))]).compress
  logInfo m!"PHYSICAL_MODE_CONTACT_PASS public={mouths.size} all_owned={owned.length} tests={tests.size} nodes={nodes} opaque_all_read={opaques} axioms={axioms}"

#audit_moving_pole_gauss_return
