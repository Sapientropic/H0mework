import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussConnection
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussKineticTorque
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard
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
namespace LowEnergy.PreparationPhysicalGaussColorTorqueAudit
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
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

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

open PreparationVacuumNonlinearFieldCurve
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation


open PreparationVacuumPhysicalModeContact GaussLiveMomentum CanonicalPhysicalWardCore



open LowEnergy.PreparationVacuumPhysicalGaussColorTorque
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
open PreparationVacuumNonlinearFieldCurve
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation
open PreparationVacuumPhysicalModeContact GaussLiveMomentum CanonicalPhysicalWardCore
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
open PreparationVacuumPhysicalModeContact GaussLiveMomentum CanonicalPhysicalWardCore
open scoped ContDiff
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
open PreparationVacuumPhysicalModeContact GaussLiveMomentum CanonicalPhysicalWardCore
open scoped ContDiff

theorem checked_sourceColor_directional (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    directional v (chargeAction (colorGenerator 2) f) z=
      LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorChargeFiber (directional v f z)  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_directional v f z

theorem checked_sourceColor_covariant_connection (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    covariantMomentum v (chargeAction (colorGenerator 2) f) z-
      chargeAction (colorGenerator 2) (covariantMomentum v f) z=
        (-Complex.I) • LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorConnectionFiber v z (f z)  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_covariant_connection v f z

theorem checked_sourceColorCharge_hermitian : (chargeMatrix (colorGenerator 2)).conjTranspose=chargeMatrix (colorGenerator 2)  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCharge_hermitian

theorem checked_sourceColorCharge_pair (f g : QuantumTest) :
    sourcePair f (chargeAction (colorGenerator 2) g)=sourcePair (chargeAction (colorGenerator 2) f) g  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCharge_pair f g

theorem checked_sourceColorCovariantTorque_generated (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCovariantTorque v f z=(-Complex.I) • LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorConnectionFiber v z (f z)  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCovariantTorque_generated v f z

theorem checked_sourceNativeSandwichWard (v w : Ambient) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f g : QuantumTest) :
    sourcePair f (GaussNativeForm.sandwich v w c smooth (chargeAction (colorGenerator 2) g)-
      chargeAction (colorGenerator 2) (GaussNativeForm.sandwich v w c smooth g))=
      LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeSandwichTorque v w c smooth f g  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeSandwichWard v w c smooth f g

theorem checked_sourceNativeOperator_generated :
    LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorWardOperator GaussNativeForm.nativeAction=
      (1/2 : ℂ) • (∑ a : GaussNativeForm.ScalarIndex,
        LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorWardOperator (GaussNativeForm.sandwich (GaussNativeForm.scalarDirection a) (GaussNativeForm.scalarDirection a)
          GaussNativeEnergy.scalarWeight GaussNativeEnergy.scalarWeight_smooth))+
      (1/2 : ℂ) • (∑ a : GaussNativeForm.LieIndex,∑ i : Fin 3,∑ j : Fin 3,
        LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorWardOperator (GaussNativeForm.sandwich (GaussNativeForm.gaugeDirection i a) (GaussNativeForm.gaugeDirection j a)
          (fun z=>GaussNativeEnergy.gaugeWeight z i j) (GaussNativeEnergy.gaugeWeight_smooth i j)))  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeOperator_generated

theorem checked_sourceNativeActionWard (f g : QuantumTest) :
    sourcePair f (GaussNativeForm.nativeAction (chargeAction (colorGenerator 2) g)-
      chargeAction (colorGenerator 2) (GaussNativeForm.nativeAction g))=LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeTorque f g  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeActionWard f g

theorem checked_sourceColor_coframeDerivative (v : SourceCoordinateSlice) (f : QuantumTest) :
    GaussCoframeCore.derivative v (chargeAction (colorGenerator 2) f)=
      chargeAction (colorGenerator 2) (GaussCoframeCore.derivative v f)  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeDerivative v f

theorem checked_sourceColor_coframeMomentum (i : Fin 6) :
    Commute (chargeAction (colorGenerator 2)) (GaussCoframeCore.momentum i)  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeMomentum i

theorem checked_sourceColor_coframeAdjoint (i : Fin 6) :
    Commute (chargeAction (colorGenerator 2)) (GaussCoframeCore.adjoint i)  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeAdjoint i

theorem checked_sourceColor_spin_full (a : Fin 7) :
    GaussCoframeSpin.full a*nativeFull (colorGenerator 2)=nativeFull (colorGenerator 2)*GaussCoframeSpin.full a  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_spin_full a

theorem checked_sourceColor_spinCurrent (a : Fin 7) :
    Commute (chargeAction (colorGenerator 2)) (GaussCoframeSpin.current a)  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_spinCurrent a

theorem checked_sourceColor_scalar (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (chargeAction (colorGenerator 2)) (GaussNativeForm.multiply c smooth)  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_scalar c smooth

theorem checked_sourceColor_coframeTerm (i j : Fin 6) :
    Commute (chargeAction (colorGenerator 2)) (GaussCoframeKinetic.term i j)  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeTerm i j

theorem checked_sourceColor_coframeMixed (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice→ℝ)
    (smooth : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (chargeAction (colorGenerator 2)) (GaussCoframeForm.mixed i a c smooth)  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeMixed i a c smooth

theorem checked_sourceColor_number : Commute (chargeAction (colorGenerator 2)) GaussCoframeForm.number  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_number

theorem checked_sourceColor_coframeAction : Commute (chargeAction (colorGenerator 2)) GaussCoframeForm.coframeAction  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeAction

theorem checked_sourceMatterTorque_generated (f : QuantumTest) (z : SourceCoordinateSlice) :
    LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorWardOperator GaussMatterCore.matterAction f z=LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceMatterTorqueFiber z (f z)  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceMatterTorque_generated f z

theorem checked_sourceConfigurationTorque_generated :
    configurationTorque (colorGenerator 2)=LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorWardOperator GaussNativeForm.nativeAction+
      LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorWardOperator GaussMatterCore.matterAction  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceConfigurationTorque_generated

theorem checked_sourceConfigurationTorque_ward (f g : QuantumTest) :
    sourcePair f (configurationTorque (colorGenerator 2) g)=LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeTorque f g+
      sourcePair f (LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorWardOperator GaussMatterCore.matterAction g)  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceConfigurationTorque_ward f g

theorem checked_sourceActualN1_gaussColorCore (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (k : PhysicalMomentum) (left : QuantumTest) :
    sourcePair left (sourceN1WardCore k (colorGenerator 2)
      (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))=
      LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeTorque left (sourceTestApprox q.F (sourceActualN1Primal q p state z t))+
      sourcePair left (LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorWardOperator GaussMatterCore.matterAction
        (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))+
      sourcePair left (CanonicalPhysicalWardCore.currentAction k (colorGenerator 2)
        (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))+
      sourcePair left (yukawaTorque (colorGenerator 2)
        (sourceTestApprox q.F (sourceActualN1Primal q p state z t)))  := LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceActualN1_gaussColorCore q p state z t k left

end LowEnergy.PreparationPhysicalGaussColorTorqueAudit
elab (name := H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque.auditCommand) "#audit_moving_pole_gauss_return" : command => do
  let env ← getEnv
  let cache ← liftIO (IO.mkRef ({} : NameMap (Array Name)))
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussConnection,
    `H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussKineticTorque,
    `H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorChargeFiber,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorConnectionFiber,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_directional,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_covariant_connection,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCharge_hermitian,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCharge_pair,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.QuantumEnd,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCovariantTorque,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCovariantTorque_generated,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeSandwichTorque,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeSandwichWard,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorWardOperator,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeOperator_generated,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeTorque,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeActionWard,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeDerivative,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeMomentum,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeAdjoint,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_spin_full,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_spinCurrent,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_scalar,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeTerm,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeMixed,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_number,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeAction,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceMatterTorqueFiber,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceMatterTorque_generated,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceConfigurationTorque_generated,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceConfigurationTorque_ward,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceActualN1_gaussColorCore]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_directional,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_covariant_connection,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColorCharge_hermitian,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColorCharge_pair,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColorCovariantTorque_generated,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceNativeSandwichWard,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceNativeOperator_generated,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceNativeActionWard,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_coframeDerivative,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_coframeMomentum,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_coframeAdjoint,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_spin_full,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_spinCurrent,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_scalar,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_coframeTerm,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_coframeMixed,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_number,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_coframeAction,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceMatterTorque_generated,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceConfigurationTorque_generated,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceConfigurationTorque_ward,
    ``LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceActualN1_gaussColorCore]
  let roots := owned ++ tests.toList
  let closure ← liftIO (completeClosure env cache roots)
  let anchors := #[``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorChargeFiber,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorConnectionFiber,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCovariantTorque,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeSandwichTorque,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorWardOperator,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeTorque,
    ``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceMatterTorqueFiber]
  for name in anchors do
    unless closure.contains name do throwError m!"MISSING_SOURCE {name}"
  let consumers := #[(``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_covariant_connection,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_directional),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCharge_pair,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCharge_hermitian),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCovariantTorque_generated,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_covariant_connection),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeSandwichWard,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCharge_pair),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeActionWard,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeSandwichWard),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeActionWard,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeOperator_generated),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeMomentum,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeDerivative),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeAdjoint,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeMomentum),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeAdjoint,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCharge_pair),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_spinCurrent,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_spin_full),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeTerm,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeMomentum),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeTerm,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeAdjoint),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeMixed,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeMomentum),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeMixed,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_spinCurrent),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeAction,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeTerm),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeAction,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeMixed),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeAction,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_spin_full),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeAction,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_number),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceConfigurationTorque_generated,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeAction),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceConfigurationTorque_ward,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceConfigurationTorque_generated),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceConfigurationTorque_ward,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeActionWard),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceMatterTorque_generated,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceMatterTorqueFiber),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceActualN1_gaussColorCore,``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceConfigurationTorque_ward),
    (``LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceActualN1_gaussColorCore,``LowEnergy.PreparationVacuumPhysicalN1WardCollapse.sourceActualN1Primal)]
  for (mouth, producer) in consumers do
    let reached ← liftIO (completeClosure env cache [mouth])
    unless reached.contains producer do throwError m!"UNCONSUMED_SOURCE {mouth}: {producer}"
  let (nodes, opaques, axioms) ← checkClosure env cache roots
  if let some path ← liftIO (IO.getEnv "ALPHA_PHYSICAL_GAUSS_COLOR_TORQUE_OUTPUT") then
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
  logInfo m!"PHYSICAL_GAUSS_COLOR_TORQUE_PASS public={mouths.size} all_owned={owned.length} tests={tests.size} nodes={nodes} opaque_all_read={opaques} axioms={axioms}"

#audit_moving_pole_gauss_return
