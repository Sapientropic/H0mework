import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorReader
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorWard
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorColumn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorConstraint

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit
elab "checked_native_color_generatorContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_generator).type
theorem checked_native_color_generator : checked_native_color_generatorContract := @LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_generator

elab "checked_native_color_gradient_stateContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_state).type
theorem checked_native_color_gradient_state : checked_native_color_gradient_stateContract := @LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_state

elab "checked_native_color_gradient_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_action).type
theorem checked_native_color_gradient_action : checked_native_color_gradient_actionContract := @LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_action

elab "checked_native_color_gradient_transportContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_transport).type
theorem checked_native_color_gradient_transport : checked_native_color_gradient_transportContract := @LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_transport

elab "checked_native_color_gradient_reader_germContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_reader_germ).type
theorem checked_native_color_gradient_reader_germ : checked_native_color_gradient_reader_germContract := @LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_reader_germ

elab "checked_native_color_gradient_readerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_reader).type
theorem checked_native_color_gradient_reader : checked_native_color_gradient_readerContract := @LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_reader

elab "checked_native_color_gradient_contactContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_contact).type
theorem checked_native_color_gradient_contact : checked_native_color_gradient_contactContract := @LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_contact

elab "checked_native_color_gradient_historyContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_history).type
theorem checked_native_color_gradient_history : checked_native_color_gradient_historyContract := @LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_history

elab "checked_native_color_gradient_actualContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_actual).type
theorem checked_native_color_gradient_actual : checked_native_color_gradient_actualContract := @LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_actual

elab "checked_native_color_temporal_gaussContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_temporal_gauss).type
theorem checked_native_color_temporal_gauss : checked_native_color_temporal_gaussContract := @LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_temporal_gauss

elab "checked_native_color_prepared_insertionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_prepared_insertion).type
theorem checked_native_color_prepared_insertion : checked_native_color_prepared_insertionContract := @LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_prepared_insertion

elab "checked_original_color_column_gradientContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.original_color_column_gradient).type
theorem checked_original_color_column_gradient : checked_original_color_column_gradientContract := @LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.original_color_column_gradient

elab "checked_native_color_constraint_currentContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_constraint_current).type
theorem checked_native_color_constraint_current : checked_native_color_constraint_currentContract := @LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_constraint_current

elab "checked_source_color_constraint_currentContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.source_color_constraint_current).type
theorem checked_source_color_constraint_current : checked_source_color_constraint_currentContract := @LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.source_color_constraint_current

elab "checked_source_color_constraint_nonlinearContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.source_color_constraint_nonlinear).type
theorem checked_source_color_constraint_nonlinear : checked_source_color_constraint_nonlinearContract := @LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.source_color_constraint_nonlinear

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open FullQuantum.StateGreen PreparationVacuumFixedMomentumActionReturn PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization SourceQuantumFockGauge PreparationVacuumNonlinearFieldCurve
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumActionFieldLift PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction
open PreparationVacuumLowerClassical PreparationVacuumTemporalCharge PreparationVacuumGaugeSourceInjection
open PreparationVacuumNoetherChart PreparationVacuumSourceActionJets PreparationVacuumFullFieldRiesz
open SourcePropagationNativeActionHessian GaussNativeMatter GaussCoreHilbert
open ActualDressedNativeConstraint ActualDressedNullNative ActualDressedLockedWard ActualDressedConstraintRead
open ActualDressedTemporalCurrent PreparationVacuumWeightedChargeActionWard
open Filter
open scoped Matrix BigOperators Topology Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
attribute [local irreducible] nativeSourceColumn noetherReader nativeReader nativeReaderContact

open GaussHistoryHilbert GaussCoreDifferential GaussQuantumMultiplier
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumNonlinearFieldCurve PreparationVacuumHalfDensityFiber
open MeasureTheory Set
open scoped InnerProductSpace
abbrev TestOp:=H→L[ℂ]H
local instance : NormedAlgebra ℝ TestOp:=NormedAlgebra.restrictScalars ℝ ℂ _

open SourcePropagationTimeDependentFeedback SourcePropagationNoetherTime PreparationVacuumPropagationPencil
open PreparationVacuumFieldConstraintResponse GaussFockPair PreparationVacuumElectricConstraint PreparationPhysicalActionUnits PreparationVacuumSourceChargeWard
open PreparationVacuumNoetherOrdinaryWard PreparationVacuumFullElectricWard CanonicalGradedCharge
open ActualDressedNoether ActualDressedFullCoulomb ActualDressedSourcePreparation
attribute [local irreducible] nativeWardHistory dressedEulerObserver jointResolvent physicalTime jointCurrent sourceHamiltonian

open ActualDressedNativeQuantumWard ActualDressedConstraintWard ActualDressedSignal ActualDressedPencil
open ActualEMDressedSchur SourcePropagationMotherEulerKernel SourcePropagationNativeEulerHistory
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open scoped Interval

theorem checked_source_valid_transport (g : Fin 3) (gradient : Fin 4→ℝ) (p : PhysicalMomentum) :
    nativeNoether (Fin.castAdd 6 g) 0 gradient p (sourceState sourcePoint.val) (sourceState sourcePoint.val)=
      ∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) •
        transportedRawSymbol (gaugeField b.2 b.1) (sourceState sourcePoint.val) (sourceState sourcePoint.val) p :=
  native_color_gradient_transport g gradient p _ _ (sourceState_valid sourcePoint.val sourcePoint.property)

theorem checked_actual_resolvent_time_right_leg (event : DressedEvent) (transfer : PhysicalMomentum) (g : Fin 3) (r t : ℝ) :
    let q:=dressedKinematicPoint event transfer
    let y:=jointResolvent q.p q.F q.w 0
      (physicalTime q.p q.F t 0 (sourceDressedUnit event.epsilon event.precision))
    nativeColorTemporalInsertion q g r y=
      ∑a : Fin 12,((-r*gaugeColorRaw g a : ℝ):ℂ) •
        (sourceApprox q.F (embed (weightedWardCore q.p q.k a (sourceTestApprox q.F y)))+
         leftCompressionDefect (q.p+q.k) q.F (rawChargeCore a (sourceTestApprox q.F y))+
         leftUncutDefect (q.p+q.k) q.F (rawChargeCore a (sourceTestApprox q.F y))-
         sourceApprox q.F (embed (rawChargeCore a
           (rightCompressionDefect q.p q.F y+rightUncutDefect q.p q.F y)))) :=by
  dsimp only
  exact native_color_prepared_insertion _ _ _ _

theorem checked_source_generated_nonlinear_window (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (lambda : ℂ) (v : SignalAmplitude) (g : Fin 3) :
    let T:=dressedSignalDuration event transfer p v/2
    sourceCokernel p
      (fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*deriv (fun r=>dressedSignalRawEuler event transfer p v r t i) 0)
      (Fin.castAdd 6 g)=
      -(∫t in (0:ℝ)..T,laplaceWeight lambda t*
        (dressedQuantumReader event transfer (originalNullColumn 0 (Fin.castAdd 6 g)) p v t+
          ∑a : Fin 12,∑mu : Fin 4,(p mu*(gaugeColorRaw g a:ℂ))*
            dressedQuantumReader event transfer (fun row=>(gaugeField mu a row:ℂ)) p v t)) :=by
  dsimp only
  have positive:=dressed_signal_duration_positive event transfer p v
  exact source_color_constraint_nonlinear event transfer p lambda _ (le_of_lt (half_pos positive))
    v (half_lt_self positive) g
end LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit

open Lean Elab Command
private def packageCertChildren (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def packageCertClosure (env : Environment)
    (roots : List Name) : CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (packageCertChildren info).toList ++ pending
      seen := seen.insert name
  return seen


private def packageCertRequire (env : Environment) (root : Name) (required : Array Name) : CommandElabM Unit := do
  let mut pending := [root]
  let mut seen : NameSet := {}
  let mut found : NameSet := {}
  while !pending.isEmpty && !(required.all found.contains) do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      let children := packageCertChildren info
      for target in required do
        if name == target || children.contains target then found := found.insert target
      pending := children.toList ++ pending
      seen := seen.insert name
  for name in required do
    unless found.contains name do throwError m!"UNCONSUMED_DIRECT {root} {name}"

elab "#audit_dressed_native_quantum_ward" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorSource,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorReader,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorWard,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorColumn,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorConstraint]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_generator,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_state,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_action,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_transport,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_reader_germ,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_reader,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_contact,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_history,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_actual,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_temporal_gauss,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.nativeColorTemporalInsertion,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_prepared_insertion,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.original_color_column_gradient,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_constraint_current,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.source_color_constraint_current,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.source_color_constraint_nonlinear]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_native_color_generator,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_native_color_gradient_state,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_native_color_gradient_action,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_native_color_gradient_transport,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_native_color_gradient_reader_germ,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_native_color_gradient_reader,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_native_color_gradient_contact,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_native_color_gradient_history,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_native_color_gradient_actual,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_native_color_temporal_gauss,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_native_color_prepared_insertion,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_original_color_column_gradient,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_native_color_constraint_current,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_source_color_constraint_current,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_source_color_constraint_nonlinear,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_source_valid_transport,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_actual_resolvent_time_right_leg,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWardAudit.checked_source_generated_nonlinear_window]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_state,#[
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_generator,
    ``LowEnergy.PreparationVacuumGaugeSourceInjection.gauge_direction]),
    (``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_action,#[
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_state,
    ``LowEnergy.PreparationVacuumFixedMomentumActionReturn.sourceFixedMomentumGradient]),
    (``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_transport,#[
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_action,
    ``LowEnergy.PreparationVacuumFixedMomentumActionReturn.sourceFixedMomentumGradient_raw]),
    (``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_reader_germ,#[
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_transport]),
    (``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_reader,#[
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_reader_germ]),
    (``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_contact,#[
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_reader_germ,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReader_generated]),
    (``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_history,#[
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_reader,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_contact,
    ``LowEnergy.SourcePropagationNoetherTime.noetherHistoryOperatorJet_value]),
    (``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_actual,#[
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_history,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver]),
    (``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_temporal_gauss,#[
    ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_noether_reader_return,
    ``LowEnergy.PreparationVacuumElectricConstraint.original_gauss_constraint]),
    (``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_prepared_insertion,#[
    ``LowEnergy.PreparationVacuumWeightedChargeActionWard.temporalInsertion_action_return,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.nativeColorTemporalInsertion]),
    (``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.original_color_column_gradient,#[
    ``LowEnergy.GaussComposite.ActualDressedNullNative.original_null_column_literal]),
    (``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_constraint_current,#[
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.original_color_column_gradient,
    ``LowEnergy.GaussComposite.ActualDressedNativeConstraint.native_constraint_quadratures,
    ``LowEnergy.GaussComposite.ActualDressedConstraintWard.dressed_quantum_reader_actual]),
    (``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.source_color_constraint_current,#[
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_constraint_current,
    ``LowEnergy.GaussComposite.ActualDressedNativeConstraint.source_constraint_native_history]),
    (``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.source_color_constraint_nonlinear,#[
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_constraint_current,
    ``LowEnergy.GaussComposite.ActualDressedNativeConstraint.source_constraint_native_nonlinear])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_generator,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_state,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_action,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_transport,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_reader_germ,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_reader,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_contact,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_history,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_actual,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_temporal_gauss,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_prepared_insertion,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.original_color_column_gradient,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_constraint_current,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.source_color_constraint_current,
    ``LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.source_color_constraint_nonlinear]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointResolvent,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReaderContact,
    ``LowEnergy.SourcePropagationNoetherTime.noetherHistoryOperatorJet,
    ``LowEnergy.GaussComposite.ActualDressedNullNative.originalNullColumn,
    ``LowEnergy.GaussComposite.ActualEMDressedSchur.sourceCokernel,
    ``LowEnergy.GaussComposite.ActualDressedPencil.dressedWindowPolarization,
    ``LowEnergy.PreparationPhysicalActionUnits.sourceTimeWeightCore,
    ``LowEnergy.PreparationVacuumWeightedChargeActionWard.normalChargeCore]
  for name in anchors do
    unless all.contains name do throwError m!"UNCONSUMED_SOURCE {name}"
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  let mut axioms : Nat := 0
  let mut opaques : Nat := 0
  for name in all.toArray do
    let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
    if info.isUnsafe || info.isPartial then throwError m!"UNTRUSTED {name}"
    match info with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
      unless (info.value? (allowOpaque := true)).isSome do throwError m!"UNREAD {name}"
    | _ => pure ()
    if let .opaqueInfo _ := info then opaques := opaques + 1
    if let .axiomInfo _ := info then
      axioms := axioms + 1
      unless allowed.contains name do throwError m!"UNAUTHORIZED_AXIOM {name}"
  for name in #[`SaturationMonoid.StandardModelConstraint.alphaEMIntegerDenominator,
      `SaturationMonoid.StandardModelConstraint.alphaEMFromIntegerConstraint,
      `SaturationMonoid.StandardModelConstraint.gutWeakMixingInformationRatio,
      `SaturationMonoid.StandardModelConstraint.alphaStrongDisplayed] do
    if all.contains name then throwError m!"TARGET_CONTAMINATION {name}"
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_NATIVE_QUANTUM_WARD_AUDIT_OUTPUT") then
    let project := all.toArray.filter fun name =>
      match owner name with
      | none => false
      | some m => !(#["Mathlib","Init","Lean","Std","Batteries","Aesop","Qq","Plausible","ImportGraph","ProofWidgets"].any (fun h => h.isPrefixOf m.toString))
    liftIO <| IO.FS.writeFile path <| (Json.mkObj [
      ("owned",toJson (owned.map Name.toString)),("public",toJson (mouths.map Name.toString)),
      ("tests",toJson (tests.map Name.toString)),("nodes",toJson all.size),("opaque_read",toJson opaques),
      ("axioms",toJson axioms),("anchors",toJson (anchors.map Name.toString)),
      ("direct",toJson (direct.map fun p => (p.1.toString,p.2.map Name.toString))),
      ("project",toJson (project.map fun n => (n.toString,(owner n).map Name.toString)))]).compress
  logInfo m!"DRESSED_NATIVE_QUANTUM_WARD_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_native_quantum_ward
#print axioms LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_generator
#print axioms LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_state
#print axioms LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_action
#print axioms LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_transport
#print axioms LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_reader_germ
#print axioms LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_reader
#print axioms LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_contact
#print axioms LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_history
#print axioms LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_gradient_actual
#print axioms LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_temporal_gauss
#print axioms LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_prepared_insertion
#print axioms LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.original_color_column_gradient
#print axioms LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.native_color_constraint_current
#print axioms LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.source_color_constraint_current
#print axioms LowEnergy.GaussComposite.ActualDressedNativeQuantumWard.source_color_constraint_nonlinear
