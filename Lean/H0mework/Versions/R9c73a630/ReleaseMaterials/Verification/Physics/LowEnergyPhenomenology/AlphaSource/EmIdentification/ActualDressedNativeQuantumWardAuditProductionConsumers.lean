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

