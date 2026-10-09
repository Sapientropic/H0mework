import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseConfigurationContact

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPhasePropagation
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField FullQuantum.StateGreen
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumOriginalDensity PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets PreparationVacuumPhysicalFeedback
open PreparationVacuumNoetherChart
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _

open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction PreparationVacuumHalfDensityFiber
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
open ActualEMOriginWard Stage9C.Material.SpinPair PreparationVacuumPhysicalModeContact


open GaussLiveMomentum GaussNativeMatter SourceQuantumScalarChart SourceQuantumResidualGaugeSlice
open StageNineP286GaugeConnectionVariationDensity
open PreparationPhysicalPhaseGaugeRealization PreparationVacuumNativeFieldInjection
open PreparationVacuumActionDecomposition StageNineHolonomicField
open ActualEMCompleteOrbit

open PreparationVacuumFieldConstraintResponse SourceGraph
open ActualDressedPhaseWard ActualDressedNoether ActualDressedFullCoulomb ActualDressedSourcePreparation
open PreparationVacuumElectricConstraint PreparationVacuumFullElectricWard CanonicalPhysicalWardCore
open CanonicalGradedCharge GaussFockPair PreparationVacuumSourcePreparedResponse
attribute [local irreducible] sourceState sourceSymbol sourceActionWeight phaseHeldAction phaseHeldMixed
  sourceReferenceState sourceDressedUnit sourceProfile jointResolvent chargeReader dressedEulerObserver prepared


open ActualDressedPhaseConfiguration ActualDressedNonlinearHalf


open SourcePropagationNearFieldTime SourcePropagationNoetherTime SourcePropagationTimeDependentFeedback
open ActualDressedLockedWard ActualDressedConstraintRead
attribute [local irreducible] physicalTime phaseReader phaseReaderContact nativeWardHistory
  configurationWardReader configurationWardContact physicalBackgroundMap


/-- This transports the generated profile reader and its own full contact through both ordered original time legs. -/
def configurationPhaseHistory (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (age : ℝ) : H→L[ℂ]H :=
  nativeWardHistory (dressedKinematicPoint event transfer)
    (configurationWardReader event.momentum event.frame)
    (fun force=>configurationWardContact force event.momentum event.frame)
    (fun s=>(signal s).value) age

theorem configuration_history_original (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (age : ℝ) :
    configurationPhaseHistory event transfer signal age=phaseHistory .deviation event transfer signal age := by
  unfold configurationPhaseHistory phaseHistory
  simp only [configuration_reader_original,configuration_contact_original]

/-- The true all289 Noether current consumes the configuration/profile Ward with its original contact and preparation terms. -/
theorem configuration_actual_current (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (age : ℝ) :
    ((gaugeScale/2:ℝ):ℂ)*(∑j : Fin 289,(sourceModeField j:ℂ)*(dressedNoetherJet event transfer signal age j).value)=
      dressedEulerObserver event (phaseHistory .ward event transfer signal age)-
      dressedEulerObserver event (phaseHistory .scalar event transfer signal age)-
      dressedEulerObserver event (configurationPhaseHistory event transfer signal age) := by
  rw [configuration_history_original]
  exact phase_actual_current event transfer signal age

/-- Fixed age uses its actual time-shifted dense legs, rather than commuting a charge through the evolution. -/
def configurationTimeRead (event : DressedEvent) (transfer : PhysicalMomentum) (age : ℝ)
    (readFrame : GaussUnitaryHistory.Index) : ℂ :=
  -phaseConfigurationRead readFrame
    ((physicalTime (event.momentum-transfer) event.frame (-age) 0*
      jointResolvent (event.momentum-transfer) event.frame event.energy 0).adjoint
      (sourceDressedUnit event.epsilon event.precision))
    ((jointResolvent event.momentum event.frame event.energy 0*physicalTime event.momentum event.frame age 0)
      (sourceDressedUnit event.epsilon event.precision))+
  phaseConfigurationRead readFrame
    ((physicalTime (event.momentum-transfer) event.frame (-age) 0*
      jointResolvent (event.momentum-transfer) event.frame event.energy 0).adjoint
      (prepared (sourceProfile event.epsilon event.precision)))
    ((jointResolvent event.momentum event.frame event.energy 0*physicalTime event.momentum event.frame age 0)
      (prepared (sourceProfile event.epsilon event.precision)))

private theorem observed_complete_limit (event : DressedEvent) (L R : H→L[ℂ]H) :
    Tendsto (fun F : GaussUnitaryHistory.Index=>
      -phaseConfigurationRead F (L.adjoint (sourceDressedUnit event.epsilon event.precision))
        (R (sourceDressedUnit event.epsilon event.precision))+
      phaseConfigurationRead F (L.adjoint (prepared (sourceProfile event.epsilon event.precision)))
        (R (prepared (sourceProfile event.epsilon event.precision)))) GaussUnitaryHistory.sourceFilter
      (𝓝 (dressedEulerObserver event (L*(-chargeReader sourcePhaseGaugeLie)*R))) := by
  have unit:=phase_configuration_source_limit (L.adjoint (sourceDressedUnit event.epsilon event.precision))
    (R (sourceDressedUnit event.epsilon event.precision))
  have background:=phase_configuration_source_limit (L.adjoint (prepared (sourceProfile event.epsilon event.precision)))
    (R (prepared (sourceProfile event.epsilon event.precision)))
  have combine:=unit.neg.add background
  have pair (x : H) : inner ℂ (L.adjoint x) ((-chargeReader sourcePhaseGaugeLie) (R x))=
      inner ℂ x ((L*(-chargeReader sourcePhaseGaugeLie)*R) x) := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    rfl
  have endpoint:=(congrArg₂ (fun a b : ℂ=> -a+b)
    (pair (sourceDressedUnit event.epsilon event.precision))
    (pair (prepared (sourceProfile event.epsilon event.precision)))).trans
      (dressed_euler_observer_original event (L*(-chargeReader sourcePhaseGaugeLie)*R)).symm
  exact Eq.mp (congrArg (fun value : ℂ=>Tendsto (fun F : GaussUnitaryHistory.Index=>
      -phaseConfigurationRead F (L.adjoint (sourceDressedUnit event.epsilon event.precision))
        (R (sourceDressedUnit event.epsilon event.precision))+
      phaseConfigurationRead F (L.adjoint (prepared (sourceProfile event.epsilon event.precision)))
        (R (prepared (sourceProfile event.epsilon event.precision)))) GaussUnitaryHistory.sourceFilter
      (𝓝 value)) endpoint) combine

/-- The complete configuration generator reaches the actual physical-background map at each age, on its two genuine endpoints. -/
theorem configuration_time_source_limit (event : DressedEvent) (transfer : PhysicalMomentum) (age : ℝ) :
    Tendsto (configurationTimeRead event transfer age) GaussUnitaryHistory.sourceFilter
      (𝓝 (dressedEulerObserver event (physicalBackgroundMap (dressedKinematicPoint event transfer) 0 age
        (jointResolvent (event.momentum-transfer) event.frame event.energy 0*
          (-chargeReader sourcePhaseGaugeLie)*jointResolvent event.momentum event.frame event.energy 0)))) := by
  have generated:=observed_complete_limit event
    (physicalTime (event.momentum-transfer) event.frame (-age) 0*
      jointResolvent (event.momentum-transfer) event.frame event.energy 0)
    (jointResolvent event.momentum event.frame event.energy 0*physicalTime event.momentum event.frame age 0)
  unfold configurationTimeRead
  simpa only [physicalBackgroundMap_apply,dressedKinematicPoint,
    sub_eq_add_neg,mul_assoc] using generated

end LowEnergy.GaussComposite.ActualDressedPhasePropagation
