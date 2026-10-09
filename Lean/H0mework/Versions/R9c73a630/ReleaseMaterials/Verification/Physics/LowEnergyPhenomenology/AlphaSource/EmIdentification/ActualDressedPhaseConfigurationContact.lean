import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseConfigurationRead
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNonlinearPolarization

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

/-- The original weighted configuration/profile Ward, including its three generated source terms. -/
def configurationWardEntry (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  Complex.I*(sourcePair (phaseDevAdjoint a) (phaseSourceActionMultiplier p b)-
    sourcePair a (phaseSourceActionMultiplier p (phaseDevAction b)))-
    ∫z,phaseConfigurationCompensationSample p a b z ∂GaussHistoryHilbert.configurationMeasure

def configurationWardReader (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  finiteRiesz F (fun i j=>configurationWardEntry p (frameTest F i) (frameTest F j))

theorem configuration_reader_original (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    configurationWardReader p F=phaseReader .deviation p F 0 :=
  (phase_deviation_configuration_reader p F).symm

/-- Source-coordinate second variation, its actual vertical state and both chart/contact complements. -/
def configurationMixedState (force : Field289) (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FullMatrix :=
  -(4:ℂ) • (sourceActionWeight (sourceState z)*
    (symbolSecond p (sourceState z) (sliceState (phaseConfigurationDirection z)) (fieldDirection force)+
    symbolSecond p (sourceState z)
      (phaseAmbientState (orbitMap z (phaseConfigurationConnection z))) (fieldDirection force)+
    (symbolFirst p (sourceState z)
      (phaseAmbientState (variationL (PreparationVacuumFieldConstraintResponse.fieldVector force z) (sourcePhaseGaugeLie,0)))+
    symbolFirst p (sourceState z) (emGaugeState (complement force z)))))

def configurationContactForm (force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  ∫z,pairSample z (a z) (quantizer (configurationMixedState force p z) (b z))
    ∂GaussHistoryHilbert.configurationMeasure

def configurationWardContact (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  finiteRiesz F (fun i j=>configurationContactForm force p (frameTest F i) (frameTest F j))

theorem configuration_mixed_original (force : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    configurationMixedState force p z.val=phaseHeldMixed .deviation force p (sourceState z.val) (sourceState z.val) :=
  (phase_deviation_mixed_configuration force p z).symm

theorem configuration_contact_form_original (force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    configurationContactForm force p a b=phaseContactForm .deviation force p a b := by
  unfold configurationContactForm phaseContactForm
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  change pairSample z (a z) (quantizer (configurationMixedState force p z) (b z))=
    pairSample z (a z) (quantizer (phaseHeldMixed .deviation force p (sourceState z) (sourceState z)) (b z))
  by_cases inside : z∈tsupport a
  · rw [configuration_mixed_original force p ⟨z,a.tsupport_subset inside⟩]
  · simp only [image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

theorem configuration_contact_original (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    configurationWardContact force p F=phaseReaderContact .deviation force p F := by
  rw [phase_reader_contact_source]
  unfold configurationWardContact
  exact congrArg (finiteRiesz F) (funext (fun i=>funext (fun j=>
    configuration_contact_form_original force p (frameTest F i) (frameTest F j))))

/-- This is the actual nonlinear reader's contact; the weighted source reader is not declared a fixed field. -/
theorem configuration_reader_source_derivative (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    HasDerivAt (fun r : ℝ=>phaseReader .deviation p F (r • force)) (configurationWardContact force p F) 0 := by
  rw [configuration_contact_original]
  exact phase_reader_generated .deviation force p F

end LowEnergy.GaussComposite.ActualDressedPhasePropagation
