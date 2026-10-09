import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFullCoulomb
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCauchyCurrent

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNoether
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource GaussCoreHilbert GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFieldConstraintResponse
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumSourcePreparedResponse SourcePropagationNoetherTime
open ActualDressedSourcePreparation ActualDressedFullCoulomb ActualEMCauchyDynamic
open SourceGraph MeasureTheory Filter
open scoped Matrix BigOperators InnerProductSpace Topology Interval
local instance : NormedAlgebra ℝ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] sourceDressedUnit sourceProfile noetherHistoryOperatorJet
  sourceGreen originalJacobi PreparationVacuumOriginalGreenFeedback.sourceField originalReadback originalChange

/-- The old prepared pair is not used: this point supplies the same original kinematics to the operator. -/
def dressedKinematicPoint (event : DressedEvent) (transfer : PhysicalMomentum) : PhysicalResponsePoint where
  epsilon := event.epsilon
  precision := event.precision
  p := event.momentum
  k := -transfer
  F := event.frame
  z := event.energy
  w := event.energy
  left := true
  right := true
  lc := 1
  ls := 0
  rc := 1
  rs := 0

theorem dressed_kinematic_transfer (event : DressedEvent) (transfer : PhysicalMomentum) :
    PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalTransfer
      ((dressedKinematicPoint event transfer).p+(dressedKinematicPoint event transfer).k)
      (dressedKinematicPoint event transfer).p=transfer :=
  dressed_current_physical_transfer event transfer

/-- The original Euler minus is applied once to the actual unit minus its unchanged background. -/
def dressedEulerObserver (event : DressedEvent) : (H→L[ℂ]H)→L[ℂ]ℂ :=
  -((innerSL ℂ (sourceDressedUnit event.epsilon event.precision)).comp
      (ContinuousLinearMap.apply ℂ H (sourceDressedUnit event.epsilon event.precision))-
    (innerSL ℂ (prepared (sourceProfile event.epsilon event.precision))).comp
      (ContinuousLinearMap.apply ℂ H (prepared (sourceProfile event.epsilon event.precision))))

theorem dressed_euler_observer_original (event : DressedEvent) (A : H→L[ℂ]H) :
    dressedEulerObserver event A=
      -inner ℂ (sourceDressedUnit event.epsilon event.precision)
        (A (sourceDressedUnit event.epsilon event.precision))+
      inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (A (prepared (sourceProfile event.epsilon event.precision))) := by
  simp only [dressedEulerObserver, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, innerSL_apply_apply, neg_sub]
  abel

/-- Both time jets of the complete Noether operator are observed by precisely that preparation. -/
def dressedNoetherJet (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (t : ℝ) (i : Fin 289) : SourceJet ℂ :=
  let J:=noetherHistoryOperatorJet (dressedKinematicPoint event transfer) (fieldUnit i) signal t
  ⟨dressedEulerObserver event J.value,dressedEulerObserver event J.first,dressedEulerObserver event J.second⟩

theorem dressed_noether_jet_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (continuousSignal : Continuous (fun t=>(signal t).value))
    (t : ℝ) (paid : HasSourceJets signal t) (i : Fin 289) :
    HasSourceJets (fun s=>dressedNoetherJet event transfer signal s i) t := by
  have generated:=noetherHistoryOperatorJet_generated (dressedKinematicPoint event transfer)
    (fieldUnit i) signal continuousSignal t paid
  exact ⟨((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t generated.1,
    ((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t generated.2⟩

theorem dressed_noether_jet_continuous (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (paid : ContinuousJets signal) (i : Fin 289) :
    ContinuousJets (fun t=>dressedNoetherJet event transfer signal t i) := by
  have generated:=noetherHistoryOperatorJet_continuous (dressedKinematicPoint event transfer)
    (fieldUnit i) signal paid
  exact ⟨(dressedEulerObserver event).continuous.comp generated.1,
    (dressedEulerObserver event).continuous.comp generated.2.1,
    (dressedEulerObserver event).continuous.comp generated.2.2⟩

theorem dressed_noether_jet_original (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (t : ℝ) (i : Fin 289) :
    (dressedNoetherJet event transfer signal t i).value=
      dressedEulerObserver event
        ((noetherHistoryOperatorJet (dressedKinematicPoint event transfer) (fieldUnit i) signal t).value) := rfl

def dressedNoetherForcing (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (lambda : ℂ) (T : ℝ) : Fin 289→ℂ :=
  fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*(dressedNoetherJet event transfer signal t i).value

theorem dressed_noether_forcing_original (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (lambda : ℂ) (T : ℝ) (i : Fin 289) :
    dressedNoetherForcing event transfer signal lambda T i=
      ∫t in (0:ℝ)..T,laplaceWeight lambda t*
        dressedEulerObserver event
          ((noetherHistoryOperatorJet (dressedKinematicPoint event transfer) (fieldUnit i) signal t).value) := rfl

/-- The quantum vertex transfer and the native Green have the same physical momentum. -/
def dressedNoetherField (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (lambda : physicalSpectralDomain transfer) (T : ℝ) : Fin 289→ℂ :=
  PreparationVacuumOriginalGreenFeedback.sourceField ⟨fullMomentum (physicalSpatial transfer) lambda.val,lambda.property⟩
    (dressedNoetherForcing event transfer signal lambda.val T)

theorem dressed_noether_field_equation (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (lambda : physicalSpectralDomain transfer) (T : ℝ) :
    originalJacobi (fullMomentum (physicalSpatial transfer) lambda.val)*ᵥ
        dressedNoetherField event transfer signal lambda T=
      dressedNoetherForcing event transfer signal lambda.val T-
        originalRowLift (fullMomentum (physicalSpatial transfer) lambda.val)*ᵥ
          sourceCompatibility (fullMomentum (physicalSpatial transfer) lambda.val)
            (dressedNoetherForcing event transfer signal lambda.val T) := by
  exact original_forced_field ⟨_,lambda.property⟩ _

/-- Both real histories use the original complete Cauchy voltage, scalar ramp and constitutive B. -/
def dressedVoltageForcing (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) : Fin 289→ℂ :=
  dressedNoetherForcing event transfer (voltageNativeTimeJet (physicalSpatial transfer) false) lambda T+
    Complex.I • dressedNoetherForcing event transfer (voltageNativeTimeJet (physicalSpatial transfer) true) lambda T

def dressedVoltageUpdate (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : physicalSpectralDomain transfer) (T : ℝ) : Fin 289→ℂ :=
  PreparationVacuumOriginalGreenFeedback.sourceField ⟨fullMomentum (physicalSpatial transfer) lambda.val,lambda.property⟩
    (voltageWindowForcing (physicalSpatial transfer) lambda.val T+dressedVoltageForcing event transfer lambda.val T)

theorem dressed_voltage_update_original (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : physicalSpectralDomain transfer) (T : ℝ) :
    originalJacobi (fullMomentum (physicalSpatial transfer) lambda.val)*ᵥdressedVoltageUpdate event transfer lambda T=
      voltageWindowForcing (physicalSpatial transfer) lambda.val T+dressedVoltageForcing event transfer lambda.val T-
        originalRowLift (fullMomentum (physicalSpatial transfer) lambda.val)*ᵥ
          sourceCompatibility (fullMomentum (physicalSpatial transfer) lambda.val)
            (voltageWindowForcing (physicalSpatial transfer) lambda.val T+dressedVoltageForcing event transfer lambda.val T) := by
  exact original_forced_field ⟨_,lambda.property⟩ _

end LowEnergy.GaussComposite.ActualDressedNoether
