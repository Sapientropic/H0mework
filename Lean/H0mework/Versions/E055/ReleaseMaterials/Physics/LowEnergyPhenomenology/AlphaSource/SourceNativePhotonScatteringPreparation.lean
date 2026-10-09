import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualScatteringSoftReturn

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativePhotonScatteringSheetReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage9C.Material.SpinPair Stage10 CanonicalGradedSpatialSource
open PreparationPhysicalJointGeneratorEnergyReturn PreparationPhysicalChargedScatteringFourierReturn
open PreparationVacuumElectromagneticIdentity PreparationVacuumNativePoleTensor
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalQuantumLockedCharge
open GaussComposite.PhysicalFullFieldScattering Electromagnetic.CanonicalCoframe
open SourcePropagationNativeActionHessian Filter Set
open scoped BigOperators Matrix Topology
attribute [local irreducible] actualSheetField actualSheetResidue actualFrequencyResidue
  sourcePreparedScatteringPair originalTransferPair

/-- Each photon source leg keeps its actual charged maker pair, response point, momentum and preparation window. -/
structure SourcePhotonLeg where
  q : PhysicalResponsePoint
  momentum : PhysicalMomentum
  sideL : Fin 2
  edgeL : Fin 2
  sideR : Fin 2
  edgeR : Fin 2
  window : ℝ

def sourcePhotonField (leg : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  actualSheetField leg.q epsilon s n leg.momentum
    (sourceChargedRestIndex leg.sideL leg.edgeL) (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window

def sourcePhotonResidue (leg : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  actualSheetResidue leg.q epsilon s n leg.momentum
    (sourceChargedRestIndex leg.sideL leg.edgeL) (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window

def sourcePhotonFrequencyResidue (leg : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  actualFrequencyResidue leg.q epsilon s n leg.momentum
    (sourceChargedRestIndex leg.sideL leg.edgeL) (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window

/-- This is the original source-current momentum, not an independently selected scattering transfer. -/
theorem sourcePhoton_momentum (leg : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum) :
    sourcePhysicalTransfer (sheetLeft epsilon n leg.momentum) leg.momentum=epsilon^2 • n ∧
      actualMomentum (sheetLeft epsilon n leg.momentum) leg.momentum (sheetLambda epsilon s)=frequencyRay epsilon s n := by
  constructor
  · unfold sourcePhysicalTransfer sheetLeft
    abel
  · exact sheetMomentum_actual epsilon s n leg.momentum

/-- All nine constraints retain the actual initial/final source cosource. -/
theorem sourcePhoton_currentWard (leg : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum) :
    originalReadback (frequencyRay epsilon s n)*ᵥ
      sheetCurrent leg.q epsilon s n leg.momentum
        (sourceChargedRestIndex leg.sideL leg.edgeL) (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window=
      sheetCosource leg.q epsilon s n leg.momentum
        (sourceChargedRestIndex leg.sideL leg.edgeL) (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window :=
  sheetCurrent_ward leg.q epsilon s n leg.momentum _ _ leg.window

/-- The actual branch domain returns the entire original field equation with its null residual. -/
theorem sourcePhoton_fieldWhole (leg : SourcePhotonLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀ᶠ s in 𝓝[≠] (sourceSheet branch n unit e.val),
      nativeFourierHessian nativeHessian (frequencyRay e.val s n)*ᵥsourcePhotonField leg e.val s n=
        sheetCurrent leg.q e.val s n leg.momentum
          (sourceChargedRestIndex leg.sideL leg.edgeL) (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window-
          originalRowLift (frequencyRay e.val s n)*ᵥ
            (nullProjection*ᵥsheetCosource leg.q e.val s n leg.momentum
              (sourceChargedRestIndex leg.sideL leg.edgeL) (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window) :=
  actualSheetField_whole leg.q branch n leg.momentum unit _ _ leg.window

def sourcePhotonTransfer (positive negative : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum) : TransferPair :=
  originalTransferPair (sourcePhotonField positive epsilon s n) (sourcePhotonField negative epsilon s n)

def sourcePhotonResidueTransfer (positive negative : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum) : TransferPair :=
  originalTransferPair (sourcePhotonResidue positive epsilon s n) (sourcePhotonResidue negative epsilon s n)

def sourcePhotonFrequencyResidueTransfer (positive negative : SourcePhotonLeg) (epsilon s : ℝ)
    (n : PhysicalMomentum) : TransferPair :=
  originalTransferPair (sourcePhotonFrequencyResidue positive epsilon s n) (sourcePhotonFrequencyResidue negative epsilon s n)

/-- The same actual charged external preparations consume source photon legs and their identical physical transfer. -/
def sourcePhotonScatteringPair (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) : ℂ × ℂ :=
  sourcePreparedScatteringPair sideL edgeL sideR edgeR
    (sourcePhotonTransfer Ap An epsilon s n) (sourcePhotonTransfer Bp Bn epsilon s n) (epsilon^2 • n) time age

def sourcePhotonScatteringResidue (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) : ℂ × ℂ :=
  sourcePreparedScatteringPair sideL edgeL sideR edgeR
    (sourcePhotonResidueTransfer Ap An epsilon s n) (sourcePhotonResidueTransfer Bp Bn epsilon s n) (epsilon^2 • n) time age

def sourcePhotonScatteringFrequencyResidue (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : SourcePhotonLeg) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) : ℂ × ℂ :=
  sourcePreparedScatteringPair sideL edgeL sideR edgeR
    (sourcePhotonFrequencyResidueTransfer Ap An epsilon s n) (sourcePhotonFrequencyResidueTransfer Bp Bn epsilon s n)
      (epsilon^2 • n) time age

/-- The two source branches determine the frequency slope before any electromagnetic interpretation. -/
theorem sourcePhoton_frequencySlope (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>sourceFrequency e.val (sourceSheet branch n unit e.val)/e.val^2)
      scaleApproach (𝓝 (sourceSpeed branch)) := by
  have read:=(sourceSheet_tendsto branch n unit).comp scaleVal_tendsto
  apply read.congr'
  filter_upwards [] with e
  dsimp [sourceFrequency]
  field_simp [e.property.1.ne']

end LowEnergy.PreparationPhysicalNativePhotonScatteringSheetReturn
