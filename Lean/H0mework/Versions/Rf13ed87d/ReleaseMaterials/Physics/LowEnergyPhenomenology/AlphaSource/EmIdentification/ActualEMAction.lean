import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMInfrared
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeLocalAction
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationOriginalHessianReturn

set_option autoImplicit false
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMAction
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativePointwiseActionJetCarrier
open SourcePropagationNativeActionHessian SourcePropagationMotherEulerKernel
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationPhysicalNativePhotonFluxReturn PreparationVacuumPhysicalChargedFieldFactor
open CanonicalGradedSpatialSource
open ActualEMCarrierOwn Filter Set
open scoped Matrix BigOperators Topology

/-- Literal original action on its actual first-jet restriction, with the repaired independent dual. -/
def emOriginalAction (jet : NativeFirstJet) : ℝ :=
  generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
    positiveSmoothUnifiedSource (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
    0 0 (nativeLocalPoint 0 jet)

theorem em_action_source (jet : NativeFirstJet) : emOriginalAction jet = nativeJetDensity jet :=
  (nativeLocalAction_original 0 jet).symm.trans (nativeLocalAction_zero jet)

def emOriginalHessian : NativeFirstJet →L[ℝ] NativeFirstJet →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ emOriginalAction) 0

theorem em_hessian_source : emOriginalHessian = nativeHessian := by
  have same : emOriginalAction = nativeJetDensity := funext em_action_source
  unfold emOriginalHessian
  rw [same]
  rfl

def emOriginalJacobi (p : Fin 4 → ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  nativeFourierHessian emOriginalHessian p

theorem em_jacobi_source (p : Fin 4 → ℂ) : emOriginalJacobi p = originalJacobi p := by
  unfold emOriginalJacobi
  rw [em_hessian_source]
  exact nativeActionFourierHessian_original p

def emActionSheetJet (epsilon s : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  deriv (fun t : ℝ => emOriginalJacobi (frequencyRay epsilon t n)) s

theorem em_action_sheet_jet (epsilon s : ℝ) (n : PhysicalMomentum) :
    emActionSheetJet epsilon s n = sourcePhotonSheetJacobiJet epsilon s n := by
  unfold emActionSheetJet sourcePhotonSheetJacobiJet
  congr 1
  funext t
  exact em_jacobi_source _

/-- The original physical clock, before differentiating the full action pencil. -/
def emActionFrequencyJacobi (epsilon omega : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  emOriginalJacobi (frequencyRay epsilon (omega / epsilon ^ 2) n)

def emActionFrequencyJet (epsilon omega : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  deriv (fun w : ℝ => emActionFrequencyJacobi epsilon w n) omega

theorem em_action_frequency_jet (epsilon omega : ℝ) (n : PhysicalMomentum) :
    emActionFrequencyJet epsilon omega n = sourcePhotonFrequencyJacobiJet epsilon omega n := by
  unfold emActionFrequencyJet sourcePhotonFrequencyJacobiJet
  congr 1
  funext w
  exact em_jacobi_source _

/-- All output rows of the actual EM carrier solve the literal action Hessian equation. -/
theorem em_action_carrier_homogeneous (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) :
    ∀ᶠ e in scaleApproach,
      emOriginalJacobi (frequencyRay e.val (sourceSheet branch n unit e.val) n) *
        emPropagatingCarrier e.val (sourceSheet branch n unit e.val) n = 0 := by
  filter_upwards [em_carrier_homogeneous branch n unit] with e equation
  rw [em_jacobi_source]
  exact equation

/-- The EM residue consumes the derivative of the same literal source action. -/
theorem em_action_sheet_flux (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) :
    ∀ᶠ e in scaleApproach,
      emInsertion.transpose * sourceWholePhotonResidue e.val (sourceSheet branch n unit e.val) n *
        emActionSheetJet e.val (sourceSheet branch n unit e.val) n *
        emPropagatingCarrier e.val (sourceSheet branch n unit e.val) n =
      emPoleTensor e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [em_flux_generated branch n unit] with e flux
  rw [em_action_sheet_jet]
  exact flux

/-- Physical-frequency normalization uses the source clock and its original Hessian derivative once. -/
theorem em_action_frequency_flux (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n = 1) :
    ∀ᶠ e in scaleApproach,
      emInsertion.transpose * sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *
        emActionFrequencyJet e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n *
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n * emInsertion) =
      emInsertion.transpose * sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *
        emInsertion := by
  filter_upwards [sourceWholePhotonResidue_frequencyFlux branch n unit] with e flux
  rw [em_action_frequency_jet]
  calc
    _ = emInsertion.transpose *
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *
          sourcePhotonFrequencyJacobiJet e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n *
          sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n) * emInsertion := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [flux]

end LowEnergy.GaussComposite.ActualEMAction
