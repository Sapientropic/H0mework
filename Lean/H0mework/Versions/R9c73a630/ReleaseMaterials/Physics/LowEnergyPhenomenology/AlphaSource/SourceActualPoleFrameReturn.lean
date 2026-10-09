import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativePolarizationFlux
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceSoftNativeFrame
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceEnergyChannelFrame

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativePoleChargeReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse PreparationVacuumWholeOrigin
open PreparationVacuumFullSlowFieldResponse PreparationVacuumNativePoleTensor PreparationVacuumSoftPoleSelection
open PreparationVacuumPhysicalChargedFieldFactor PreparationPhysicalNativePolarizationEmitter
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNormalizedFullField
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] originalChange fullKernelFrame slowFastFrame sourceNativeFrame sourceResidue
  sourceChargedNativeFrameJet sourceChargedNativeFrameResidual sourceNativePolarization

/-- The actual pole column retains all five coordinates and the original slow/fast scaling. -/
def sourcePoleCoordinates (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  fiveVector (regularScaling epsilon*ᵥsourceNativePoleColumn branch epsilon s n)

def sourcePoleOriginField (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  (fullNativeOrigin*slowFastFrame)*ᵥsourcePoleCoordinates branch epsilon s n

def sourcePoleJetField (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  sourceChargedNativeFrameJet (physicalFrequencyMomentum s n)*ᵥsourcePoleCoordinates branch epsilon s n

def sourcePoleFrameResidual (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  sourceChargedNativeFrameResidual ((epsilon:ℂ)^2) (physicalFrequencyMomentum s n)*ᵥ
    sourcePoleCoordinates branch epsilon s n

/-- This is the same frequency-flux polarization, not an independent frozen forcing or chosen vector. -/
theorem sourceNativeFrequencyPolarization_frame (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) :
    sourceNativeFrequencyPolarization branch epsilon s n=
      sourceNativeFrame (frequencyRay epsilon s n)*ᵥsourcePoleCoordinates branch epsilon s n := by
  have returned:=softInsertion_generated epsilon s n nonzero (sourceNativePoleColumn branch epsilon s n)
  have castSmul (v : Fin 289→ℂ) : (epsilon:ℂ)^2 • v=(epsilon^2:ℝ) • v := by
    ext i
    simp only [Pi.smul_apply,Complex.real_smul,Complex.ofReal_pow,smul_eq_mul]
  rw [castSmul] at returned
  simpa only [sourceNativeFrequencyPolarization,sourceNativePolarization,sourceNativeFrame,
    sourcePoleCoordinates,softInsertion,Matrix.mulVec_mulVec,mul_assoc] using returned

/-- The actual pole field consumes the full source Taylor identity with its current residue column, including both fast coordinates. -/
theorem sourceNativeFrequencyPolarization_firstReturn (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) :
    sourceNativeFrequencyPolarization branch epsilon s n-sourcePoleOriginField branch epsilon s n-
      (epsilon:ℂ)^2 • sourcePoleJetField branch epsilon s n=sourcePoleFrameResidual branch epsilon s n := by
  have returned:=congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>M*ᵥsourcePoleCoordinates branch epsilon s n)
    (sourceChargedNativeFrame_first_return ((epsilon:ℂ)^2) (physicalFrequencyMomentum s n))
  rw [sourceNativeFrequencyPolarization_frame branch epsilon s n nonzero,frequencyRay_scaled]
  simpa only [Matrix.sub_mulVec,Matrix.smul_mulVec,sourcePoleOriginField,sourcePoleJetField,sourcePoleFrameResidual]
    using returned

theorem sourcePoleOriginField_charge (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (mu : Fin 4) :
    sourceChargedCoefficient (sourcePoleOriginField branch epsilon s n) mu=0 := by
  unfold sourcePoleOriginField
  rw [←Matrix.mulVec_mulVec]
  exact sourceChargedNativeOrigin_slot _ mu

/-- The zero-order charge projection cancels for the entire current pole column, before any scalar or species interpretation. -/
theorem sourceNativeFrequencyPolarization_charge (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) (mu : Fin 4) :
    sourceChargedCoefficient (sourceNativeFrequencyPolarization branch epsilon s n) mu=
      (epsilon:ℂ)^2*sourceChargedCoefficient (sourcePoleJetField branch epsilon s n) mu+
        sourceChargedCoefficient (sourcePoleFrameResidual branch epsilon s n) mu := by
  have returned:=congrFun (sourceNativeFrequencyPolarization_firstReturn branch epsilon s n nonzero)
    (PreparationVacuumMixedFieldReturn.lorentzSlot mu (PreparationVacuumPhysicalElectromagneticDirection.sourceSpinSlot 2))
  change sourceChargedCoefficient (sourceNativeFrequencyPolarization branch epsilon s n) mu-
    sourceChargedCoefficient (sourcePoleOriginField branch epsilon s n) mu-
      (epsilon:ℂ)^2*sourceChargedCoefficient (sourcePoleJetField branch epsilon s n) mu=
    sourceChargedCoefficient (sourcePoleFrameResidual branch epsilon s n) mu at returned
  rw [sourcePoleOriginField_charge,sub_zero] at returned
  exact sub_eq_iff_eq_add.mp returned |>.trans (add_comm _ _)

/-- The literal 200-term source matrix supplies all three slow columns of this same actual pole jet. -/
def sourcePoleLiteralJet (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  sourceMatrix sourceEnergyChannelTerms (physicalFrequencyMomentum s n)*ᵥsourcePoleCoordinates branch epsilon s n

/-- The remaining coordinates are retained with their actual source frame action. -/
def sourcePoleFastJet (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  sourceChargedNativeFrameJet (physicalFrequencyMomentum s n)*ᵥ
    ((1-projectionMatrix (fun j : Fin 289=>decide (j.val<3)))*ᵥsourcePoleCoordinates branch epsilon s n)

theorem sourcePoleJetField_literal (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    sourcePoleJetField branch epsilon s n=sourcePoleLiteralJet branch epsilon s n+sourcePoleFastJet branch epsilon s n := by
  unfold sourcePoleJetField sourcePoleLiteralJet sourcePoleFastJet
  have generated:=sourceEnergyChannelMatrix_generated (physicalFrequencyMomentum s n)
  change sourceMatrix sourceEnergyChannelTerms (physicalFrequencyMomentum s n)=
    sourceChargedNativeFrameJet (physicalFrequencyMomentum s n)*projectionMatrix (fun j : Fin 289=>decide (j.val<3)) at generated
  rw [generated,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.mulVec_sub,Matrix.mulVec_mulVec]
  abel

end LowEnergy.PreparationPhysicalNativePoleChargeReturn
