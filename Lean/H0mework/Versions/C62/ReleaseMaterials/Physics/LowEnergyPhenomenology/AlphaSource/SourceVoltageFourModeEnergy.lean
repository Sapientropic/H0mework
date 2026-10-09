import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceVoltageNoetherPrepared

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalVoltageNoetherChargeReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy Stage10
open FullQuantum FullSpace Stage9C.Material.SpinPair
open PreparationVacuumNoetherChart PreparationVacuumNoetherOrdinaryWard PreparationVacuumOrderedRealSignal
open PreparationVacuumPhysicalFeedback PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumActionFieldLift PreparationVacuumMatterEulerFeedback PreparationVacuumOriginalGreenFeedback
open PreparationPhysicalVoltageEnergyIdentity PreparationPhysicalVoltageCompleteReturn
open PreparationPhysicalChargedEnergyVariation PreparationPhysicalChargedEnergyPoleReturn
open PreparationPhysicalChargedPacketVoltage PreparationVacuumVoltageGaussGreen
open CanonicalGradedSpatialSource
open MeasureTheory Filter
open scoped Topology BigOperators Matrix
local instance : DecidableEq PhysicalMomentum:=Classical.decEq _

private def unitBranch (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (time : ℝ) : ℂ :=
  if response then sourceVoltageUnitPreparedSlope q force time else sourceVoltageUnitPreparedCurrent q time

/-- The four original physical modes retain the reverse and both independent cross preparations, including coincident modes. -/
def sourceVoltageUnitModes (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (time : ℝ) : MomentumCoefficients :=
  let F:=unitBranch q force response time
  let R:=unitBranch (oppositeCoordinates q) force response time
  let DR:=unitBranch (crossRightCoordinates q) force response time
  let DL:=unitBranch (crossLeftCoordinates q) force response time
  Finsupp.single (-q.k) ((1/2:ℂ)*(F+star R))+Finsupp.single q.k ((1/2:ℂ)*(R+star F))+
    Finsupp.single (2 • q.p+q.k) ((1/2:ℂ)*(DR+star DL))+
      Finsupp.single (-(2 • q.p+q.k)) ((1/2:ℂ)*(DL+star DR))

/-- The original Euler minus is used exactly once. -/
theorem sourceVoltageModeJet_value (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (time : ℝ) :
    (modeJet q force response wave time 20).value=
      -(ActionNormalization.phaseMomentum:ℂ)*sourceVoltageUnitModes q force response time (-wave) := by
  cases response <;>
    simp only [modeJet,realEulerTimeJet,negativeJet,realCoefficientJet_value,Bool.false_eq_true,
      ite_false,ite_true,coefficientSlope,realDensityCoefficients,oppositeCurrent_actual,crossRight_actual,crossLeft_actual,
      sourceVoltageNoetherPreparedCurrent,sourceVoltageNoetherPreparedSlope,sourceVoltageUnitModes,unitBranch,
      Finsupp.add_apply,Finsupp.single_apply,star_mul,Complex.star_def,Complex.conj_ofReal]
  all_goals split_ifs <;> ring

def sourceVoltageUnitGaussSource (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (z : ℂ) (T : ℝ) : ℂ :=
  ∫t in (0:ℝ)..T,PreparationVacuumGaugeSourceInjection.laplaceWeight z t*sourceVoltageUnitModes q force response t (-wave)

theorem sourceVoltageModeForcing_charge (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (wave : PhysicalMomentum) (z : ℂ) (T : ℝ) :
    modeForcing q force response wave z T 20=
      -(ActionNormalization.phaseMomentum:ℂ)*sourceVoltageUnitGaussSource q force response wave z T := by
  simp only [modeForcing,sourceVoltageModeJet_value,sourceVoltageUnitGaussSource]
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  ring

/-- The test vertex is the original charged packet's actual raw current integral, before its proved unit return. -/
def sourcePreparedPhysicalVoltageEnergy (q : PhysicalResponsePoint) (force : Field289) (shift : Position)
    (z : physicalSpectralDomain (physicalMomentum shift)) (T : ℝ) (side edge : Fin 2) : ℂ :=
  -(∫x : Fin 3→ℝ,sourceVoltageRawCharge (sourceChargedPacketMatter side edge) (sourceChargedPacketDual side edge) x)*
    sourcePhysicalEnergyReader shift side edge side edge (deriv (actionFieldCurve q force (physicalMomentum shift) z T) 0)

/-- The second original Noether vertex supplies the second h; no charge-unit constant is inserted by definition. -/
theorem sourcePreparedPhysicalVoltageEnergy_generated (q : PhysicalResponsePoint) (force : Field289) (shift : Position)
    (z : physicalSpectralDomain (physicalMomentum shift)) (nonzero : z.val≠0)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) (side edge : Fin 2) :
    sourcePreparedPhysicalVoltageEnergy q force shift z T side edge=
      -(ActionNormalization.phaseMomentum:ℂ)^2/(2*(lapse:ℂ)*(spatialSquare (physicalMomentum shift):ℂ))*
        sourceVoltageUnitGaussSource q force true (physicalMomentum shift) z.val T*
        sourceChargedVoltageOverlap shift side edge side edge-
      (ActionNormalization.phaseMomentum:ℂ)*sourcePreparedVoltageAmplitude q force (physicalMomentum shift) z.val T*
        sourceFullEnergyRead
          (originalChange (fullMomentum (physicalSpatial (physicalMomentum shift)) z.val)*ᵥ(nullProjection*ᵥ
            (originalInverse (fullMomentum (physicalSpatial (physicalMomentum shift)) z.val)*ᵥ
              sourceVoltageLaplaceRamp (physicalSpatial (physicalMomentum shift)) z.val))) shift side edge side edge+
      (ActionNormalization.phaseMomentum:ℂ)*sourceFullEnergyRead
        (PreparationVacuumOriginalGreenFeedback.sourceField
          ⟨fullMomentum (physicalSpatial (physicalMomentum shift)) z.val,z.property⟩
          (sourcePreparedVoltageRemainder q force (physicalMomentum shift) z.val T)) shift side edge side edge := by
  rw [sourcePreparedPhysicalVoltageEnergy,sourceChargedPacket_totalCurrent,Complex.ofReal_neg,neg_neg,
    sourcePreparedVoltageEnergy_gauss q force shift z nonzero hz hw T side edge side edge,
    sourceVoltageModeForcing_charge q force true (physicalMomentum shift) z.val T]
  ring

end LowEnergy.PreparationPhysicalVoltageNoetherChargeReturn
