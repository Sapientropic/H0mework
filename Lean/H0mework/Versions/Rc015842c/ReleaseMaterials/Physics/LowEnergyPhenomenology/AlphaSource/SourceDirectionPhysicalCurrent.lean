import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceLockedPoleDirection

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalElectromagneticDirectionReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy Stage10
open FullQuantum FullSpace FullQuantum.CoframeResponse FullQuantum.StateGreen
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalFilteredLockedChargeReturn
open PreparationPhysicalVoltageEnergyIdentity PreparationVacuumNonlinearFieldCurve
open PreparationVacuumVoltageGaussGreen PreparationVacuumPhysicalQuantumLockedCharge GaussHistoryHilbert
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumPhysicalElectromagneticDirection
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn
open PreparationPhysicalNativePhotonScatteringSheetReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators Matrix Matrix.Norms.L2Operator
attribute [local irreducible] sourcePhysicalEnergyReader sourceChargedEnergyRead PreparationPhysicalChargedEnergyVariation.sourceFullEnergyRead
  sourceChargedFilteredPacket sourceNativeFrequencyPolarization sourceChargedFieldRemainder
local instance directionCurrentIndex : DecidableEq Quantum.Index:=Classical.decEq _

private theorem energy_real_matrix (f : Field289) (p : PhysicalMomentum) :
    affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState (fieldDirection f)) p=
      ∑j : Fin 289,(f j:ℂ) •
        affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState (fieldDirection (fieldUnit j))) p := by
  have source:=congrArg (fun M : FullMatrix=>M.toBlocks₁₁)
    (sourceFullEnergyMatrix_generated p sourceVoltageActualState (sourceState_valid sourcePoint)
      (fun j=>(f j:ℂ)))
  rw [sourceFullEnergyMatrix_real p sourceVoltageActualState (sourceState_valid sourcePoint),
    sourceNormalizedEnergySymbol_matrix p sourceVoltageActualState _ (sourceState_valid sourcePoint)] at source
  apply Matrix.ext
  intro a b
  have entry:=congrFun (congrFun source a) b
  simpa only [Matrix.toBlocks₁₁,Matrix.of_apply,Matrix.sum_apply,Matrix.smul_apply,
    fourierLinear,LinearMap.coe_mk,AddHom.coe_mk,realFourierMatrix,Matrix.fromBlocks_apply₁₁] using entry

/-- The physical read of a real full-field direction is the same original Hamiltonian derivative on the actual two filtered preparations. -/
private theorem energy_real (f : Field289) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR (fun j=>(f j:ℂ))=
      sourceChargedEnergyRead (fieldDirection f) shift sideL edgeL sideR edgeR := by
  rw [sourcePhysicalEnergyReader_original,sourceFullEnergyRead_generated,sourceChargedEnergyRead_fourier]
  simp_rw [sourceChargedEnergyRead_fourier]
  have pointwise (frequency : Position) :
      inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
        (sourceEnergyMatrixRead (affineMatrix
          (sourceHamiltonianJetMatrix sourceVoltageActualState (fieldDirection f))
          (physicalMomentum (frequency-shift)))
          (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift)))=
      ∑j : Fin 289,(f j:ℂ)*inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
        (sourceEnergyMatrixRead (affineMatrix
          (sourceHamiltonianJetMatrix sourceVoltageActualState (fieldDirection (fieldUnit j)))
          (physicalMomentum (frequency-shift)))
          (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))) := by
    rw [energy_real_matrix]
    simp only [map_sum,map_smul,sum_apply,smul_apply,inner_sum,inner_smul_right]
  simp_rw [pointwise]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro j _
    exact (sourceChargedEnergyRead_integrable (fieldDirection (fieldUnit j)) shift sideL edgeL sideR edgeR).const_mul _

private theorem locked_temporal (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*
      sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR (sourceChargedLockedField 0)=
      -sourceFilteredLockedFormFactor shift sideL edgeL sideR edgeR := by
  change (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR
    (fun j=>(sourceLockedField 0 2 j:ℂ))=_
  rw [energy_real]
  exact sourceLockedEnergy_current shift sideL edgeL sideR edgeR

/-- Every spatial locked insertion and the entire other field tensor remain in the original physical energy read. -/
def sourceDirectionOtherEnergy (V : Fin 289→ℂ) (shift : Position)
    (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  (∑j : Fin 3,sourceChargedCoefficient V j.succ*
    sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR (sourceChargedLockedField j.succ))+
  sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR (sourceChargedFieldRemainder V)

private theorem full_energy_split (V : Fin 289→ℂ) (shift : Position)
    (sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR V=
      sourceChargedCoefficient V 0*
        sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR (sourceChargedLockedField 0)+
      sourceDirectionOtherEnergy V shift sideL edgeL sideR edgeR := by
  have field : V=sourceChargedFieldPart V+sourceChargedFieldRemainder V := by
    unfold sourceChargedFieldRemainder
    abel
  have read:=congrArg (sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR) field
  simp only [map_add,sourceChargedFieldPart,map_sum,map_smul,smul_eq_mul] at read
  rw [Fin.sum_univ_succ] at read
  simpa only [sourceDirectionOtherEnergy,add_assoc] using read

/-- The temporal unit current is paid by the same original energy and h normalization; no part of the other tensor is discarded. -/
theorem sourceDirectionPole_energy (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR
      (sourceNativeFrequencyPolarization branch epsilon s n)=
      -sourceDirectionPoleCoefficient branch epsilon s n 0*
        sourceFilteredLockedFormFactor shift sideL edgeL sideR edgeR+
      (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
        (sourceNativeFrequencyPolarization branch epsilon s n) shift sideL edgeL sideR edgeR := by
  rw [full_energy_split,sourceDirectionPoleCoefficient_generated branch epsilon s n nonzero]
  have unit:=locked_temporal shift sideL edgeL sideR edgeR
  linear_combination sourceDirectionPoleCoefficient branch epsilon s n 0*unit

/-- Actual unit charge is accompanied by the source Green torque correction, independently of the full remaining field tensor. -/
theorem sourceDirectionPole_actualUnit (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR
      (sourceNativeFrequencyPolarization branch epsilon s n)=
      (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionPoleCoefficient branch epsilon s n 0*
        (sourceChargedPolarity edgeR:ℂ)*sourceChargedVoltageOverlap shift sideL edgeL sideR edgeR-
      (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionPoleCoefficient branch epsilon s n 0*
        inner ℂ (sourceChargedFilteredPacket sideL edgeL)
          (PacketNoise.phaseShift shift (sourceFilteredLockedCorrection sideR edgeR))+
      (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
        (sourceNativeFrequencyPolarization branch epsilon s n) shift sideL edgeL sideR edgeR := by
  rw [sourceDirectionPole_energy branch epsilon s n nonzero,sourceFilteredLockedFormFactor_generated]
  ring

/-- The observable is evaluated at the original physical-frequency residue, with the very same independent emitter that fixes its flux. -/
theorem sourceDirectionResidue_energy (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    ∀ᶠ e in scaleApproach,∀leg : SourcePhotonLeg,
      (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR
        (sourcePhotonFrequencyResidue leg e.val (sourceSheet branch n unit e.val) n)=
        sourcePhotonEmitter leg branch e.val (sourceSheet branch n unit e.val) n*
          (-sourceDirectionPoleCoefficient branch e.val (sourceSheet branch n unit e.val) n 0*
            sourceFilteredLockedFormFactor shift sideL edgeL sideR edgeR+
          (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
            (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n)
              shift sideL edgeL sideR edgeR) := by
  filter_upwards [sourcePhotonFrequencyResidue_fluxFactor branch n unit] with e factor
  intro leg
  rw [factor leg,map_smul,smul_eq_mul]
  have read:=sourceDirectionPole_energy branch e.val (sourceSheet branch n unit e.val) n
    e.property.1.ne' shift sideL edgeL sideR edgeR
  linear_combination sourcePhotonEmitter leg branch e.val (sourceSheet branch n unit e.val) n*read

/-- The full field, including every remaining component, keeps the original finite preparation price. -/
theorem sourceDirectionPole_price (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    ‖sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR
      (sourceNativeFrequencyPolarization branch epsilon s n)‖≤
      sourceFullEnergyPrice (sourceNativeFrequencyPolarization branch epsilon s n) sideR edgeR := by
  rw [sourcePhysicalEnergyReader_original]
  exact sourceFullEnergyRead_norm _ shift sideL edgeL sideR edgeR

end LowEnergy.PreparationPhysicalElectromagneticDirectionReturn
