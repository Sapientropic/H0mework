import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceDirectionPhysicalCurrent
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceEnergyPreparedWard
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedNativeEnergyDomain

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalRemainderWardPoleReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy Stage10
open FullQuantum FullSpace
open PreparationPhysicalElectromagneticDirectionReturn PreparationPhysicalEnergyCurrentWardReturn
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedVertexDomainReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalFilteredChargeVoltage PreparationPhysicalFilteredLockedChargeReturn
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumChargedLongRangeRead
open PreparationVacuumPhysicalElectromagneticDirection PreparationVacuumMixedFieldReturn
open PreparationVacuumCausalPoleResponse PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumOriginalGreenFeedback PreparationVacuumNativeSlowCoupling PreparationVacuumWholeOrigin
open PreparationPhysicalNormalizedFullField CanonicalGradedSpatialSource
open MeasureTheory Filter
open scoped Matrix BigOperators Topology InnerProductSpace
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
attribute [local irreducible] sourceChargedNativeFrameJet sourceChargedChannel sourcePhysicalEnergyReader
  sourcePhysicalEnergyChannel sourceChargedFieldRemainder sourceChargedFilteredPacket

private theorem five_single (i : Fin 3) :
    fiveVector (Pi.single (⟨i.val,by omega⟩:Fin 5) (1:ℂ))=
      Pi.single (⟨i.val,by omega⟩:Fin 289) (1:ℂ) := by
  funext j
  by_cases inside : j.val<5
  · simp [fiveVector,inside,Pi.single_apply,Fin.ext_iff]
  · have different : i.val≠j.val:=by omega
    simp [fiveVector,inside,Fin.ext_iff,different]

/-- This is the original frame column, with the same three slow-coordinate injection. -/
theorem sourceChannel_column (n : PhysicalMomentum) (zeta : ℂ) (i : Fin 3) :
    sourceChargedChannel n zeta i=
      fun row=>sourceChargedNativeFrameJet (fixedMomentum n zeta) row ⟨i.val,by omega⟩ := by
  rw [sourceChargedChannel,five_single,Matrix.mulVec_single_one]
  rfl

/-- A0 vanishes by the actual full200 calculation, although the complete physical energy in this channel need not vanish. -/
theorem sourceChannelTwo_temporal_zero (n : PhysicalMomentum) (zeta : ℂ) :
    sourceChargedCoefficient (sourceChargedChannel n zeta 2) 0=0 := by
  rw [sourceChannel_column]
  change sourceChargedNativeFrameJet (fixedMomentum n zeta)
    (lorentzSlot 0 (sourceSpinSlot 2)) (2:Fin 289)=0
  exact (sourceDirectionLiteral_generated (fixedMomentum n zeta) 0 (2:Fin 3)).trans rfl

/-- In the same actual channel, the complete remaining-field energy equals the original full physical energy, not a remainder estimate. -/
theorem sourceChannelTwo_otherEnergy (shift : Position) (zeta : ℂ)
    (sideL edgeL sideR edgeR : Fin 2) :
    sourceDirectionOtherEnergy (sourceChargedChannel (physicalMomentum shift) zeta 2)
      shift sideL edgeL sideR edgeR=sourcePhysicalEnergyChannel shift zeta 2 sideL edgeL sideR edgeR := by
  rw [sourcePhysicalEnergyChannel_generated]
  unfold sourceDirectionOtherEnergy sourceChargedFieldRemainder sourceChargedFieldPart
  simp only [map_sub,map_add,map_smul,smul_eq_mul,Fin.sum_univ_four,Fin.sum_univ_three,
    sourceChannelTwo_temporal_zero,zero_mul,zero_add,
    show (0:Fin 3).succ=(1:Fin 4) from rfl,
    show (1:Fin 3).succ=(2:Fin 4) from rfl,
    show (2:Fin 3).succ=(3:Fin 4) from rfl]
  ring

/-- The original full Dirac input/damping Ward now evaluates the complete other-energy term; both actual preparations and their generated retention are retained. -/
theorem sourceChannelTwo_otherWard (shift : Position) (frequency : ℝ)
    (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
      (sourceChargedChannel (physicalMomentum shift) (Complex.I*(frequency:ℂ)) 2)
        shift sideL edgeL sideR edgeR=
      (frequency:ℂ)*sourceFilteredChargeFormFactor shift sideL edgeL sideR edgeR-
        ((5/3:ℂ)*(ActionNormalization.phaseMomentum:ℂ))*
          ∫k : Position,sourceEnergyRetainedWardIntegrand shift sideL edgeL sideR edgeR k := by
  rw [sourceChannelTwo_otherEnergy]
  exact sourceEnergyChannel_two_retainedWard shift frequency sideL edgeL sideR edgeR

/-- Homogeneity comes from the same original first derivative of the complete native frame. -/
theorem sourceNativeFrameJet_scaled (z : ℂ) (v : Fin 4→ℂ) :
    sourceChargedNativeFrameJet (z • v)=z • sourceChargedNativeFrameJet v := by
  simp only [sourceChargedNativeFrameJet,sourceLinearPart,degreeTensor_scaled,pow_one,
    smul_mul_assoc,mul_smul_comm,←smul_sub]

private theorem frequency_fixed (s : ℝ) (n : PhysicalMomentum) :
    fixedMomentum n (-Complex.I*(s:ℂ))=physicalFrequencyMomentum s n := rfl

/-- The epsilon-squared physical momentum is read by the already generated Fourier shift; the physical minus-i frequency fixes the sign. -/
theorem sourceChannel_physicalScale (epsilon s : ℝ) (n : PhysicalMomentum) (i : Fin 3) :
    (epsilon:ℂ)^2 • sourceChargedChannel n (-Complex.I*(s:ℂ)) i=
      sourceChargedChannel (physicalMomentum (sourcePhotonEnergyShift epsilon n))
        (Complex.I*((-sourceFrequency epsilon s:ℝ):ℂ)) i := by
  rw [sourcePhotonEnergyShift_momentum]
  have momentum : fixedMomentum (epsilon^2 • n) (Complex.I*((-sourceFrequency epsilon s:ℝ):ℂ))=
      (epsilon:ℂ)^2 • fixedMomentum n (-Complex.I*(s:ℂ)) := by
    rw [frequency_fixed]
    have frequency : Complex.I*((-sourceFrequency epsilon s:ℝ):ℂ)=
        -Complex.I*((s*epsilon^2:ℝ):ℂ) := by
      simp only [sourceFrequency,Complex.ofReal_neg,Complex.ofReal_mul]
      ring
    rw [frequency,frequency_fixed,←frequencyRay_scaled]
    rfl
  simp only [sourceChargedChannel,momentum,sourceNativeFrameJet_scaled,Matrix.smul_mulVec]

/-- The full physical channel at the actual pole scale has its source-unit charge term and exact Dirac input/damping return. -/
theorem sourceChannelTwo_physicalWard (epsilon s : ℝ) (n : PhysicalMomentum)
    (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyReader (sourcePhotonEnergyShift epsilon n)
      sideL edgeL sideR edgeR
      ((epsilon:ℂ)^2 • sourceChargedChannel n (-Complex.I*(s:ℂ)) 2)=
      (-sourceFrequency epsilon s:ℂ)*
        sourceFilteredChargeFormFactor (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR-
      ((5/3:ℂ)*(ActionNormalization.phaseMomentum:ℂ))*
        ∫k : Position,sourceEnergyRetainedWardIntegrand (sourcePhotonEnergyShift epsilon n)
          sideL edgeL sideR edgeR k := by
  rw [sourceChannel_physicalScale,←sourcePhysicalEnergyChannel_generated]
  simpa only [Complex.ofReal_neg] using sourceEnergyChannel_two_retainedWard (sourcePhotonEnergyShift epsilon n)
    (-sourceFrequency epsilon s) sideL edgeL sideR edgeR

end LowEnergy.PreparationPhysicalRemainderWardPoleReturn
