import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceRemainderChannelWard

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
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn
open PreparationPhysicalNativePolarizationEmitter PreparationPhysicalNativePhotonScatteringSheetReturn
open PreparationVacuumPhysicalQuantumLockedCharge PreparationPhysicalChargedPacketVoltage
open MeasureTheory Filter
open scoped Matrix BigOperators Topology InnerProductSpace
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
attribute [local irreducible] sourceChargedNativeFrameJet sourceChargedChannel sourcePhysicalEnergyReader
  sourcePhysicalEnergyChannel sourceChargedFieldRemainder sourceChargedFilteredPacket
  sourcePoleCoordinates sourcePoleOriginField sourcePoleFastJet sourcePoleFrameResidual
  sourceNativeFrequencyPolarization sourceFilteredLockedFormFactor sourceDirectionOtherEnergy

private theorem first_three (w : Fin 289→ℂ) :
    projectionMatrix (fun j : Fin 289=>decide (j.val<3))*ᵥw=
      ∑i : Fin 3,w ⟨i.val,by omega⟩ • Pi.single (⟨i.val,by omega⟩:Fin 289) (1:ℂ) := by
  funext j
  by_cases small : j.val<3
  · have cases : j=0 ∨ j=1 ∨ j=2 := by
      simp only [Fin.ext_iff]
      omega
    rcases cases with rfl|rfl|rfl <;>
      simp [projectionMatrix,Matrix.mulVec_diagonal,Fin.sum_univ_three,Pi.single_apply,
        Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  · have h0 : j≠0 := by omega
    have h1 : j≠1 := by omega
    have h2 : j≠2 := by omega
    simp [projectionMatrix,Matrix.mulVec_diagonal,small,Fin.sum_univ_three,
      Pi.single_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,h0,h1,h2]

/-- The same whole pole column supplies all three slow weights; the full inverse calculation is consumed rather than repeated. -/
theorem sourcePoleLiteral_allChannels (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    sourcePoleLiteralJet branch epsilon s n=
      ∑i : Fin 3,sourcePoleCoordinates branch epsilon s n ⟨i.val,by omega⟩ •
        sourceChargedChannel n (-Complex.I*(s:ℂ)) i := by
  have matrix:=sourceEnergyChannelMatrix_generated (physicalFrequencyMomentum s n)
  change sourceMatrix sourceEnergyChannelTerms (physicalFrequencyMomentum s n)=
    sourceChargedNativeFrameJet (physicalFrequencyMomentum s n)*
      projectionMatrix (fun j : Fin 289=>decide (j.val<3)) at matrix
  rw [sourcePoleLiteralJet,matrix,←Matrix.mulVec_mulVec,first_three]
  simp only [Matrix.mulVec_sum,Matrix.mulVec_smul,Matrix.mulVec_single_one]
  apply Finset.sum_congr rfl
  intro i _
  rw [sourceChannel_column]
  rfl

/-- No other channel is dropped: both remaining slow columns, the whole origin, both fast coordinates and the exact frame residual remain in this actual field. -/
def sourcePoleOtherField (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  sourcePoleOriginField branch epsilon s n+
  (epsilon:ℂ)^2 •
    (sourcePoleCoordinates branch epsilon s n 0 • sourceChargedChannel n (-Complex.I*(s:ℂ)) 0+
      sourcePoleCoordinates branch epsilon s n 1 • sourceChargedChannel n (-Complex.I*(s:ℂ)) 1+
      sourcePoleFastJet branch epsilon s n)+
  sourcePoleFrameResidual branch epsilon s n

theorem sourcePoleField_channelTwo (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) :
    sourceNativeFrequencyPolarization branch epsilon s n=
      sourcePoleCoordinates branch epsilon s n 2 •
        ((epsilon:ℂ)^2 • sourceChargedChannel n (-Complex.I*(s:ℂ)) 2)+
      sourcePoleOtherField branch epsilon s n := by
  have exactField:=sourceNativeFrequencyPolarization_firstReturn branch epsilon s n nonzero
  have solved:=sub_eq_iff_eq_add.mp (sub_eq_iff_eq_add.mp exactField)
  rw [solved,sourcePoleJetField_literal,sourcePoleLiteral_allChannels]
  simp only [Fin.sum_univ_three,sourcePoleOtherField,smul_add,
    show (⟨(0:Fin 3).val,by omega⟩:Fin 289)=(0:Fin 289) from rfl,
    show (⟨(1:Fin 3).val,by omega⟩:Fin 289)=(1:Fin 289) from rfl,
    show (⟨(2:Fin 3).val,by omega⟩:Fin 289)=(2:Fin 289) from rfl]
  module

private theorem part_add (V W : Fin 289→ℂ) :
    sourceChargedFieldPart (V+W)=sourceChargedFieldPart V+sourceChargedFieldPart W := by
  funext j
  simp only [sourceChargedFieldPart,sourceChargedCoefficient,Finset.sum_apply,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,Finset.sum_add_distrib]
private theorem part_smul (c : ℂ) (V : Fin 289→ℂ) :
    sourceChargedFieldPart (c • V)=c • sourceChargedFieldPart V := by
  funext j
  simp only [sourceChargedFieldPart,sourceChargedCoefficient,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

private theorem other_add (V W : Fin 289→ℂ) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceDirectionOtherEnergy (V+W) shift sideL edgeL sideR edgeR=
      sourceDirectionOtherEnergy V shift sideL edgeL sideR edgeR+
        sourceDirectionOtherEnergy W shift sideL edgeL sideR edgeR := by
  simp only [sourceDirectionOtherEnergy,sourceChargedFieldRemainder,part_add,
    sourceChargedCoefficient,Pi.add_apply,add_mul,Finset.sum_add_distrib,map_sub,map_add]
  ring
private theorem other_smul (c : ℂ) (V : Fin 289→ℂ) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceDirectionOtherEnergy (c • V) shift sideL edgeL sideR edgeR=
      c*sourceDirectionOtherEnergy V shift sideL edgeL sideR edgeR := by
  simp only [sourceDirectionOtherEnergy,sourceChargedFieldRemainder,part_smul,
    sourceChargedCoefficient,Pi.smul_apply,smul_eq_mul,map_sub,map_smul,
    mul_add,mul_sub,Finset.mul_sum,mul_assoc]

/-- The complete original other-energy read exposes its actual canonical-current term and its exact retained Dirac input/damping term, while retaining every remaining field component. -/
theorem sourcePoleOtherEnergy_Ward (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
      (sourceNativeFrequencyPolarization branch epsilon s n) (sourcePhotonEnergyShift epsilon n)
        sideL edgeL sideR edgeR=
      sourcePoleCoordinates branch epsilon s n 2*
        ((-sourceFrequency epsilon s:ℂ)*sourceFilteredChargeFormFactor
          (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR-
        ((5/3:ℂ)*(ActionNormalization.phaseMomentum:ℂ))*
          ∫k : Position,sourceEnergyRetainedWardIntegrand (sourcePhotonEnergyShift epsilon n)
            sideL edgeL sideR edgeR k)+
      (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
        (sourcePoleOtherField branch epsilon s n) (sourcePhotonEnergyShift epsilon n)
          sideL edgeL sideR edgeR := by
  rw [sourcePoleField_channelTwo branch epsilon s n nonzero,other_add,other_smul]
  have ward : (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
      ((epsilon:ℂ)^2 • sourceChargedChannel n (-Complex.I*(s:ℂ)) 2)
      (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR=
      (-sourceFrequency epsilon s:ℂ)*sourceFilteredChargeFormFactor
          (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR-
        ((5/3:ℂ)*(ActionNormalization.phaseMomentum:ℂ))*
          ∫k : Position,sourceEnergyRetainedWardIntegrand (sourcePhotonEnergyShift epsilon n)
            sideL edgeL sideR edgeR k := by
    rw [sourceChannel_physicalScale]
    simpa only [Complex.ofReal_neg] using sourceChannelTwo_otherWard (sourcePhotonEnergyShift epsilon n) (-sourceFrequency epsilon s)
      sideL edgeL sideR edgeR
  linear_combination sourcePoleCoordinates branch epsilon s n 2*ward

/-- The same full detector keeps the locked form factor as well as the newly exposed canonical-current and source Ward terms. -/
theorem sourcePoleEnergy_twoCurrents (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyReader (sourcePhotonEnergyShift epsilon n)
      sideL edgeL sideR edgeR (sourceNativeFrequencyPolarization branch epsilon s n)=
      -sourceDirectionPoleCoefficient branch epsilon s n 0*
        sourceFilteredLockedFormFactor (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR+
      sourcePoleCoordinates branch epsilon s n 2*
        ((-sourceFrequency epsilon s:ℂ)*sourceFilteredChargeFormFactor
          (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR-
        ((5/3:ℂ)*(ActionNormalization.phaseMomentum:ℂ))*
          ∫k : Position,sourceEnergyRetainedWardIntegrand (sourcePhotonEnergyShift epsilon n)
            sideL edgeL sideR edgeR k)+
      (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
        (sourcePoleOtherField branch epsilon s n) (sourcePhotonEnergyShift epsilon n)
          sideL edgeL sideR edgeR := by
  rw [sourceDirectionPole_energy branch epsilon s n nonzero,sourcePoleOtherEnergy_Ward branch epsilon s n nonzero]
  ring

/-- Both sheets use their actual beta emitter and physical omega residue, with no replacement of either quantum carrier. -/
theorem sourcePoleResidue_twoCurrents (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (sideL edgeL sideR edgeR : Fin 2) :
    ∀ᶠ e in scaleApproach,∀leg : SourcePhotonLeg,
      (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyReader (sourcePhotonEnergyShift e.val n)
        sideL edgeL sideR edgeR (sourcePhotonFrequencyResidue leg e.val (sourceSheet branch n unit e.val) n)=
      sourcePhotonEmitter leg branch e.val (sourceSheet branch n unit e.val) n*
        (-sourceDirectionPoleCoefficient branch e.val (sourceSheet branch n unit e.val) n 0*
          sourceFilteredLockedFormFactor (sourcePhotonEnergyShift e.val n) sideL edgeL sideR edgeR+
        sourcePoleCoordinates branch e.val (sourceSheet branch n unit e.val) n 2*
          ((-sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ)*sourceFilteredChargeFormFactor
            (sourcePhotonEnergyShift e.val n) sideL edgeL sideR edgeR-
          ((5/3:ℂ)*(ActionNormalization.phaseMomentum:ℂ))*
            ∫k : Position,sourceEnergyRetainedWardIntegrand (sourcePhotonEnergyShift e.val n)
              sideL edgeL sideR edgeR k)+
        (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
          (sourcePoleOtherField branch e.val (sourceSheet branch n unit e.val) n)
          (sourcePhotonEnergyShift e.val n) sideL edgeL sideR edgeR) := by
  filter_upwards [sourcePhotonFrequencyResidue_fluxFactor branch n unit] with e factor
  intro leg
  rw [factor leg,map_smul,smul_eq_mul]
  have read:=sourcePoleEnergy_twoCurrents branch e.val (sourceSheet branch n unit e.val) n
    e.property.1.ne' sideL edgeL sideR edgeR
  linear_combination sourcePhotonEmitter leg branch e.val (sourceSheet branch n unit e.val) n*read

end LowEnergy.PreparationPhysicalRemainderWardPoleReturn
