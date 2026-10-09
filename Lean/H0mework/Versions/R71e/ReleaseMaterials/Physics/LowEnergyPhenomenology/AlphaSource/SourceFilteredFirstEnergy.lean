import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFilteredFirstPhase

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFilteredFirstPhaseReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy Stage10
open FullQuantum FullSpace YangMills.FullPairing CanonicalGradedSpatialSource
open GaussHistoryHilbert
open FullQuantum.CoframeResponse FullQuantum.StateGreen FullQuantum.Triangular
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalFirstTemporalChargeReturn
open PreparationPhysicalActualPolarizationResponse PreparationPhysicalNormalizedFullField
open PreparationPhysicalChargedEnergyVariation PreparationPhysicalChargedEnergyPoleReturn
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedPacketVoltage
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalChargedVertexDomainReturn
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalVoltageEnergyIdentity
open PreparationPhysicalInternalChargePoleReturn PreparationPhysicalInternalOriginPoleAssembly
open PreparationPhysicalFiniteOriginCovariance PreparationPhysicalFiniteTransferOriginWard
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn
open PreparationPhysicalElectromagneticDirectionReturn PreparationPhysicalRemainderWardPoleReturn
open PreparationPhysicalNativePhotonScatteringSheetReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumChargedLongRangeRead
open PreparationVacuumPhysicalElectromagneticDirection
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumVoltageGaussGreen PreparationVacuumNonlinearFieldCurve
open PreparationVacuumMixedFieldReturn PreparationVacuumCausalPoleResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open Filter MeasureTheory
open scoped BigOperators Matrix InnerProductSpace Topology
local instance firstPhaseQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

/-- All four axes consume the complete original Hamiltonian jet, before taking any prepared restriction. -/
theorem sourceFirstAxisEnergy_matrix (p : PhysicalMomentum) (k : Fin 4) :
    affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState (fieldDirection (sourceEnergyAxisField 1 k))) p=
      Quantum.operatorMatrix (sourceFirstEnergyAction k) := by
  rw [sourceFirstGauge_state]
  simp only [affineMatrix,sourceHamiltonianJet_connection,if_true,Fin.succ_ne_zero,if_false,
    smul_zero,Finset.sum_const_zero,add_zero]
  have frame : sourceVoltageActualState.1=Stage9C.Material.SpinPair.actual.coframe 0 :=
    congrArg Prod.fst sourceState_event
  rw [frame]
  exact (sourceFirstEnergyAction_matrix k).symm

private theorem matrix_read (A : YangMills.FullPairing.Mother) :
    sourceEnergyMatrixRead (Quantum.operatorMatrix A)=operator A := by
  change operator (Quantum.operatorMatrix.symm (Quantum.operatorMatrix A))=operator A
  rw [AlgEquiv.symm_apply_apply]

theorem sourceFirstAxisEnergy_read (k : Fin 4) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedEnergyRead (fieldDirection (sourceEnergyAxisField 1 k)) shift sideL edgeL sideR edgeR=
      sourceChargedQuantumRead sideL edgeL sideR edgeR
        (((operator (sourceFirstEnergyAction k)).compLpL 2 volume).comp
          (PacketNoise.phaseShift shift).toContinuousLinearMap) := by
  rw [sourceChargedEnergyRead_fourier,sourceChargedQuantumRead_generated,ContinuousLinearMap.comp_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap]
  rw [←fourier.inner_map_map,GaugeGreen.constant_fourier,PacketNoise.phaseShift_fourier,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(operator (sourceFirstEnergyAction k)).coeFn_compLpL
    (PacketNoise.frequencyShift shift (fourier (sourceChargedFilteredPacket sideR edgeR))),
    PacketNoise.frequencyShift_ae shift (fourier (sourceChargedFilteredPacket sideR edgeR))] with frequency reader shifted
  rw [reader,shifted,sourceFirstAxisEnergy_matrix,matrix_read]

theorem sourceFirstAxisEnergy_temporal : sourceFirstEnergyAction 0=sourceFirstTemporalCharge := by
  apply Quantum.operatorMatrix.injective
  rw [sourceFirstEnergyAction_matrix]
  have paid:=sourceFirstTemporal_energy sourceVoltageActualState (sourceState_valid sourcePoint)
  unfold sourcePolarizationAxisEnergy sourcePolarizationAxisLower at paid
  have frame : sourceVoltageActualState.1=Stage9C.Material.SpinPair.actual.coframe 0 :=
    congrArg Prod.fst sourceState_event
  rw [frame] at paid
  exact paid

theorem sourceFirstTemporal_phaseRead (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*
      sourceChargedEnergyRead (fieldDirection (sourceEnergyAxisField 1 0)) shift sideL edgeL sideR edgeR=
      sourceInternalPhaseFormFactor shift sideL edgeL sideR edgeR := by
  rw [sourceFirstAxisEnergy_read,sourceFirstAxisEnergy_temporal,sourceInternalPhaseFormFactor]
  simp only [sourceChargedQuantumRead_generated,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,sourceFirstTemporal_filtered]

/-- Spatial and transverse insertions keep their entire full-mother actions between the actual shifted filtered legs. -/
def sourceFirstSpatialRead (shift : Position) (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  ∑j : Fin 3,fixedMomentum (physicalMomentum shift) 0 j.succ*
    sourceChargedQuantumRead sideL edgeL sideR edgeR
      (((operator (sourceFirstEnergyAction j.succ)).compLpL 2 volume).comp
        (PacketNoise.phaseShift shift).toContinuousLinearMap)

theorem sourceFirstChannel_phaseRead (shift : Position) (zeta : ℂ) (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyChannel shift zeta 1 sideL edgeL sideR edgeR=
      zeta*sourceInternalPhaseFormFactor shift sideL edgeL sideR edgeR+
      (ActionNormalization.phaseMomentum:ℂ)*sourceFirstSpatialRead shift sideL edgeL sideR edgeR := by
  rw [sourcePhysicalEnergyChannel_axes,Fin.sum_univ_succ]
  have temporal : fixedMomentum (physicalMomentum shift) zeta 0=zeta := rfl
  have spatial (j : Fin 3) : fixedMomentum (physicalMomentum shift) zeta j.succ=
      fixedMomentum (physicalMomentum shift) 0 j.succ := rfl
  simp only [temporal,spatial,sourceFirstAxisEnergy_read,sourceFirstSpatialRead]
  have paid:=sourceFirstTemporal_phaseRead shift sideL edgeL sideR edgeR
  rw [sourceFirstAxisEnergy_read] at paid
  linear_combination zeta*paid

theorem sourceFirstChannel_lockedZero (n : PhysicalMomentum) (zeta : ℂ) (mu : Fin 4) :
    sourceChargedCoefficient (sourceChargedChannel n zeta 1) mu=0 := by
  rw [sourceChannel_column]
  change sourceChargedNativeFrameJet (fixedMomentum n zeta) (lorentzSlot mu (sourceSpinSlot 2)) (1:Fin 289)=0
  exact (sourceDirectionLiteral_generated (fixedMomentum n zeta) mu (1:Fin 3)).trans
    (by fin_cases mu <;> rfl)

private theorem first_other (shift : Position) (zeta : ℂ) (sideL edgeL sideR edgeR : Fin 2) :
    sourceDirectionOtherEnergy (sourceChargedChannel (physicalMomentum shift) zeta 1) shift sideL edgeL sideR edgeR=
      sourcePhysicalEnergyChannel shift zeta 1 sideL edgeL sideR edgeR := by
  rw [sourcePhysicalEnergyChannel_generated]
  simp only [sourceDirectionOtherEnergy,sourceChargedFieldRemainder,sourceChargedFieldPart,
    sourceFirstChannel_lockedZero,zero_mul,zero_smul,Finset.sum_const_zero,sub_zero,zero_add]

theorem sourceFirstPhysical_phaseRead (epsilon s : ℝ) (n : PhysicalMomentum) (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
      ((epsilon:ℂ)^2 • sourceChargedChannel n (-Complex.I*(s:ℂ)) 1)
      (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR=
      (-Complex.I*(sourceFrequency epsilon s:ℂ))*
        sourceInternalPhaseFormFactor (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR+
      (ActionNormalization.phaseMomentum:ℂ)*sourceFirstSpatialRead
        (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR := by
  rw [sourceChannel_physicalScale,first_other,sourceFirstChannel_phaseRead]
  simp only [Complex.ofReal_neg,mul_neg,neg_mul]

private theorem part_add (V W : Fin 289→ℂ) :
    sourceChargedFieldPart (V+W)=sourceChargedFieldPart V+sourceChargedFieldPart W := by
  funext j
  simp only [sourceChargedFieldPart,sourceChargedCoefficient,Finset.sum_apply,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,Finset.sum_add_distrib]

private theorem part_smul (c : ℂ) (V : Fin 289→ℂ) : sourceChargedFieldPart (c • V)=c • sourceChargedFieldPart V := by
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

theorem sourceFirstTail_phaseRead (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
      ((epsilon:ℂ)^2 • (sourcePoleCoordinates branch epsilon s n 0 • sourceChargedChannel n (-Complex.I*(s:ℂ)) 0+
        sourcePoleCoordinates branch epsilon s n 1 • sourceChargedChannel n (-Complex.I*(s:ℂ)) 1+
        sourcePoleFastJet branch epsilon s n)+sourcePoleFrameResidual branch epsilon s n)
      (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR=
      (-Complex.I*(sourceFrequency epsilon s:ℂ))*sourcePoleCoordinates branch epsilon s n 1*
        sourceInternalPhaseFormFactor (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR+
      (ActionNormalization.phaseMomentum:ℂ)*sourcePoleCoordinates branch epsilon s n 1*
        sourceFirstSpatialRead (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR+
      (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
        ((epsilon:ℂ)^2 • (sourcePoleCoordinates branch epsilon s n 0 • sourceChargedChannel n (-Complex.I*(s:ℂ)) 0+
          sourcePoleFastJet branch epsilon s n)+sourcePoleFrameResidual branch epsilon s n)
        (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR := by
  have field :
      (epsilon:ℂ)^2 • (sourcePoleCoordinates branch epsilon s n 0 • sourceChargedChannel n (-Complex.I*(s:ℂ)) 0+
        sourcePoleCoordinates branch epsilon s n 1 • sourceChargedChannel n (-Complex.I*(s:ℂ)) 1+
        sourcePoleFastJet branch epsilon s n)+sourcePoleFrameResidual branch epsilon s n=
      sourcePoleCoordinates branch epsilon s n 1 • ((epsilon:ℂ)^2 • sourceChargedChannel n (-Complex.I*(s:ℂ)) 1)+
        ((epsilon:ℂ)^2 • (sourcePoleCoordinates branch epsilon s n 0 • sourceChargedChannel n (-Complex.I*(s:ℂ)) 0+
          sourcePoleFastJet branch epsilon s n)+sourcePoleFrameResidual branch epsilon s n) := by module
  rw [field,other_add,other_smul]
  have generated:=sourceFirstPhysical_phaseRead epsilon s n sideL edgeL sideR edgeR
  linear_combination sourcePoleCoordinates branch epsilon s n 1*generated

/-- The temporal first-pole contribution is evaluated on the actual filtered legs; all spatial and remaining-field actions survive. -/
theorem sourcePoleEnergy_firstPhaseWard (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyReader (sourcePhotonEnergyShift epsilon n)
      sideL edgeL sideR edgeR (sourceNativeFrequencyPolarization branch epsilon s n)=
      (sourceDirectionPoleCoefficient branch epsilon s n 0+2*sourceFiniteOriginAmplitude branch epsilon s n+(-Complex.I*(sourceFrequency epsilon s:ℂ))*sourcePoleCoordinates branch epsilon s n 1)*
        sourceInternalPhaseFormFactor (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR+
      (ActionNormalization.phaseMomentum:ℂ)*
        ((sourceFrequency epsilon s:ℂ)*sourcePoleCoordinates branch epsilon s n 2-sourceDirectionPoleCoefficient branch epsilon s n 0/2)*
        sourceChargedVoltageOverlap (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR-
      sourceDirectionPoleCoefficient branch epsilon s n 0*sourceInternalSpinFormFactor (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR-
      ((5/3:ℂ)*(ActionNormalization.phaseMomentum:ℂ))*sourcePoleCoordinates branch epsilon s n 2*
        (∫k : Position,sourceEnergyRetainedWardIntegrand (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR k)+
      (ActionNormalization.phaseMomentum:ℂ)*sourceFiniteOriginAmplitude branch epsilon s n*
        (∫k : Position,sourceOriginWardBalance (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR k)+
      (ActionNormalization.phaseMomentum:ℂ)*sourcePoleCoordinates branch epsilon s n 1*
        sourceFirstSpatialRead (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR+
      (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
        ((epsilon:ℂ)^2 •
          (sourcePoleCoordinates branch epsilon s n 0 • sourceChargedChannel n (-Complex.I*(s:ℂ)) 0+
            sourcePoleFastJet branch epsilon s n)+sourcePoleFrameResidual branch epsilon s n)
        (sourcePhotonEnergyShift epsilon n) sideL edgeL sideR edgeR := by
  rw [sourcePoleEnergy_originPhaseWard branch epsilon s n nonzero,sourceFirstTail_phaseRead]
  ring

/-- The original full signed current creates the same physical-frequency field, which the original independent filtered detector reads. -/
theorem sourceSignedEmitter_firstPhaseWard (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (q : PhysicalResponsePoint) (sL eL sR eR sideL edgeL sideR edgeR : Fin 2) (T : ℝ) :
    ∀ᶠ e in scaleApproach,
      (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyReader (sourcePhotonEnergyShift e.val n)
        sideL edgeL sideR edgeR
        (sourceInternalSignedField q sL eL sR eR T e.val (sourceSheet branch n unit e.val) n)=
        sourceInternalSignedEmitter branch q sL eL sR eR T e.val (sourceSheet branch n unit e.val) n*
          ((sourceDirectionPoleCoefficient branch e.val (sourceSheet branch n unit e.val) n 0+2*sourceFiniteOriginAmplitude branch e.val (sourceSheet branch n unit e.val) n+(-Complex.I*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ))*sourcePoleCoordinates branch e.val (sourceSheet branch n unit e.val) n 1)*
        sourceInternalPhaseFormFactor (sourcePhotonEnergyShift e.val n) sideL edgeL sideR edgeR+
      (ActionNormalization.phaseMomentum:ℂ)*
        ((sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ)*sourcePoleCoordinates branch e.val (sourceSheet branch n unit e.val) n 2-sourceDirectionPoleCoefficient branch e.val (sourceSheet branch n unit e.val) n 0/2)*
        sourceChargedVoltageOverlap (sourcePhotonEnergyShift e.val n) sideL edgeL sideR edgeR-
      sourceDirectionPoleCoefficient branch e.val (sourceSheet branch n unit e.val) n 0*sourceInternalSpinFormFactor (sourcePhotonEnergyShift e.val n) sideL edgeL sideR edgeR-
      ((5/3:ℂ)*(ActionNormalization.phaseMomentum:ℂ))*sourcePoleCoordinates branch e.val (sourceSheet branch n unit e.val) n 2*
        (∫k : Position,sourceEnergyRetainedWardIntegrand (sourcePhotonEnergyShift e.val n) sideL edgeL sideR edgeR k)+
      (ActionNormalization.phaseMomentum:ℂ)*sourceFiniteOriginAmplitude branch e.val (sourceSheet branch n unit e.val) n*
        (∫k : Position,sourceOriginWardBalance (sourcePhotonEnergyShift e.val n) sideL edgeL sideR edgeR k)+
      (ActionNormalization.phaseMomentum:ℂ)*sourcePoleCoordinates branch e.val (sourceSheet branch n unit e.val) n 1*
        sourceFirstSpatialRead (sourcePhotonEnergyShift e.val n) sideL edgeL sideR edgeR+
      (ActionNormalization.phaseMomentum:ℂ)*sourceDirectionOtherEnergy
        ((e.val:ℂ)^2 •
          (sourcePoleCoordinates branch e.val (sourceSheet branch n unit e.val) n 0 • sourceChargedChannel n (-Complex.I*((sourceSheet branch n unit e.val):ℂ)) 0+
            sourcePoleFastJet branch e.val (sourceSheet branch n unit e.val) n)+sourcePoleFrameResidual branch e.val (sourceSheet branch n unit e.val) n)
        (sourcePhotonEnergyShift e.val n) sideL edgeL sideR edgeR) := by
  filter_upwards [sourceInternalSignedField_generated branch n unit] with e factor
  rw [factor,map_smul,smul_eq_mul]
  have generated:=sourcePoleEnergy_firstPhaseWard branch e.val (sourceSheet branch n unit e.val) n
    e.property.1.ne' sideL edgeL sideR edgeR
  linear_combination sourceInternalSignedEmitter branch q sL eL sR eR T e.val
    (sourceSheet branch n unit e.val) n*generated

end LowEnergy.PreparationPhysicalFilteredFirstPhaseReturn
