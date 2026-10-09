import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFilteredLockedCurrent

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFilteredLockedChargeReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy Stage10
open FullQuantum FullSpace FullQuantum.PerturbedGreen YangMills.FullPairing
open FullQuantum.CoframeResponse FullQuantum.StateGreen FullQuantum.Triangular
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation PreparationVacuumVoltageGaussGreen
open PreparationVacuumActualFieldQuantization
open PreparationVacuumPhysicalElectromagneticDirection PreparationVacuumActionFieldLift PreparationVacuumSourceFieldFamily
open DiracExteriorMatterAction DiracCliffordRepresentation Stage10.CanonicalMatter GaussHistoryHilbert
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalVoltageEnergyIdentity
open PreparationVacuumPhysicalQuantumLockedCharge
open MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators
local instance : DecidableEq Quantum.Index:=Classical.decEq _

def sourceLockedSpatialTorque (j : Fin 3) : FiberOperators :=
  SpatialWeak.spatial 0 j*sourceLockedFiberCharge-sourceLockedFiberCharge*SpatialWeak.spatial 0 j

/-- The retained correction contains the original zero-order torque and all three physical momentum terms. -/
theorem sourceLockedDiracTorque_affine (k : Position) :
    sourceLockedDiracTorque (physicalMomentum k)=sourceLockedDiracTorque 0-
      ∑j : Fin 3,(physicalMomentum k j:ℂ) • sourceLockedSpatialTorque j := by
  have affine : sourceLockedDiracMatrix (physicalMomentum k)=sourceLockedDiracMatrix 0-
      ∑j : Fin 3,(physicalMomentum k j:ℂ) • SpatialWeak.spatial 0 j:=SpatialWeak.symbol_affine 0 0 1 k
  rw [sourceLockedDiracTorque,affine,sourceLockedDiracTorque]
  simp only [sourceLockedSpatialTorque,sub_mul,mul_sub,Finset.sum_mul,Finset.mul_sum,
    smul_mul_assoc,mul_smul_comm,smul_sub,Finset.sum_sub_distrib]
  abel

/-- The two physical momenta keep both original Dirac operators in the Ward insertion. -/
def sourceLockedTransferWard (left right : Fin 3→ℝ) : FiberOperators :=
  sourceLockedDiracMatrix left*sourceLockedFiberCharge-sourceLockedFiberCharge*sourceLockedDiracMatrix right

theorem sourceLockedGreenTransfer_generated (left right : Fin 3→ℝ) :
    sourceLockedFiberCharge*Retarded.diracValue 0 right 0 1-
      Retarded.diracValue 0 left 0 1*sourceLockedFiberCharge=
      Retarded.diracValue 0 left 0 1*sourceLockedTransferWard left right*Retarded.diracValue 0 right 0 1 := by
  have inverseL:=Retarded.diracValue_two_sided 0 left 0 1 (by norm_num)
  have inverseR:=Retarded.diracValue_two_sided 0 right 0 1 (by norm_num)
  change _*_=1 ∧ Retarded.diracValue 0 left 0 1*sourceLockedDiracMatrix left=1 at inverseL
  change sourceLockedDiracMatrix right*Retarded.diracValue 0 right 0 1=1 ∧ _*_=1 at inverseR
  rw [sourceLockedTransferWard,mul_sub,sub_mul]
  calc
    _=(Retarded.diracValue 0 left 0 1*sourceLockedDiracMatrix left)*sourceLockedFiberCharge*
        Retarded.diracValue 0 right 0 1-
      Retarded.diracValue 0 left 0 1*sourceLockedFiberCharge*
        (sourceLockedDiracMatrix right*Retarded.diracValue 0 right 0 1) := by
      rw [inverseL.2,inverseR.1,one_mul,mul_one]
    _=_ := by noncomm_ring

private theorem charge_shift (shift : Position) (field : FullMatterL2) :
    sourceLockedSpatialCharge (PacketNoise.phaseShift shift field)=
      PacketNoise.phaseShift shift (sourceLockedSpatialCharge field) := by
  apply Lp.ext
  filter_upwards [sourceLockedFiberCharge.coeFn_compLpL (PacketNoise.phaseShift shift field),
    PacketNoise.phaseShift_position shift field,
    PacketNoise.phaseShift_position shift (sourceLockedSpatialCharge field),
    sourceLockedFiberCharge.coeFn_compLpL field] with x reader shifted shiftedQ original
  change sourceLockedFiberCharge.compLpL 2 volume (PacketNoise.phaseShift shift field) x=_
  rw [reader,shifted,map_smul,shiftedQ]
  change _=_ • sourceLockedFiberCharge.compLpL 2 volume field x
  rw [original]

/-- The physical locked current, inside both actual source preparations, carries momentum transfer. -/
def sourceFilteredLockedFormFactor (shift : Position) (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  (ActionNormalization.phaseMomentum:ℂ)*sourceChargedQuantumRead sideL edgeL sideR edgeR
    (sourceLockedSpatialCharge.comp (PacketNoise.phaseShift shift).toContinuousLinearMap)

theorem sourceFilteredLockedFormFactor_generated (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceFilteredLockedFormFactor shift sideL edgeL sideR edgeR=
      -(ActionNormalization.phaseMomentum:ℂ)*(sourceChargedPolarity edgeR:ℂ)*
        sourceChargedVoltageOverlap shift sideL edgeL sideR edgeR+
      (ActionNormalization.phaseMomentum:ℂ)*inner ℂ (sourceChargedFilteredPacket sideL edgeL)
        (PacketNoise.phaseShift shift (sourceFilteredLockedCorrection sideR edgeR)) := by
  rw [sourceFilteredLockedFormFactor,sourceChargedQuantumRead_generated,ContinuousLinearMap.comp_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap]
  rw [charge_shift,sourceFilteredLockedAction,map_add,map_smul,inner_add_right,inner_smul_right,
    sourceChargedVoltageOverlap]
  ring

theorem sourceFilteredLockedFormFactor_fourier (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceFilteredLockedFormFactor shift sideL edgeL sideR edgeR=
      -(ActionNormalization.phaseMomentum:ℂ)*(sourceChargedPolarity edgeR:ℂ)*
        sourceChargedVoltageOverlap shift sideL edgeL sideR edgeR+
      (ActionNormalization.phaseMomentum:ℂ)*(∫k : Position,inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) k)
        (Retarded.diracValue 0 (physicalMomentum (k-shift)) 0 1
          (sourceLockedDiracTorque (physicalMomentum (k-shift))
            (fourier (sourceChargedFilteredPacket sideR edgeR) (k-shift))))) := by
  rw [sourceFilteredLockedFormFactor_generated]
  congr 1
  congr 1
  rw [←fourier.inner_map_map,L2.inner_def,PacketNoise.phaseShift_fourier]
  apply integral_congr_ae
  have shifted:=(measurePreserving_sub_right volume shift).quasiMeasurePreserving.ae
    (sourceFilteredLockedCorrection_fourier sideR edgeR)
  filter_upwards [PacketNoise.frequencyShift_ae shift (fourier (sourceFilteredLockedCorrection sideR edgeR)),shifted]
    with k read correction
  rw [read,correction]

theorem sourceFilteredLockedFormFactor_continuous (sideL edgeL sideR edgeR : Fin 2) :
    Continuous (fun shift=>sourceFilteredLockedFormFactor shift sideL edgeL sideR edgeR) := by
  simp only [sourceFilteredLockedFormFactor_generated,sourceChargedVoltageOverlap]
  exact ((continuous_const.inner (PacketNoise.phaseShift_continuous _)).const_mul _).add
    ((continuous_const.inner (PacketNoise.phaseShift_continuous _)).const_mul _)

/-- Zero transfer returns the actual torque expectation as well as the source rest polarity. -/
theorem sourceFilteredLockedFormFactor_soft (side edge : Fin 2) :
    Tendsto (fun shift=>sourceFilteredLockedFormFactor shift side edge side edge)
      (𝓝 (0:Position)) (𝓝 (-(ActionNormalization.phaseMomentum:ℂ)*(sourceChargedPolarity edge:ℂ)+
        (ActionNormalization.phaseMomentum:ℂ)*inner ℂ (sourceChargedFilteredPacket side edge)
          (sourceFilteredLockedCorrection side edge))) := by
  have generated:=(sourceFilteredLockedFormFactor_continuous side edge side edge).tendsto (0:Position)
  simpa only [sourceFilteredLockedFormFactor_generated,sourceChargedVoltageOverlap_unit,
    PacketNoise.phaseShift_zero,mul_one] using generated

/-- The original locked field, including its spin connection, has this actual normalized energy insertion. -/
theorem sourceLockedEnergyCoefficient (k : Fin 4) :
    sourceEnergyMatrixRead (sourceHamiltonianJetMatrix sourceVoltageActualState
      (fieldDirection (sourceLockedField 0 2)) k)=if k=0 then -sourceLockedFiberCharge else 0 := by
  rw [sourceLockedField_direction,sourceHamiltonianJet_connection]
  by_cases zero : k=0
  · simp only [zero,ite_true,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ]
    rw [←principalMatrix_coefficient,←mul_assoc,
      Ring.inverse_mul_cancel _ (principalMatrix_regular _
        (PreparationVacuumNonlinearFieldCurve.sourceState_valid sourcePoint).2),one_mul]
    change operator (Quantum.operatorMatrix.symm ((-Complex.I) • Quantum.operatorMatrix (sourceLockedAction 2)))=
      -operator (sourceLockedCurrentDirection 0 2)
    rw [map_smul,Quantum.operatorMatrix.symm_apply_apply,operator_smul]
    have temporal : sourceLockedCurrentDirection 0 2=Complex.I • sourceLockedAction 2 := by
      apply LinearMap.ext
      intro matter
      simp only [sourceLockedCurrentDirection,sourceLockedCurrent,LinearMap.comp_apply,LinearMap.smul_apply,
        map_smul,diracGamma,Matrix.cons_val_zero,phase_inverse_source]
    rw [temporal,operator_smul]
    module
  · simp only [if_neg zero,map_zero]

/-- The same full 289-direction energy reader consumes the actual locked charge, including its generated torque. -/
theorem sourceLockedEnergy_current (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourceChargedEnergyRead
      (fieldDirection (sourceLockedField 0 2)) shift sideL edgeL sideR edgeR=
      -sourceFilteredLockedFormFactor shift sideL edgeL sideR edgeR := by
  have current : sourceChargedQuantumRead sideL edgeL sideR edgeR
      (sourceLockedSpatialCharge.comp (PacketNoise.phaseShift shift).toContinuousLinearMap)=
      ∫k : Position,inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) k)
        (sourceLockedFiberCharge (fourier (sourceChargedFilteredPacket sideR edgeR) (k-shift))) := by
    rw [sourceChargedQuantumRead_generated,ContinuousLinearMap.comp_apply]
    simp only [LinearIsometry.coe_toContinuousLinearMap]
    rw [←fourier.inner_map_map,L2.inner_def]
    have mapped:=GaugeGreen.constant_fourier sourceLockedFiberCharge
      (PacketNoise.phaseShift shift (sourceChargedFilteredPacket sideR edgeR))
    change fourier (sourceLockedSpatialCharge (PacketNoise.phaseShift shift (sourceChargedFilteredPacket sideR edgeR)))=_ at mapped
    rw [mapped,PacketNoise.phaseShift_fourier]
    apply integral_congr_ae
    filter_upwards [sourceLockedFiberCharge.coeFn_compLpL
      (PacketNoise.frequencyShift shift (fourier (sourceChargedFilteredPacket sideR edgeR))),
      PacketNoise.frequencyShift_ae shift (fourier (sourceChargedFilteredPacket sideR edgeR))] with k reader shifted
    rw [reader,shifted]
  rw [sourceFilteredLockedFormFactor,current,sourceChargedEnergyRead_fourier]
  simp only [affineMatrix,map_add,map_sum,map_smul,sourceLockedEnergyCoefficient,
    ite_true,Fin.succ_ne_zero,ite_false,
    _root_.smul_zero (M:=ℂ) (A:=FiberOperators),Finset.sum_const_zero,add_zero,neg_apply,inner_neg_right]
  rw [integral_neg]
  ring

end LowEnergy.PreparationPhysicalFilteredLockedChargeReturn
