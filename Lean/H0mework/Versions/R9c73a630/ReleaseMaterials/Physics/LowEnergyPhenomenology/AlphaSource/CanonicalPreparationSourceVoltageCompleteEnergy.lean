import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceVoltageProjectedEnergy

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalVoltageEnergyIdentity
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage9C.Material.SpinPair FullQuantum FullSpace
open PreparationPhysicalVoltageNoether PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalVoltageCompleteReturn PreparationPhysicalChargedEnergyPoleReturn
open PreparationPhysicalChargedPacketQuantumReturn
open PreparationVacuumStaticVoltageSource PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumNoetherOrdinaryWard PreparationVacuumMatterEulerFeedback
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCharacteristic
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedFieldReturn
open CanonicalGradedSpatialSource
open scoped Matrix BigOperators InnerProductSpace Topology

private theorem voltage_basis : fieldDirection (fieldUnit 20)=sourceVoltageStateDirection 1 0 := by
  have same : fieldUnit 20=sourceVoltageCoordinates 1 0 0:=by
    ext j
    simp [fieldUnit,sourceVoltageCoordinates]
  rw [same,sourceVoltageField_direction]

private theorem scalar_basis : fieldDirection (fieldUnit 8)=sourceVoltageStateDirection 0 1 := by
  have same : fieldUnit 8=sourceVoltageCoordinates 0 1 0:=by
    ext j
    simp [fieldUnit,sourceVoltageCoordinates]
  rw [same,sourceVoltageField_direction]

private theorem auxiliary_basis (axis : Fin 3) :
    fieldDirection (fieldUnit ⟨264+12*axis.val,by omega⟩)=sourceVoltageStateDirection 0 0 := by
  have same : fieldUnit ⟨264+12*axis.val,by omega⟩=sourceVoltageCoordinates 0 0 (Pi.single axis 1):=by
    fin_cases axis <;> ext j <;> norm_num [fieldUnit,sourceVoltageCoordinates,Pi.single_apply,Fin.ext_iff]
  rw [same,sourceVoltageField_direction]

private theorem read_single (shift : Position) (sideL edgeL sideR edgeR : Fin 2) (j : Fin 289) (a : ℂ) :
    sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR (Pi.single j a)=
      a*sourceChargedEnergyRead (fieldDirection (fieldUnit j)) shift sideL edgeL sideR edgeR := by
  rw [sourcePhysicalEnergyReader_original,sourceFullEnergyRead_generated]
  simp [Pi.single_apply]

/-- Constitutive B remains in the original field; its actual energy derivative vanishes, while the voltage acts on the retained packet. -/
theorem sourceVoltageSpatialVector_energy (spatial : Fin 3→ℂ) (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR (sourceVoltageSpatialVector spatial)=
      sourceChargedVoltageOverlap shift sideL edgeL sideR edgeR := by
  have b0 : fieldDirection (fieldUnit 264)=sourceVoltageStateDirection 0 0:=auxiliary_basis 0
  have b1 : fieldDirection (fieldUnit 276)=sourceVoltageStateDirection 0 0:=auxiliary_basis 1
  have b2 : fieldDirection (fieldUnit 288)=sourceVoltageStateDirection 0 0:=auxiliary_basis 2
  simp only [sourceVoltageSpatialVector,map_add,read_single,voltage_basis,b0,b1,b2,
    sourceChargedVoltageEnergy_actual,Complex.ofReal_one,Complex.ofReal_zero,one_mul,mul_zero,zero_mul,add_zero]

/-- The time-ramp scalar term is present in the field and disappears only after the original left-source energy read. -/
theorem sourceVoltageTemporalVector_energy (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR sourceVoltageTemporalVector=0 := by
  rw [sourceVoltageTemporalVector,read_single,scalar_basis,sourceChargedVoltageEnergy_actual]
  simp

theorem sourceVoltageLaplaceRamp_energy (spatial : Fin 3→ℂ) (z : ℂ) (shift : Position)
    (sideL edgeL sideR edgeR : Fin 2) :
    sourceFullEnergyRead (sourceVoltageLaplaceRamp spatial z) shift sideL edgeL sideR edgeR=
      z⁻¹*sourceChargedVoltageOverlap shift sideL edgeL sideR edgeR := by
  rw [←sourcePhysicalEnergyReader_original,sourceVoltageLaplaceRamp,map_add,map_smul,map_smul,
    sourceVoltageSpatialVector_energy,sourceVoltageTemporalVector_energy]
  simp only [smul_eq_mul,mul_zero,add_zero]

theorem sourceChargedVoltageOverlap_unit (side edge : Fin 2) : sourceChargedVoltageOverlap 0 side edge side edge=1 := by
  rw [sourceChargedVoltageOverlap,PacketNoise.phaseShift_zero,inner_self_eq_norm_sq_to_K,sourceChargedFilteredPacket_unit]
  norm_num

/-- The actual complete response exposes the original Gauss inverse price in its same-Phi energy, with null and all residual fields retained. -/
theorem sourcePreparedVoltageEnergy_gauss (q : PhysicalResponsePoint) (force : Field289) (shift : Position)
    (z : physicalSpectralDomain (physicalMomentum shift)) (nonzero : z.val≠0)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) (sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR
      (deriv (actionFieldCurve q force (physicalMomentum shift) z T) 0)=
      (modeForcing q force true (physicalMomentum shift) z.val T 20 /
        (2*(lapse:ℂ)*(spatialSquare (physicalMomentum shift):ℂ)))*sourceChargedVoltageOverlap shift sideL edgeL sideR edgeR-
      sourcePreparedVoltageAmplitude q force (physicalMomentum shift) z.val T*
        sourceFullEnergyRead
          (originalChange (fullMomentum (physicalSpatial (physicalMomentum shift)) z.val)*ᵥ(nullProjection*ᵥ
            (originalInverse (fullMomentum (physicalSpatial (physicalMomentum shift)) z.val)*ᵥ
              sourceVoltageLaplaceRamp (physicalSpatial (physicalMomentum shift)) z.val))) shift sideL edgeL sideR edgeR+
      sourceFullEnergyRead
        (PreparationVacuumOriginalGreenFeedback.sourceField
          ⟨fullMomentum (physicalSpatial (physicalMomentum shift)) z.val,z.property⟩
          (sourcePreparedVoltageRemainder q force (physicalMomentum shift) z.val T)) shift sideL edgeL sideR edgeR := by
  rw [sourcePreparedVoltage_energy_return q force shift z nonzero hz hw T sideL edgeL sideR edgeR,
    sourceVoltageLaplaceRamp_energy]
  have scale : sourcePreparedVoltageAmplitude q force (physicalMomentum shift) z.val T*z.val⁻¹=
      modeForcing q force true (physicalMomentum shift) z.val T 20 /
        (2*(lapse:ℂ)*(spatialSquare (physicalMomentum shift):ℂ)) := by
    rw [sourcePreparedVoltageAmplitude]
    field_simp [nonzero]
  rw [mul_sub,←mul_assoc,scale]

end LowEnergy.PreparationPhysicalVoltageEnergyIdentity
