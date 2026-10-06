import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationVacuumSymbol
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylSmooth

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEnergyTail
open PreparationActualFactor PreparationVacuumFactor PreparationVacuumWeyl
open PreparationPhaseSource PreparationScalarCoordinates
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open GaussNativeEnergy GaussNativeForm GaussHistoryHilbert GaussCoreDifferential
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open SourceQuantumFockGauge CanonicalPreparationCreation
open scoped BigOperators Matrix

abbrev Phase := FlatConfiguration × PhysicalMomentum

def originalLeadingEnergy (zp : Phase) : ℝ :=
  sourceTheta zp.1 (normalizedMomentum zp.2)*sourceChi (2*‖zp.2‖)*
    timelikePrincipal (nativePhase zp).1 (nativePhase zp).2
      (C (nativePhase zp).1 (nativePhase zp).2) 0

theorem sourceTheta_zero_position {z u : FlatConfiguration}
    (outside : z∉thetaPositionClosed) : sourceTheta z u=0 := by
  have square:=sourceThetaRoot_square (z,u)
  rw [sourceThetaRoot_split,positionRoot_zero_outside outside,zero_mul] at square
  simpa using square.symm

theorem sourceTheta_zero_direction {z u : FlatConfiguration}
    (outside : u∉thetaDirectionClosed) : sourceTheta z u=0 := by
  have square:=sourceThetaRoot_square (z,u)
  rw [sourceThetaRoot_split,directionRoot_zero_outside outside,mul_zero] at square
  simpa using square.symm

theorem originalLeadingEnergy_b1_square (zp : Phase) : originalLeadingEnergy zp=b1 zp^2 := by
  by_cases momentumZero : zp.2=0
  · have low : ‖zp.2‖≤1/2 := by rw [momentumZero]; norm_num
    rw [b1_zero_low zp low]
    simp [originalLeadingEnergy,momentumZero,sourceChi]
  · by_cases position : zp.1∈thetaPositionClosed
    · by_cases direction : normalizedMomentum zp.2∈thetaDirectionClosed
      · have cone:=source_support_positiveCone zp.1 zp.2 position direction momentumZero
        rw [originalLeadingEnergy,principal_clock_energy cone]
        exact (b1_square zp cone).symm
      · have theta:=sourceTheta_zero_direction (z:=zp.1) direction
        have zero : b1 zp=0 := by
          simp only [b1,factorWeight,sourceThetaRoot_split,directionRoot_zero_outside direction,
            mul_zero,zero_mul]
        simp only [originalLeadingEnergy,theta,zero_mul,zero]
        norm_num
    · have theta:=sourceTheta_zero_position (u:=normalizedMomentum zp.2) position
      have zero : b1 zp=0 := by
        simp only [b1,factorWeight,sourceThetaRoot_split,positionRoot_zero_outside position,zero_mul]
      simp only [originalLeadingEnergy,theta,zero_mul,zero]
      norm_num

def originalFirstSourceScalar (z : SourceCoordinateSlice) (p : Cotangent) :
    FockFiber →L[ℂ] FockFiber :=
  ((1/sourceTime 0 : ℝ) : ℂ) • (scalarConnectionSymbol z p+coframeConnectionSymbol z p)

def originalFirstSourceGaugeTrace (z : SourceCoordinateSlice) (p : Cotangent) :
    FockFiber →L[ℂ] FockFiber :=
  (-Complex.I) • ∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3,
    ((sourceSigma*volume z*inverseSpatial z i j : ℝ) : ℂ) •
      ((electricMomentum z p i a : ℂ) • connection (gaugeDirection j a) z+
        (electricMomentum z p j a : ℂ) • connection (gaugeDirection i a) z)

theorem originalFirstSourceGaugeTrace_readback (z : SourceCoordinateSlice) (p : Cotangent) :
    originalFirstSourceGaugeTrace z p=
      ((2*sourceTime 0 : ℝ) : ℂ) • gaugeConnectionSymbol z p := by
  unfold originalFirstSourceGaugeTrace gaugeConnectionSymbol
  simp only [Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold gaugeWeight
  have nonzero : (sourceTime 0 : ℂ)≠0 := by exact_mod_cast source_time_nonzero
  push_cast
  field_simp [nonzero]

-- Engine(1)'s literal energy row has source slots0,4,5,6 with weights
-- c,1/(2c),1/(2c),1/(2c). The trace retains the original three spatial slots.
def originalFirstRecursionEnergy (n : ℝ) (z : SourceCoordinateSlice) (p : Cotangent) :
    FockFiber →L[ℂ] FockFiber :=
  (n : ℂ) • originalFirstSourceScalar z p+
    ((1/(2*n) : ℝ) : ℂ) • originalFirstSourceGaugeTrace z p

theorem originalFirstRecursionEnergy_readback (n : ℝ) (z : SourceCoordinateSlice) (p : Cotangent) :
    originalFirstRecursionEnergy n z p=zeroShiftCurrentSymbol n z p := by
  rw [originalFirstRecursionEnergy,originalFirstSourceGaugeTrace_readback]
  unfold originalFirstSourceScalar zeroShiftCurrentSymbol
  simp only [smul_smul]
  have scalar : (n : ℂ)*((1/sourceTime 0 : ℝ) : ℂ)=((n/sourceTime 0 : ℝ) : ℂ) := by
    push_cast
    simp only [div_eq_mul_inv,one_mul]
  have gauge : ((1/(2*n) : ℝ) : ℂ)*((2*sourceTime 0 : ℝ) : ℂ)=
      ((sourceTime 0/n : ℝ) : ℂ) := by
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
    norm_num
    ring
  rw [scalar,gauge]

def originalFirstEnergy (zp : Phase) : FockFiber →L[ℂ] FockFiber :=
  originalFirstRecursionEnergy (C (nativePhase zp).1 (nativePhase zp).2)
    (nativePhase zp).1 (nativePhase zp).2

theorem originalFirstEnergy_native (zp : Phase) : originalFirstEnergy zp=nativePrincipalCurrent zp :=
  originalFirstRecursionEnergy_readback _ _ _

theorem originalFirstEnergy_vacuum (zp : Phase) : originalFirstEnergy zp vacuumFiber=0 := by
  rw [originalFirstEnergy_native]
  exact nativePrincipalCurrent_vacuum zp

end LowEnergy.PreparationVacuumEnergyTail
