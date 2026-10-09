import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePoleEnergySheet

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalPoleChargeMatrix
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalCurvatureSheetLimit PreparationPhysicalNormalizedFullField
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePolarizationEmitter
open PreparationPhysicalActualNoetherVertexReturn PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalPhaseGaugeRealization
open PreparationVacuumPhysicalFeedback PreparationVacuumSourceFieldFamily GaussHistoryHilbert
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumNativeSlowCoupling PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor
open PreparationPhysicalGaugeMomentumCoupling PreparationPhysicalActualGaussChargeCurrent
open CanonicalGradedSpatialSource
open Filter Set
open scoped Matrix BigOperators Topology InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _

/-- The actual source sheet fixes this complete four-state coefficient; no charge label supplies it. -/
def sourcePolePreparedCoefficient (n : PhysicalMomentum) (i : ActualPreparedIndex) : ℂ :=
  (sourceSpeed 1:ℂ)+(Real.sqrt 30:ℂ)/5*(if i.1=i.2 then 1 else -1)*(n 2:ℂ)

theorem sourcePoleEnergyMatrix_physical (epsilon : ℝ) (precision : 0<epsilon) (p n : PhysicalMomentum) :
    sourcePoleEnergyMatrix epsilon precision p (physicalFrequencyMomentum (sourceSpeed 1) n)=
      Matrix.diagonal (sourcePolePreparedCoefficient n) := by
  rw [sourcePoleEnergyMatrix_generated]
  congr 1
  funext i
  change Complex.I*(-Complex.I*(sourceSpeed 1:ℂ))-
    (Complex.I*(Real.sqrt 30:ℂ)/5)*(if i.1=i.2 then 1 else -1)*(Complex.I*(n 2:ℂ))=_
  unfold sourcePolePreparedCoefficient
  have square : Complex.I*Complex.I=(-1:ℂ):=Complex.I_mul_I
  calc
    _= -(Complex.I*Complex.I)*(sourceSpeed 1:ℂ)-
      (Complex.I*Complex.I)*(Real.sqrt 30:ℂ)/5*(if i.1=i.2 then 1 else -1)*(n 2:ℂ) := by ring
    _=_ := by rw [square];ring

/-- The complete matrix difference keeps the neutral directions and all actual external states. -/
theorem sourcePoleCharge_difference (epsilon : ℝ) (precision : 0<epsilon) (p n : PhysicalMomentum) :
    sourcePoleEnergyMatrix epsilon precision p (physicalFrequencyMomentum (sourceSpeed 1) n)-
      (sourceSpeed 1:ℂ) • sourcePreparedChargeUnitMatrix=
      Matrix.diagonal (fun i=>sourcePolePreparedCoefficient n i-
        (sourceSpeed 1:ℂ)*(sourceActualPhaseCharge i.2:ℂ)) := by
  rw [sourcePoleEnergyMatrix_physical]
  ext i j
  simp only [Matrix.sub_apply,sourcePreparedChargeUnitMatrix,Matrix.smul_apply,Matrix.diagonal_apply,smul_eq_mul]
  split_ifs <;> simp

/-- The comparison consumes the original absolute hQ vertex on the actual four preparations. -/
theorem sourcePoleAbsoluteCharge_difference (q : PhysicalResponsePoint) (p n : PhysicalMomentum) :
    sourcePoleEnergyMatrix q.epsilon q.precision p (physicalFrequencyMomentum (sourceSpeed 1) n)-
      ((sourceSpeed 1:ℂ)/(Stage10.ActionNormalization.phaseMomentum:ℂ)) •
        sourcePreparedCurrentMatrix q sourceAbsoluteCharge=
      Matrix.diagonal (fun i=>sourcePolePreparedCoefficient n i-
        (sourceSpeed 1:ℂ)*(sourceActualPhaseCharge i.2:ℂ)) := by
  rw [sourcePreparedChargeUnit_generated,smul_smul,
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne')]
  exact sourcePoleCharge_difference q.epsilon q.precision p n

private theorem energyJet_entry (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (v : Fin 4→ℂ) (a : ℂ) (i j : ActualPreparedIndex) :
    sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
      (sourceChargedNativeFrameJet v*ᵥPi.single (2:Fin 289) a)=
      a*sourcePoleEnergyMatrix epsilon precision p v i j := by
  simp only [sourceFullEnergyRead,sourcePoleEnergyMatrix,sourceLiteralEnergyCoefficient,sourceChargedEnergyRead_entry]
  rw [sourceLiteralEnergyWeight_generated]
  simp only [sourceFullEnergyMatrix,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.mulVec_single,op_smul_eq_smul,Pi.smul_apply,Matrix.col_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have column : (⟨(2:Fin 3).val,by decide⟩:Fin 289)=(2:Fin 289) := by decide
  rw [column]
  ring

/-- The original complete-field first return now reads the generated all16 coefficient, preserving its actual origin separately. -/
theorem sourcePolePreparedEnergy_limit (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (i j : ActualPreparedIndex) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet 1 n unit e.val:ℂ))*
      (sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourceNativeFrequencyPolarization 1 e.val (sourceSheet 1 n unit e.val) n)-
       sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourcePoleOriginField 1 e.val (sourceSheet 1 n unit e.val) n))/(e.val:ℂ)^2)
      scaleApproach (𝓝 ((softCoefficient 1:ℂ)*
        (Matrix.diagonal (sourcePolePreparedCoefficient n)) i j)) := by
  have original:=sourcePoleEnergy_first_limit epsilon precision p i j 1 n unit
  change Tendsto _ _ (𝓝 (sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
    (sourceChargedNativeFrameJet (physicalFrequencyMomentum (sourceSpeed 1) n)*ᵥ
      Pi.single (2:Fin 289) (softCoefficient 1:ℂ)))) at original
  simpa only [energyJet_entry,sourcePoleEnergyMatrix_physical] using original

private theorem energyRead_smul (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (i j : ActualPreparedIndex) (z : ℂ) (V : Fin 289→ℂ) :
    sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2 (z • V)=
      z*sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2 V := by
  simp only [sourceFullEnergyRead,sourceChargedEnergyRead_entry,sourceFullEnergyMatrix,
    Matrix.sum_apply,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The same physical current emitter consumes the full energy first return, retaining its actual origin contribution explicitly. -/
theorem sourcePoleCurrent_energy (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (pL pR : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum) (i j : ActualPreparedIndex) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet 1 n unit e.val:ℂ))*
      (sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourcePhaseGaugePhotonField q sL eL sR eR pL pR lambda T e.val (sourceSheet 1 n unit e.val) n)-
       sourcePhotonLeftReader 1 e.val (sourceSheet 1 n unit e.val) n
         (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T)*
       sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourcePoleOriginField 1 e.val (sourceSheet 1 n unit e.val) n)))
      scaleApproach (𝓝 (sourceCurvatureEmitterInput
        (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T) (residueIndex 1)*
        ((softCoefficient 1:ℂ)*(Matrix.diagonal (sourcePolePreparedCoefficient n)) i j))) := by
  have left:=sourcePhotonLeftReader_sheet 1 n unit (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T)
  have right:=sourcePolePreparedEnergy_limit epsilon precision p i j n unit
  have generated:=left.mul right
  apply generated.congr'
  filter_upwards [sourcePhaseGaugePhotonField_factor q sL eL sR eR pL pR lambda T 1 n unit] with e factor
  rw [factor,energyRead_smul]
  have nonzero : (e.val:ℂ)≠0:=Complex.ofReal_ne_zero.mpr e.property.1.ne'
  field_simp [nonzero]

end LowEnergy.PreparationPhysicalPoleChargeMatrix
