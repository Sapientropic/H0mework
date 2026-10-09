import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCauchyPoleJet

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCauchyDynamic
open SaturationMonoid.PhysicsCore
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumMixedFieldReturn
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn
open PreparationPhysicalNativePolarizationEmitter PreparationPhysicalNormalizedFullField
open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor PreparationVacuumWholeOrigin
open PreparationPhysicalCurvatureSheetLimit CanonicalGradedSpatialSource Filter
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceNativeFrequencyPolarization sourceChargedNativeFrameResidual
  sourcePoleCoordinates

private theorem pole_coordinate_one (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ))*
      sourcePoleCoordinates branch e.val (sourceSheet branch n unit e.val) n 1)
    scaleApproach (𝓝 (if branch=0 then (softCoefficient branch:ℂ) else 0)) := by
  have paid:=tendsto_pi_nhds.mp (sourcePoleCoordinates_sheet branch n unit) 1
  fin_cases branch <;>
    simpa [regularScaling,fiveVector,fiveIndex,residueIndex,Pi.single_apply,Matrix.single_mulVec,
      Pi.smul_apply,smul_eq_mul,Matrix.mulVec_diagonal,Matrix.col_apply,Matrix.single_apply] using paid

/-- The full residual is multiplied by the actual moving cofactor column; no bounded-current premise enters. -/
theorem voltage_pole_residual_divided (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (row : Fin 289) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ))*
      sourcePoleFrameResidual branch e.val (sourceSheet branch n unit e.val) n row/(e.val:ℂ)^2)
      scaleApproach (𝓝 0) := by
  have terms (j : Fin 289):= (sourceNativeFrameResidual_sheet branch n unit row j).mul
    (tendsto_pi_nhds.mp (sourcePoleCoordinates_sheet branch n unit) j)
  have result:=tendsto_finsetSum Finset.univ (fun j _=>terms j)
  simp only [zero_mul,Finset.sum_const_zero] at result
  apply result.congr'
  filter_upwards [] with e
  simp only [sourcePoleFrameResidual,Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,
    Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem electric_residual_divided (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (i : Fin 3) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ))*
      voltageYElectric (physicalFrequencyMomentum (sourceSheet branch n unit e.val) n)
        (sourcePoleFrameResidual branch e.val (sourceSheet branch n unit e.val) n) i/(e.val:ℂ)^2)
      scaleApproach (𝓝 0) := by
  have time:=tendsto_pi_nhds.mp (sourceCurvatureDirection_tendsto branch n unit) 0
  have space:=tendsto_pi_nhds.mp (sourceCurvatureDirection_tendsto branch n unit) i.succ
  have result:=(time.mul (voltage_pole_residual_divided branch n unit (gaugeSlot i.succ 11))).sub
    (space.mul (voltage_pole_residual_divided branch n unit (gaugeSlot 0 11)))
  simp only [mul_zero,sub_zero] at result
  apply result.congr'
  filter_upwards [] with e
  unfold voltageYElectric
  ring

/-- The actual source-generated sheets have their next ordinary electric-curvature coefficient, with the original frequency-flux normalization. -/
theorem voltage_y_electric_ir (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (i : Fin 3) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ))*
      voltageYElectric (frequencyRay e.val (sourceSheet branch n unit e.val) n)
        (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n) i/(e.val:ℂ)^4)
      scaleApproach (𝓝 (if branch=0 then
        (-60/737:ℂ)*(sourceSpeed branch:ℂ)*(n i:ℂ)*(softCoefficient branch:ℂ) else 0)) := by
  have speed:=Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((sourceSheet_tendsto branch n unit).comp scaleVal_tendsto)
  have main:=(((tendsto_const_nhds (x:=(-60/737:ℂ))).mul speed).mul
    (tendsto_const_nhds (x:=(n i:ℂ)))).mul (pole_coordinate_one branch n unit)
  have result:=main.add (electric_residual_divided branch n unit i)
  simp only [add_zero,mul_ite,mul_zero] at result
  apply result.congr'
  filter_upwards [] with e
  rw [voltage_y_frequency_electric branch e.val _ n e.property.1.ne' i]
  have nonzero : (e.val:ℂ)≠0:=Complex.ofReal_ne_zero.mpr e.property.1.ne'
  simp only [Function.comp_apply]
  field_simp [nonzero]

end LowEnergy.GaussComposite.ActualEMCauchyDynamic
