import H0mework.NavierStokes.StressWeakInput.StressAction

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeWholeResolventZeroAction

open Set Filter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw
open NativeWholeResolvent NativeWholeResolventLimit NativeOriginalResolventInput NativeResolventCompactness
open NativeEndpointVelocityCarrier NativeCompleteStressAction NativeCompleteStressBilinear
open NativeTimeJetCarrier NativeCofinalFluxPairing

noncomputable section

def momentumOperator (nu : Viscosity) (velocity : State) : State →L[ℝ] State :=
  divergenceCLM.comp ((mixedCLM (wholeVelocity velocity)).comp wholeVelocityCLM) - viscousCLM nu

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem operator_norm_bound (source : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (input : wholePhysical) :
    ‖(operator source pointLe node step positive input).1‖ ≤ ‖input‖ := by
  exact ((operator source pointLe node step positive).le_opNorm input).trans
    ((mul_le_mul_of_nonneg_right (operator_norm source pointLe node step positive) (norm_nonneg _)).trans_eq (one_mul _))

theorem embedded_equation (source : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (input : wholePhysical) :
    NativeNegativeFourMomentum.embed ((operator source pointLe node step positive input).1 - input.1) =
      step • momentumOperator (nu := nu) (meanInput source pointLe node).1
        (operator source pointLe node step positive input).1 := by
  apply lp.ext
  funext wave
  have original := NativeWholeResolventEquation.operator_equation source pointLe node step positive input wave
  have weighted := congrArg (NativeNegativeFourMomentum.weightedRowCLM wave.1) original
  have read (value : State) : NativeNegativeFourMomentum.weightedRowCLM wave.1 (wholeVelocity value wave.1) =
      NativeNegativeFourMomentum.embed value wave := NativeNegativeFourMomentum.weightedRowCLM_row value wave
  rw [map_sub, map_smul, read, read] at weighted
  change NativeNegativeFourMomentum.embed (operator source pointLe node step positive input).1 wave -
    step • NativeNegativeFourMomentum.weightedRowCLM wave.1
      (projectedDivergenceCLM wave.1 (bilinearFlux (meanInput source pointLe node).1
        (operator source pointLe node step positive input).1 wave.1) -
        (nu.coeff * integerWaveViscousMultiplier wave.1) •
          wholeVelocity (operator source pointLe node step positive input).1 wave.1) =
      NativeNegativeFourMomentum.embed input.1 wave at weighted
  have actual : momentumOperator (nu := nu) (meanInput source pointLe node).1
      (operator source pointLe node step positive input).1 wave =
      NativeNegativeFourMomentum.weightedRowCLM wave.1
        (projectedDivergenceCLM wave.1 (bilinearFlux (meanInput source pointLe node).1
          (operator source pointLe node step positive input).1 wave.1) -
          (nu.coeff * integerWaveViscousMultiplier wave.1) •
            wholeVelocity (operator source pointLe node step positive input).1 wave.1) := by
    unfold momentumOperator
    change (divergenceCLM (mixed (wholeVelocity (meanInput source pointLe node).1)
      (wholeVelocity (operator source pointLe node step positive input).1)) -
        viscousCLM nu (operator source pointLe node step positive input).1) wave = _
    rw [lp.coeFn_sub, Pi.sub_apply, mixed, divergenceCLM_source, viscousCLM_source, ← map_sub]
    rfl
  change NativeNegativeFourMomentum.embed ((operator source pointLe node step positive input).1 - input.1) wave =
    step • (momentumOperator (nu := nu) (meanInput source pointLe node).1
      (operator source pointLe node step positive input).1 wave)
  rw [map_sub, lp.coeFn_sub, Pi.sub_apply, actual]
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp weighted).trans (add_comm _ _))

theorem embedded_error_bound (source : StressAt escape) (pointLe : point ≤ 1) (node : TimeNode)
    (step : ℝ) (positive : 0 < step) (input : wholePhysical) :
    ‖NativeNegativeFourMomentum.embed ((operator source pointLe node step positive input).1 - input.1)‖ ≤
      step * (‖momentumOperator (nu := nu) (meanInput source pointLe node).1‖ * ‖input‖) := by
  rw [embedded_equation, norm_smul, Real.norm_eq_abs, abs_of_pos positive]
  apply mul_le_mul_of_nonneg_left _ positive.le
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left (operator_norm_bound source pointLe node step positive input) (norm_nonneg _))

end
end SaturationMonoid.NavierStokes.NativeWholeResolventZeroAction
