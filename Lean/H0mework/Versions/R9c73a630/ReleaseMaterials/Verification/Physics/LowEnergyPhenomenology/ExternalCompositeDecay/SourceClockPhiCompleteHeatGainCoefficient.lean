import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiActualCovarianceStep
set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceClockPhiCompleteHeatGainCoefficient
open GaussHistoryHilbert SourceQuantumScalarChart SourcePhysicalKineticSquare
open SourceClockPhiCoframeForwardCore SourceClockPhiActualCovarianceStep

theorem actual_complete_heat_gain_square_price (t:ℝ) (ht:0<t) (z:physicalChart):
    (gainProfile (Real.sqrt t) z.val)^2≤1+6*t*reciprocalVolume z.val:=by
  have hR:=forward_ratio_pos t ht.le z
  let R:ℝ:=forwardRatio t z.val
  let a:ℝ:=R^(1/3:ℝ)
  have ha:0≤a:=Real.rpow_nonneg hR.le _
  have hc:a^3=R:=by
    change (R^(1/3:ℝ))^3=R
    rw [←Real.rpow_natCast,←Real.rpow_mul hR.le]
    norm_num
    rfl
  have hs:(gainProfile (Real.sqrt t) z.val)^2=a:=by
    unfold gainProfile
    rw [Real.sq_sqrt ht.le,←Real.rpow_natCast,←Real.rpow_mul hR.le]
    norm_num
    rfl
  have hp:0≤(a-1)^2*(a+2):=mul_nonneg (sq_nonneg _) (by linarith)
  have hl:a≤1+(R-1)/3:=by nlinarith [hc]
  have he:1+(R-1)/3=1+6*t*reciprocalVolume z.val:=by
    dsimp only [R,forwardRatio,reciprocalVolume]
    field_simp [(GaussNativeEnergy.volume_pos z).ne']
    ring
  rw [hs]
  exact he ▸ hl
end LowEnergy.SourceClockPhiCompleteHeatGainCoefficient
