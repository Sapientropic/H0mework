import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorScalar61Exchange
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRealTransferTransfer
import Mathlib.Analysis.Meromorphic.Order

set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open MixedSpectatorPairedSourceFrame

theorem actual_scalar_denominator_analytic (z : ℂ) :
    AnalyticAt ℂ
      (fun x => MixedSpectatorScalar61Exchange.denominator (worldTransfer x 0)) z := by
  simp_rw [actual_axial_transfer]
  simp only [MixedSpectatorScalar61Exchange.denominator]
  norm_num [axialTransfer]
  fun_prop

end LowEnergy.ActualFourBlockRealTransfer
