import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferScalar
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open MixedSpectatorPairedSourceFrame

theorem actual_scalar_numerator_polynomial_analytic (z : ℂ) (a : Fin 20) :
    AnalyticAt ℂ (fun x => MixedSpectatorScalar61Exchange.numeratorPolynomial
      (worldTransfer x 0) a) z := by
  simp_rw [actual_axial_transfer]
  fin_cases a <;> norm_num [MixedSpectatorScalar61Exchange.numeratorPolynomial, axialTransfer]
  all_goals fun_prop

end LowEnergy.ActualFourBlockRealTransfer
