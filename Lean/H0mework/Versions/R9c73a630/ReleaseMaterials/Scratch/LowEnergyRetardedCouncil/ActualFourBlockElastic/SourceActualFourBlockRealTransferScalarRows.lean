import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferScalarRead
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open MixedSpectatorPairedSourceFrame

theorem actual_scalar_numerator_analytic (z : ℂ) (a b : Fin 70) :
    AnalyticAt ℂ (fun x => MixedSpectatorScalar61Exchange.numerator (worldTransfer x 0) a b) z := by
  have he : (fun x => MixedSpectatorScalar61Exchange.numerator (worldTransfer x 0) a b) =
      (fun x => scalarNumeratorRead (worldTransfer x 0) a b) :=
    funext (fun x => actual_scalar_numerator_read _ a b)
  rw [he]
  unfold scalarNumeratorRead
  cases hs : scalarNumeratorIndex a b with
  | none => simpa only [hs] using (analyticAt_const (v := (0 : ℂ)) (x := z))
  | some i => simpa only [hs] using actual_scalar_numerator_polynomial_analytic z i

theorem actual_scalar_coefficient_analytic (z : ℂ)
    (h : MixedSpectatorScalar61Exchange.denominator (worldTransfer z 0) ≠ 0) (a b : Fin 70) :
    AnalyticAt ℂ (fun x => MixedSpectatorScalar61Exchange.greenCoefficient (worldTransfer x 0) a b) z :=
  (actual_scalar_numerator_analytic z a b).div (actual_scalar_denominator_analytic z) h

end LowEnergy.ActualFourBlockRealTransfer
