import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorPairedSourceFrame

set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open MixedSpectatorPairedSourceFrame

/-- This is the zero-spatial restriction of the original Fourier transfer,
using a Nat selector so literal source projections reduce before analysis. -/
def axialTransfer (x : ℂ) (a : Fin 4) : ℂ :=
  if a.val = 0 then (6*(Real.sqrt 15 : ℂ)/25)*x else 0

theorem actual_axial_transfer (x : ℂ) : worldTransfer x 0 = axialTransfer x := by
  ext a
  fin_cases a <;> norm_num [worldTransfer,axialTransfer]

end LowEnergy.ActualFourBlockRealTransfer
