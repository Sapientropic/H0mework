import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorCanonical79Data
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open MixedSpectatorCanonical79Data
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

/-- Coordinate selection in the original rational matrix. The original N and D
remain functions of the same transfer variable. -/
def selectedCanonicalInverse (x : ℂ) (entry : Option (Fin 526 × Fin 10)) : ℂ :=
  match entry with
  | none => 0
  | some (n,d) => numeratorPolynomial x 0 n / denominator x 0 d

end LowEnergy.ActualFourBlockRealTransfer
