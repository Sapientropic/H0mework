import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79ImaginaryGroupPilot
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79NumeratorFold
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary

theorem actual_numerator0_point :
    MixedSpectatorCanonical79Data.numeratorPolynomial Complex.I 0 (0 : Fin 526) =
      numeratorPoint 0 := by
  eval_canonical_numerator

end LowEnergy.ActualCanonical79Imaginary
