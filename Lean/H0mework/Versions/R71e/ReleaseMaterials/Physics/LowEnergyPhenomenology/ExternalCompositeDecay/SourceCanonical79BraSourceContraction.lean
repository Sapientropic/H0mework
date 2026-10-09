import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraSourceCurrent
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79SourceContraction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open scoped BigOperators

theorem actual_canonical_source_bra (dual : Bool) :
    (∑a : Fin 97,∑b : Fin 97,
      ((-1/2 : ℂ)*MixedSpectatorCanonical79Exchange.canonicalCoefficient Complex.I 0 a b)*
        ActualCandidateBra.pairPoint dual a b) =
      ∑i : Fin 79,∑j : Fin 79,
        ((-1/2 : ℂ)*MixedSpectatorCanonical79Data.axialInverse Complex.I 0 i j)*
          currentPoint dual i j := by
  simp only [MixedSpectatorCanonical79Exchange.canonicalCoefficient,
    ActualFourBlockElastic.zero_signed_radius]
  simp_rw [actual_world_source_point]
  rw [source_coefficient_pair_contraction]
  simp_rw [actual_source_current]
  norm_num

end LowEnergy.ActualCanonical79Imaginary
