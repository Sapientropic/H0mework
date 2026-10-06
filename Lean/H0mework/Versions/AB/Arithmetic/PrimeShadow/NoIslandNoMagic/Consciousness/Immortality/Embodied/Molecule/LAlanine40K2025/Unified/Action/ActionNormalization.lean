import H0mework.Versions.AB.Physics.MotherSource.ActionNormalization
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.CanonicalTime

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource Stage10.ActionNormalization Stage9C.Material.SpinPair
open BasinRefinement SourceFiniteData
open scoped InnerProductSpace
noncomputable section

theorem action_normalization_AO_gram (first second : Basis) (scale : ℝ) (point : BasePoint) :
    (actionScale : ℂ)*CanonicalTime.timePair first second scale point =
      inner ℂ (ChargedSource.chargedSection first scale point) (ChargedSource.chargedSection second scale point) := by
  rw [CanonicalTime.time_pair_gram, actionScale_source]
  have nonzero : (4*(spinScale : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr spinScale_pos.ne')
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]

end
end LAlanine40K2025.UnifiedAction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
