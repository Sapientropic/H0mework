import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Step

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
noncomputable section

-- The unreserved stock grows; the shrinking rational floor is not the whole receiver.
def unreserved (current : Material) : ℝ := current.body.resource.momentum-(current.reserve : ℝ)

theorem unreserved_positive (current : Material) (valid : Admissible current) : 0 < unreserved current := by
  unfold unreserved
  exact sub_pos.mpr valid.reserveBelowStock

theorem next_unreserved_increases (current : Material) (valid : Admissible current) :
    unreserved current < unreserved (nextMaterial current) := by
  have debit : (nextKineticQ current : ℝ)-(current.body.frame.kinetic : ℝ)<(current.reserve : ℝ)/2 := by
    exact_mod_cast (positive_debit_below_reserve current valid).2
  change current.body.resource.momentum-(current.reserve : ℝ)<
    current.body.resource.momentum+(current.body.frame.kinetic : ℝ)-(nextKineticQ current : ℝ)-
    ((current.reserve/2 : ℚ) : ℝ)
  push_cast
  linarith only [debit]

theorem next_receiver_decreases (current : Material) (valid : Admissible current) :
    (nextMaterial current).body.resource.momentum < current.body.resource.momentum := by
  have debit : (0 : ℝ)<(nextKineticQ current : ℝ)-(current.body.frame.kinetic : ℝ) := by
    exact_mod_cast (positive_debit_below_reserve current valid).1
  change current.body.resource.momentum+(current.body.frame.kinetic : ℝ)-(nextKineticQ current : ℝ)<_
  linarith only [debit]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation
