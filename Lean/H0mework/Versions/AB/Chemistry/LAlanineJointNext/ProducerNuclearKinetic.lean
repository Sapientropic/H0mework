import H0mework.Versions.AB.Chemistry.LAlanineJointNext.ProducerNuclearAccount

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Producer

open Force.Interface Inertia.SourceParsing
open LAlanine40K2025.JointNext.Source
noncomputable section

def targetMomentumKinetic : ℚ :=
  ∑ atom : Atom, (∑ axis : Axis, stepReadout.nuclear.target.momentum atom axis ^ 2) /
    (2 * stepReadout.nuclear.masses atom)

def targetKineticResidual : ℚ := stepReadout.nuclear.target.kinetic - targetMomentumKinetic

set_option maxHeartbeats 800000 in
theorem targetKineticResidual_bound : |targetKineticResidual| < (1 : ℚ) / 10 ^ 24 := by
  change |rationalRead _ -
    ∑ atom : Atom, (∑ axis : Axis, coordinateRead _ atom axis ^ 2) /
      (2 * massRead _ atom)| < (1 : ℚ) / 10 ^ 24
  norm_num [Fin.sum_univ_succ, coordinateRead, massRead, rationalRead]

theorem currentKinetic_reuses_parent :
    |stepReadout.nuclear.current.kinetic - Inertia.Producer.momentumKinetic| < (1 : ℚ) / 10 ^ 24 :=
  Inertia.Producer.nativeKineticResidual_bound

theorem targetKinetic_reconstruction :
    stepReadout.nuclear.target.kinetic = targetMomentumKinetic + targetKineticResidual := by
  unfold targetKineticResidual
  ring

theorem targetMechanicalEnergyWholeAccount :
    stepReadout.nuclear.target.total =
      targetMomentumKinetic + stepReadout.nuclear.target.potential + targetKineticResidual := by
  rw [nuclearTargetTotal_is_sum, targetKinetic_reconstruction]
  ring

end
end LAlanine40K2025.JointNext.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
