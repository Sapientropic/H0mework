import H0mework.Chemistry.LAlanineInertia.ProducerSourceGeneratedInertialEnergyAccount

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.Producer

open Force.Interface
open LAlanine40K2025.Inertia.Source

noncomputable section

/-- The kinetic reader uses every momentum coordinate and the same isotope mass. -/
def momentumKinetic : ℚ :=
  ∑ atom : Atom, (∑ axis : Axis, stepReadout.target.momentum atom axis ^ 2) /
    (2 * stepReadout.masses atom)

def nativeKineticResidual : ℚ := stepReadout.target.kinetic - momentumKinetic

set_option maxHeartbeats 800000 in
theorem nativeKineticResidual_bound : |nativeKineticResidual| < (1 : ℚ) / 10 ^ 24 := by
  change |SourceParsing.rationalRead _ -
    ∑ atom : Atom, (∑ axis : Axis, SourceParsing.coordinateRead _ atom axis ^ 2) /
      (2 * SourceParsing.massRead _ atom)| < (1 : ℚ) / 10 ^ 24
  norm_num [Fin.sum_univ_succ, SourceParsing.coordinateRead, SourceParsing.massRead,
    SourceParsing.rationalRead]

theorem kinetic_reconstruction : stepReadout.target.kinetic = momentumKinetic + nativeKineticResidual := by
  unfold nativeKineticResidual
  ring

theorem mechanicalEnergyWholeAccount :
    stepReadout.target.total = momentumKinetic + stepReadout.target.potential +
      nativeKineticResidual + fineEnergyArithmeticResidual := by
  unfold nativeKineticResidual fineEnergyArithmeticResidual
  ring

end
end LAlanine40K2025.Inertia.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
