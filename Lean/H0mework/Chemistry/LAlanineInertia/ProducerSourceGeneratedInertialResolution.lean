import H0mework.Chemistry.LAlanineInertia.SourceSourceBoundLAlanine40KInertialStep

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Inertia.Producer

open LAlanine40K2025.Inertia.Source

theorem currentForce_resolution : ∀ atom axis,
    |stepReadout.current.force atom axis + (stepReadout.currentGradientPicohartree atom axis : ℚ) / 10 ^ 12| <
      (1 : ℚ) / (2 * 10 ^ 12) := by
  change ∀ atom axis, |-SourceParsing.coordinateRead _ atom axis +
    (Force.Source.coordinateRead _ atom axis : ℚ) / 10 ^ 12| < (1 : ℚ) / (2 * 10 ^ 12)
  intro atom axis
  fin_cases atom <;> fin_cases axis <;>
    norm_num [SourceParsing.coordinateRead, SourceParsing.rationalRead, Force.Source.coordinateRead]

theorem targetForce_resolution : ∀ atom axis,
    |stepReadout.target.force atom axis + (stepReadout.targetGradientPicohartree atom axis : ℚ) / 10 ^ 12| <
      (1 : ℚ) / (2 * 10 ^ 12) := by
  change ∀ atom axis, |-SourceParsing.coordinateRead _ atom axis +
    (Force.Source.coordinateRead _ atom axis : ℚ) / 10 ^ 12| < (1 : ℚ) / (2 * 10 ^ 12)
  intro atom axis
  fin_cases atom <;> fin_cases axis <;>
    norm_num [SourceParsing.coordinateRead, SourceParsing.rationalRead, Force.Source.coordinateRead]

theorem currentPosition_resolution : ∀ atom axis,
    |stepReadout.current.position atom axis - (stepReadout.currentPositionPicobohr atom axis : ℚ) / 10 ^ 12| <
      (1 : ℚ) / (2 * 10 ^ 12) := by
  change ∀ atom axis, |SourceParsing.coordinateRead _ atom axis -
    (Force.Source.coordinateRead _ atom axis : ℚ) / 10 ^ 12| < (1 : ℚ) / (2 * 10 ^ 12)
  intro atom axis
  fin_cases atom <;> fin_cases axis <;>
    norm_num [SourceParsing.coordinateRead, SourceParsing.rationalRead, Force.Source.coordinateRead]

theorem targetPosition_resolution : ∀ atom axis,
    |stepReadout.target.position atom axis - (stepReadout.targetPositionPicobohr atom axis : ℚ) / 10 ^ 12| <
      (1 : ℚ) / (2 * 10 ^ 12) := by
  change ∀ atom axis, |SourceParsing.coordinateRead _ atom axis -
    (Force.Source.coordinateRead _ atom axis : ℚ) / 10 ^ 12| < (1 : ℚ) / (2 * 10 ^ 12)
  intro atom axis
  fin_cases atom <;> fin_cases axis <;>
    norm_num [SourceParsing.coordinateRead, SourceParsing.rationalRead, Force.Source.coordinateRead]

theorem currentPotential_resolution :
    |stepReadout.current.potential - (stepReadout.currentLedger.reportedSCF : ℚ) / 10 ^ 9| <
      (1 : ℚ) / (2 * 10 ^ 9) := by
  change |SourceParsing.rationalRead _ - ((-(_ : ℕ) : Int) : ℚ) / 10 ^ 9| < (1 : ℚ) / (2 * 10 ^ 9)
  norm_num [SourceParsing.rationalRead]

theorem targetPotential_resolution :
    |stepReadout.target.potential - (stepReadout.targetLedger.reportedSCF : ℚ) / 10 ^ 9| <
      (1 : ℚ) / (2 * 10 ^ 9) := by
  change |SourceParsing.rationalRead _ - ((-(_ : ℕ) : Int) : ℚ) / 10 ^ 9| < (1 : ℚ) / (2 * 10 ^ 9)
  norm_num [SourceParsing.rationalRead]

end LAlanine40K2025.Inertia.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
