import H0mework.Chemistry.LAlanineHeldForce.SourceSourceBoundLAlanineHeldForce
import H0mework.Chemistry.LAlanineInertia.ProducerSourceGeneratedInertialForceEnergy

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.HeldForce.Producer

open LAlanine40K2025.HeldForce.Source Force.Interface

theorem six_force_components : gradientComponentsReadout.size = 6 := by decide

theorem forceWholeLedger : ∀ atom axis,
    Inertia.Producer.forceComponentSum gradientComponentsReadout atom axis + gradientResidual atom axis =
      gradientPicohartree atom axis := by
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> decide

theorem force_opposes_gradient : ∀ atom axis, forcePicohartree atom axis = -gradientPicohartree atom axis := by
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> decide

theorem stationary_correction_nonzero : stationaryCorrection 0 0 = -6823 ∧ stationaryCorrection ≠ 0 := by
  constructor
  · decide
  · intro equal
    have entry := congrFun (congrFun equal 0) 0
    norm_num [stationaryCorrection, Force.Source.coordinateRead] at entry

theorem rawGradient_resolution : ∀ atom axis,
    |rawGradient atom axis - (gradientPicohartree atom axis : ℚ) / 10 ^ 12| < (1 : ℚ) / (2 * 10 ^ 12) := by
  intro atom axis
  fin_cases atom <;> fin_cases axis <;>
    norm_num [rawGradient, gradientPicohartree, Inertia.SourceParsing.coordinateRead,
      Inertia.SourceParsing.rationalRead, Force.Source.coordinateRead]

theorem no_dropped_gradient_residual : ∀ atom axis, |gradientResidual atom axis| ≤ 3 := by
  intro atom axis
  fin_cases atom <;> fin_cases axis <;> decide

end LAlanine40K2025.HeldForce.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
