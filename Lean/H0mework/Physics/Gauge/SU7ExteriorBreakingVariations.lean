import H0mework.Physics.Matter.SU7ExteriorMatterVariationCore

/-!
# Stage-8D breaking-field variation

Exact affine variation of the actual Λ⁴V breaking scalar.
-/

namespace SaturationMonoid.PhysicsCore.SU7ExteriorMatterFullVariations

open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterGaugeCovariantJet
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open DiracExteriorMatterAction
open DiracExteriorMatterLocalGaugeLink
open SU7ExteriorBreakingYukawa

noncomputable section

theorem stageEightEquationVector_withBreakingScalar
    (configuration : StageEightVariationConfiguration)
    (variation : ExteriorBreakingScalarCarrier)
    (coefficient : ℂ) :
    stageEightEquationVector
        (configuration.withBreakingScalar
          (configuration.breakingScalar + coefficient • variation)) =
      stageEightEquationVector configuration +
        coefficient •
          chiralExteriorYukawaAction variation configuration.sourceMatter := by
  change
    stageEightKineticVector configuration +
        chiralExteriorYukawaAction
          (configuration.breakingScalar + coefficient • variation)
          configuration.sourceMatter =
      (stageEightKineticVector configuration +
        chiralExteriorYukawaAction configuration.breakingScalar
          configuration.sourceMatter) +
        coefficient •
          chiralExteriorYukawaAction variation configuration.sourceMatter
  rw [chiralExteriorYukawaAction_add,
    chiralExteriorYukawaAction_smul,
    LinearMap.add_apply, LinearMap.smul_apply]
  module

theorem stageEightMatterAction_breaking_variation
    (configuration : StageEightVariationConfiguration)
    (variation : ExteriorBreakingScalarCarrier)
    (coefficient : ℂ) :
    stageEightMatterAction
        (configuration.withBreakingScalar
          (configuration.breakingScalar + coefficient • variation)) =
      stageEightMatterAction configuration +
        coefficient * stageEightBreakingEquation configuration variation := by
  change
    configuration.geometry.volume *
        configuration.conjugateMatter
          (stageEightEquationVector
            (configuration.withBreakingScalar
              (configuration.breakingScalar + coefficient • variation))) =
      configuration.geometry.volume *
          configuration.conjugateMatter
            (stageEightEquationVector configuration) +
        coefficient *
          (configuration.geometry.volume *
            configuration.conjugateMatter
              (chiralExteriorYukawaAction variation
                configuration.sourceMatter))
  rw [stageEightEquationVector_withBreakingScalar, map_add, map_smul]
  ring

end
end SaturationMonoid.PhysicsCore.SU7ExteriorMatterFullVariations
