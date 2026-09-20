import H0mework.Physics.Matter.SU7ExteriorMatterVariationCore
import H0mework.Physics.Gauge.SU7FiniteVariationAlgebra

/-!
# Stage-8D source, target, and conjugate matter variations

Exact affine first-variation laws for source matter, target matter, and the
independent conjugate field.  Directional residual and gamma-contracted
kinetic lemmas are kept in this physical-theme module rather than chained
through historical checkpoint imports.
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

/-! ## Source matter -/

/-! ## Exact affine first-variation laws -/

theorem stageEightKineticResidual_withSourceMatter
    (configuration : StageEightVariationConfiguration)
    (variation : DiracExteriorMatterCarrier)
    (coefficient : ℂ)
    (direction : LorentzianIndex) :
    stageEightKineticResidual
        (configuration.withSourceMatter
          (configuration.sourceMatter + coefficient • variation)) direction =
      stageEightKineticResidual configuration direction +
        coefficient •
          (-variation +
            configuration.geometry.spinAction direction variation) := by
  change
    configuration.motherTransport direction
          (configuration.targetMatter direction) -
        (configuration.sourceMatter + coefficient • variation) +
        configuration.geometry.spinAction direction
          (configuration.sourceMatter + coefficient • variation) =
      (configuration.motherTransport direction
          (configuration.targetMatter direction) -
        configuration.sourceMatter +
        configuration.geometry.spinAction direction
          configuration.sourceMatter) +
      coefficient •
        (-variation +
          configuration.geometry.spinAction direction variation)
  rw [map_add, map_smul]
  module

theorem stageEightKineticVector_withSourceMatter
    (configuration : StageEightVariationConfiguration)
    (variation : DiracExteriorMatterCarrier)
    (coefficient : ℂ) :
    stageEightKineticVector
        (configuration.withSourceMatter
          (configuration.sourceMatter + coefficient • variation)) =
      stageEightKineticVector configuration +
        coefficient •
          (Complex.I •
            ∑ direction : LorentzianIndex,
              configuration.geometry.gammaAction direction
                (-variation +
                  configuration.geometry.spinAction direction variation)) := by
  change
    Complex.I •
        ∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual
              (configuration.withSourceMatter
                (configuration.sourceMatter + coefficient • variation))
              direction) =
      Complex.I •
          ∑ direction : LorentzianIndex,
            configuration.geometry.gammaAction direction
              (stageEightKineticResidual configuration direction) +
        coefficient •
          (Complex.I •
            ∑ direction : LorentzianIndex,
              configuration.geometry.gammaAction direction
                (-variation +
                  configuration.geometry.spinAction direction variation))
  have sumUpdate :
      (∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual
              (configuration.withSourceMatter
                (configuration.sourceMatter + coefficient • variation))
              direction)) =
        (∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual configuration direction)) +
          coefficient •
            ∑ direction : LorentzianIndex,
              configuration.geometry.gammaAction direction
                (-variation +
                  configuration.geometry.spinAction direction variation) := by
    calc
      _ = ∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual configuration direction +
              coefficient •
                (-variation +
                  configuration.geometry.spinAction direction variation)) := by
            apply Finset.sum_congr rfl
            intro direction _
            rw [stageEightKineticResidual_withSourceMatter]
      _ = _ := finiteSum_linear_apply_add_smul
        configuration.geometry.gammaAction
        (fun direction => stageEightKineticResidual configuration direction)
        (fun direction =>
          -variation + configuration.geometry.spinAction direction variation)
        coefficient
  rw [sumUpdate]
  module

theorem stageEightYukawaVector_withSourceMatter
    (configuration : StageEightVariationConfiguration)
    (variation : DiracExteriorMatterCarrier)
    (coefficient : ℂ) :
    stageEightYukawaVector
        (configuration.withSourceMatter
          (configuration.sourceMatter + coefficient • variation)) =
      stageEightYukawaVector configuration +
        coefficient •
          chiralExteriorYukawaAction configuration.breakingScalar variation := by
  change
    chiralExteriorYukawaAction configuration.breakingScalar
        (configuration.sourceMatter + coefficient • variation) =
      chiralExteriorYukawaAction configuration.breakingScalar
          configuration.sourceMatter +
        coefficient •
          chiralExteriorYukawaAction configuration.breakingScalar variation
  rw [map_add, map_smul]

theorem stageEightEquationVector_withSourceMatter
    (configuration : StageEightVariationConfiguration)
    (variation : DiracExteriorMatterCarrier)
    (coefficient : ℂ) :
    stageEightEquationVector
        (configuration.withSourceMatter
          (configuration.sourceMatter + coefficient • variation)) =
      stageEightEquationVector configuration +
        coefficient • stageEightSourceLinearizedVector configuration variation := by
  rw [stageEightEquationVector, stageEightKineticVector_withSourceMatter,
    stageEightYukawaVector_withSourceMatter]
  change
    (stageEightKineticVector configuration +
          coefficient •
            (Complex.I •
              ∑ direction : LorentzianIndex,
                configuration.geometry.gammaAction direction
                  (-variation +
                    configuration.geometry.spinAction direction variation))) +
        (stageEightYukawaVector configuration +
          coefficient •
            chiralExteriorYukawaAction configuration.breakingScalar variation) =
      (stageEightKineticVector configuration +
          stageEightYukawaVector configuration) +
        coefficient • stageEightSourceLinearizedVector configuration variation
  rw [stageEightSourceLinearizedVector]
  module

theorem stageEightMatterAction_source_variation
    (configuration : StageEightVariationConfiguration)
    (variation : DiracExteriorMatterCarrier)
    (coefficient : ℂ) :
    stageEightMatterAction
        (configuration.withSourceMatter
          (configuration.sourceMatter + coefficient • variation)) =
      stageEightMatterAction configuration +
        coefficient * stageEightSourceEquation configuration variation := by
  change
    configuration.geometry.volume *
        configuration.conjugateMatter
          (stageEightEquationVector
            (configuration.withSourceMatter
              (configuration.sourceMatter + coefficient • variation))) =
      configuration.geometry.volume *
          configuration.conjugateMatter
            (stageEightEquationVector configuration) +
        coefficient *
          (configuration.geometry.volume *
            configuration.conjugateMatter
              (stageEightSourceLinearizedVector configuration variation))
  rw [stageEightEquationVector_withSourceMatter, map_add, map_smul]
  ring

/-! ## Target matter -/

theorem stageEightKineticResidual_withTargetMatter
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier)
    (coefficient : ℂ)
    (direction : LorentzianIndex) :
    stageEightKineticResidual
        (configuration.withTargetMatter
          (configuration.targetMatter + coefficient • variation)) direction =
      stageEightKineticResidual configuration direction +
        coefficient •
          configuration.motherTransport direction (variation direction) := by
  change
    configuration.motherTransport direction
          (configuration.targetMatter direction +
            coefficient • variation direction) -
        configuration.sourceMatter +
        configuration.geometry.spinAction direction
          configuration.sourceMatter =
      (configuration.motherTransport direction
          (configuration.targetMatter direction) -
        configuration.sourceMatter +
        configuration.geometry.spinAction direction
          configuration.sourceMatter) +
      coefficient •
        configuration.motherTransport direction (variation direction)
  rw [map_add, map_smul]
  module

theorem stageEightKineticVector_withTargetMatter
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier)
    (coefficient : ℂ) :
    stageEightKineticVector
        (configuration.withTargetMatter
          (configuration.targetMatter + coefficient • variation)) =
      stageEightKineticVector configuration +
        coefficient • stageEightTargetLinearizedVector configuration variation := by
  change
    Complex.I •
        ∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual
              (configuration.withTargetMatter
                (configuration.targetMatter + coefficient • variation))
              direction) =
      Complex.I •
          ∑ direction : LorentzianIndex,
            configuration.geometry.gammaAction direction
              (stageEightKineticResidual configuration direction) +
        coefficient •
          (Complex.I •
            ∑ direction : LorentzianIndex,
              configuration.geometry.gammaAction direction
                (configuration.motherTransport direction
                  (variation direction)))
  have sumUpdate :
      (∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual
              (configuration.withTargetMatter
                (configuration.targetMatter + coefficient • variation))
              direction)) =
        (∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual configuration direction)) +
          coefficient •
            ∑ direction : LorentzianIndex,
              configuration.geometry.gammaAction direction
                (configuration.motherTransport direction
                  (variation direction)) := by
    calc
      _ = ∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual configuration direction +
              coefficient •
                configuration.motherTransport direction
                  (variation direction)) := by
            apply Finset.sum_congr rfl
            intro direction _
            rw [stageEightKineticResidual_withTargetMatter]
      _ = _ := finiteSum_linear_apply_add_smul
        configuration.geometry.gammaAction
        (fun direction => stageEightKineticResidual configuration direction)
        (fun direction =>
          configuration.motherTransport direction (variation direction))
        coefficient
  rw [sumUpdate]
  module

theorem stageEightEquationVector_withTargetMatter
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier)
    (coefficient : ℂ) :
    stageEightEquationVector
        (configuration.withTargetMatter
          (configuration.targetMatter + coefficient • variation)) =
      stageEightEquationVector configuration +
        coefficient • stageEightTargetLinearizedVector configuration variation := by
  change
    stageEightKineticVector
          (configuration.withTargetMatter
            (configuration.targetMatter + coefficient • variation)) +
        stageEightYukawaVector configuration =
      (stageEightKineticVector configuration +
        stageEightYukawaVector configuration) +
        coefficient • stageEightTargetLinearizedVector configuration variation
  rw [stageEightKineticVector_withTargetMatter]
  module

theorem stageEightMatterAction_target_variation
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier)
    (coefficient : ℂ) :
    stageEightMatterAction
        (configuration.withTargetMatter
          (configuration.targetMatter + coefficient • variation)) =
      stageEightMatterAction configuration +
        coefficient * stageEightTargetEquation configuration variation := by
  change
    configuration.geometry.volume *
        configuration.conjugateMatter
          (stageEightEquationVector
            (configuration.withTargetMatter
              (configuration.targetMatter + coefficient • variation))) =
      configuration.geometry.volume *
          configuration.conjugateMatter
            (stageEightEquationVector configuration) +
        coefficient *
          (configuration.geometry.volume *
            configuration.conjugateMatter
              (stageEightTargetLinearizedVector configuration variation))
  rw [stageEightEquationVector_withTargetMatter, map_add, map_smul]
  ring

/-! ## Independent conjugate matter -/

theorem stageEightMatterAction_conjugate_variation
    (configuration : StageEightVariationConfiguration)
    (variation : Module.Dual ℂ DiracExteriorMatterCarrier)
    (coefficient : ℂ) :
    stageEightMatterAction
        (configuration.withConjugateMatter
          (configuration.conjugateMatter + coefficient • variation)) =
      stageEightMatterAction configuration +
        coefficient * variation
          (stageEightConjugateEquationVector configuration) := by
  change
    configuration.geometry.volume *
        (configuration.conjugateMatter + coefficient • variation)
          (stageEightEquationVector configuration) =
      configuration.geometry.volume *
          configuration.conjugateMatter
            (stageEightEquationVector configuration) +
        coefficient *
          variation
            (configuration.geometry.volume •
              stageEightEquationVector configuration)
  rw [LinearMap.add_apply, LinearMap.smul_apply, map_smul]
  ring

end
end SaturationMonoid.PhysicsCore.SU7ExteriorMatterFullVariations
