import H0mework.Physics.Matter.SU7ExteriorMatterVariationCore
import H0mework.Physics.Gauge.SU7FiniteVariationAlgebra

/-!
# Stage-8D mother-transport current variation

Exact affine mother-link transport variation and its current coefficient.
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

theorem stageEightKineticResidual_withMotherTransport
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracMatterEnd)
    (coefficient : ℂ)
    (direction : LorentzianIndex) :
    stageEightKineticResidual
        (configuration.withMotherTransport
          (configuration.motherTransport + coefficient • variation)) direction =
      stageEightKineticResidual configuration direction +
        coefficient •
          variation direction (configuration.targetMatter direction) := by
  change
    (configuration.motherTransport direction +
          coefficient • variation direction)
          (configuration.targetMatter direction) -
        configuration.sourceMatter +
        configuration.geometry.spinAction direction
          configuration.sourceMatter =
      (configuration.motherTransport direction
          (configuration.targetMatter direction) -
        configuration.sourceMatter +
        configuration.geometry.spinAction direction
          configuration.sourceMatter) +
      coefficient •
        variation direction (configuration.targetMatter direction)
  rw [LinearMap.add_apply, LinearMap.smul_apply]
  module

theorem stageEightKineticVector_withMotherTransport
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracMatterEnd)
    (coefficient : ℂ) :
    stageEightKineticVector
        (configuration.withMotherTransport
          (configuration.motherTransport + coefficient • variation)) =
      stageEightKineticVector configuration +
        coefficient •
          (Complex.I •
            ∑ direction : LorentzianIndex,
              configuration.geometry.gammaAction direction
                (variation direction
                  (configuration.targetMatter direction))) := by
  change
    Complex.I •
        ∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual
              (configuration.withMotherTransport
                (configuration.motherTransport + coefficient • variation))
              direction) =
      Complex.I •
          ∑ direction : LorentzianIndex,
            configuration.geometry.gammaAction direction
              (stageEightKineticResidual configuration direction) +
        coefficient •
          (Complex.I •
            ∑ direction : LorentzianIndex,
              configuration.geometry.gammaAction direction
                (variation direction
                  (configuration.targetMatter direction)))
  have sumUpdate :
      (∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual
              (configuration.withMotherTransport
                (configuration.motherTransport + coefficient • variation))
              direction)) =
        (∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual configuration direction)) +
          coefficient •
            ∑ direction : LorentzianIndex,
              configuration.geometry.gammaAction direction
                (variation direction
                  (configuration.targetMatter direction)) := by
    calc
      _ = ∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual configuration direction +
              coefficient • variation direction
                (configuration.targetMatter direction)) := by
            apply Finset.sum_congr rfl
            intro direction _
            rw [stageEightKineticResidual_withMotherTransport]
      _ = _ := finiteSum_linear_apply_add_smul
        configuration.geometry.gammaAction
        (fun direction => stageEightKineticResidual configuration direction)
        (fun direction =>
          variation direction (configuration.targetMatter direction))
        coefficient
  rw [sumUpdate]
  module

theorem stageEightEquationVector_withMotherTransport
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracMatterEnd)
    (coefficient : ℂ) :
    stageEightEquationVector
        (configuration.withMotherTransport
          (configuration.motherTransport + coefficient • variation)) =
      stageEightEquationVector configuration +
        coefficient •
          (Complex.I •
            ∑ direction : LorentzianIndex,
              configuration.geometry.gammaAction direction
                (variation direction
                  (configuration.targetMatter direction))) := by
  change
    stageEightKineticVector
          (configuration.withMotherTransport
            (configuration.motherTransport + coefficient • variation)) +
        stageEightYukawaVector configuration =
      (stageEightKineticVector configuration +
        stageEightYukawaVector configuration) +
        coefficient •
          (Complex.I •
            ∑ direction : LorentzianIndex,
              configuration.geometry.gammaAction direction
                (variation direction
                  (configuration.targetMatter direction)))
  rw [stageEightKineticVector_withMotherTransport]
  module

theorem stageEightMatterAction_mother_variation
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracMatterEnd)
    (coefficient : ℂ) :
    stageEightMatterAction
        (configuration.withMotherTransport
          (configuration.motherTransport + coefficient • variation)) =
      stageEightMatterAction configuration +
        coefficient * stageEightMotherCurrent configuration variation := by
  change
    configuration.geometry.volume *
        configuration.conjugateMatter
          (stageEightEquationVector
            (configuration.withMotherTransport
              (configuration.motherTransport + coefficient • variation))) =
      configuration.geometry.volume *
          configuration.conjugateMatter
            (stageEightEquationVector configuration) +
        coefficient *
          (configuration.geometry.volume *
            configuration.conjugateMatter
              (Complex.I •
                ∑ direction : LorentzianIndex,
                  configuration.geometry.gammaAction direction
                    (variation direction
                      (configuration.targetMatter direction))))
  rw [stageEightEquationVector_withMotherTransport, map_add, map_smul]
  ring

end
end SaturationMonoid.PhysicsCore.SU7ExteriorMatterFullVariations
