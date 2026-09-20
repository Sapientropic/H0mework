import H0mework.Physics.Matter.SU7ExteriorMatterVariationCore
import H0mework.Physics.Gauge.SU7FiniteVariationAlgebra

/-!
# Stage-8D finite geometry-readout variations

Exact volume, inverse-coframe gamma, and spin-readout variations plus the assembled field equations.
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

theorem stageEightMatterAction_volume_variation
    (configuration : StageEightVariationConfiguration)
    (variation coefficient : ℂ) :
    stageEightMatterAction
        (configuration.withGeometryVolume
          (configuration.geometry.volume + coefficient * variation)) =
      stageEightMatterAction configuration +
        coefficient * variation * stageEightVolumeStress configuration := by
  change
    (configuration.geometry.volume + coefficient * variation) *
        configuration.conjugateMatter
          (stageEightEquationVector configuration) =
      configuration.geometry.volume *
          configuration.conjugateMatter
            (stageEightEquationVector configuration) +
        coefficient * variation *
          configuration.conjugateMatter
            (stageEightEquationVector configuration)
  ring

theorem stageEightEquationVector_withGeometryGamma
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracMatterEnd)
    (coefficient : ℂ) :
    stageEightEquationVector
        (configuration.withGeometryGamma
          (configuration.geometry.gammaAction + coefficient • variation)) =
      stageEightEquationVector configuration +
        coefficient •
          (Complex.I •
            ∑ direction : LorentzianIndex,
              variation direction
                (stageEightKineticResidual configuration direction)) := by
  change
    Complex.I •
          ∑ direction : LorentzianIndex,
            (configuration.geometry.gammaAction direction +
                coefficient • variation direction)
              (stageEightKineticResidual configuration direction) +
        stageEightYukawaVector configuration =
      (Complex.I •
          ∑ direction : LorentzianIndex,
            configuration.geometry.gammaAction direction
              (stageEightKineticResidual configuration direction) +
        stageEightYukawaVector configuration) +
        coefficient •
          (Complex.I •
            ∑ direction : LorentzianIndex,
              variation direction
                (stageEightKineticResidual configuration direction))
  have sumUpdate :
      (∑ direction : LorentzianIndex,
          (configuration.geometry.gammaAction direction +
              coefficient • variation direction)
            (stageEightKineticResidual configuration direction)) =
        (∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual configuration direction)) +
          coefficient •
            ∑ direction : LorentzianIndex,
              variation direction
                (stageEightKineticResidual configuration direction) := by
    calc
      _ = ∑ direction : LorentzianIndex,
          (configuration.geometry.gammaAction direction
              (stageEightKineticResidual configuration direction) +
            coefficient • variation direction
              (stageEightKineticResidual configuration direction)) := by
            apply Finset.sum_congr rfl
            intro direction _
            rw [LinearMap.add_apply, LinearMap.smul_apply]
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.smul_sum]
  rw [sumUpdate]
  module

theorem stageEightMatterAction_gamma_variation
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracMatterEnd)
    (coefficient : ℂ) :
    stageEightMatterAction
        (configuration.withGeometryGamma
          (configuration.geometry.gammaAction + coefficient • variation)) =
      stageEightMatterAction configuration +
        coefficient * stageEightGammaStress configuration variation := by
  change
    configuration.geometry.volume *
        configuration.conjugateMatter
          (stageEightEquationVector
            (configuration.withGeometryGamma
              (configuration.geometry.gammaAction + coefficient • variation))) =
      configuration.geometry.volume *
          configuration.conjugateMatter
            (stageEightEquationVector configuration) +
        coefficient *
          (configuration.geometry.volume *
            configuration.conjugateMatter
              (Complex.I •
                ∑ direction : LorentzianIndex,
                  variation direction
                    (stageEightKineticResidual configuration direction)))
  rw [stageEightEquationVector_withGeometryGamma, map_add, map_smul]
  ring

theorem stageEightKineticResidual_withGeometrySpin
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracMatterEnd)
    (coefficient : ℂ)
    (direction : LorentzianIndex) :
    stageEightKineticResidual
        (configuration.withGeometrySpin
          (configuration.geometry.spinAction + coefficient • variation)) direction =
      stageEightKineticResidual configuration direction +
        coefficient • variation direction configuration.sourceMatter := by
  change
    configuration.motherTransport direction
          (configuration.targetMatter direction) -
        configuration.sourceMatter +
        (configuration.geometry.spinAction direction +
            coefficient • variation direction)
          configuration.sourceMatter =
      (configuration.motherTransport direction
          (configuration.targetMatter direction) -
        configuration.sourceMatter +
        configuration.geometry.spinAction direction
          configuration.sourceMatter) +
        coefficient • variation direction configuration.sourceMatter
  rw [LinearMap.add_apply, LinearMap.smul_apply]
  module

theorem stageEightEquationVector_withGeometrySpin
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracMatterEnd)
    (coefficient : ℂ) :
    stageEightEquationVector
        (configuration.withGeometrySpin
          (configuration.geometry.spinAction + coefficient • variation)) =
      stageEightEquationVector configuration +
        coefficient •
          (Complex.I •
            ∑ direction : LorentzianIndex,
              configuration.geometry.gammaAction direction
                (variation direction configuration.sourceMatter)) := by
  change
    (Complex.I •
          ∑ direction : LorentzianIndex,
            configuration.geometry.gammaAction direction
              (stageEightKineticResidual
                (configuration.withGeometrySpin
                  (configuration.geometry.spinAction + coefficient • variation))
                direction)) +
        stageEightYukawaVector configuration =
      (Complex.I •
          ∑ direction : LorentzianIndex,
            configuration.geometry.gammaAction direction
              (stageEightKineticResidual configuration direction) +
        stageEightYukawaVector configuration) +
        coefficient •
          (Complex.I •
            ∑ direction : LorentzianIndex,
              configuration.geometry.gammaAction direction
                (variation direction configuration.sourceMatter))
  have sumUpdate :
      (∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual
              (configuration.withGeometrySpin
                (configuration.geometry.spinAction + coefficient • variation))
              direction)) =
        (∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual configuration direction)) +
          coefficient •
            ∑ direction : LorentzianIndex,
              configuration.geometry.gammaAction direction
                (variation direction configuration.sourceMatter) := by
    calc
      _ = ∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (stageEightKineticResidual configuration direction +
              coefficient •
                variation direction configuration.sourceMatter) := by
            apply Finset.sum_congr rfl
            intro direction _
            rw [stageEightKineticResidual_withGeometrySpin]
      _ = _ := finiteSum_linear_apply_add_smul
        configuration.geometry.gammaAction
        (fun direction => stageEightKineticResidual configuration direction)
        (fun direction => variation direction configuration.sourceMatter)
        coefficient
  rw [sumUpdate]
  module

theorem stageEightMatterAction_spin_variation
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracMatterEnd)
    (coefficient : ℂ) :
    stageEightMatterAction
        (configuration.withGeometrySpin
          (configuration.geometry.spinAction + coefficient • variation)) =
      stageEightMatterAction configuration +
        coefficient * stageEightSpinStress configuration variation := by
  change
    configuration.geometry.volume *
        configuration.conjugateMatter
          (stageEightEquationVector
            (configuration.withGeometrySpin
              (configuration.geometry.spinAction + coefficient • variation))) =
      configuration.geometry.volume *
          configuration.conjugateMatter
            (stageEightEquationVector configuration) +
        coefficient *
          (configuration.geometry.volume *
            configuration.conjugateMatter
              (Complex.I •
                ∑ direction : LorentzianIndex,
                  configuration.geometry.gammaAction direction
                    (variation direction configuration.sourceMatter)))
  rw [stageEightEquationVector_withGeometrySpin, map_add, map_smul]
  ring

/-! ## Field equations -/

structure StageEightFieldEquations
    (configuration : StageEightVariationConfiguration) : Prop where
  sourceMatter : stageEightSourceEquation configuration = 0
  targetMatter : stageEightTargetEquation configuration = 0
  conjugateMatter : stageEightConjugateEquationVector configuration = 0
  breakingScalar : stageEightBreakingEquation configuration = 0
  motherConnection : stageEightMotherCurrent configuration = 0
  geometryVolume : stageEightVolumeStress configuration = 0
  geometryGamma : stageEightGammaStress configuration = 0
  geometrySpin : stageEightSpinStress configuration = 0

end
end SaturationMonoid.PhysicsCore.SU7ExteriorMatterFullVariations
