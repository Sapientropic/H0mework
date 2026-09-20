import H0mework.Physics.Matter.SU7ExteriorMatterActionCore

/-!
# Stage-8D finite-link equation and source core

This module defines the source/target/conjugate matter equations, proves
linearity of the actual exterior Yukawa action in the Λ⁴V breaking scalar, and
defines the breaking equation, mother current, and volume/gamma/spin geometry
sources.  These are the coefficients consumed by the exact affine variation
modules; no equation Boolean or reference-model table is stored.
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

/-! ## Linearized vectors and equation functionals -/

def stageEightSourceLinearizedVector
    (configuration : StageEightVariationConfiguration)
    (variation : DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  Complex.I •
      ∑ direction : LorentzianIndex,
        configuration.geometry.gammaAction direction
          (-variation +
            configuration.geometry.spinAction direction variation) +
    chiralExteriorYukawaAction configuration.breakingScalar variation

def stageEightSourceEquation
    (configuration : StageEightVariationConfiguration)
    (variation : DiracExteriorMatterCarrier) : ℂ :=
  configuration.geometry.volume *
    configuration.conjugateMatter
      (stageEightSourceLinearizedVector configuration variation)

def stageEightTargetLinearizedVector
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  Complex.I •
    ∑ direction : LorentzianIndex,
      configuration.geometry.gammaAction direction
        (configuration.motherTransport direction
          (variation direction))

def stageEightTargetEquation
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracExteriorMatterCarrier) : ℂ :=
  configuration.geometry.volume *
    configuration.conjugateMatter
      (stageEightTargetLinearizedVector configuration variation)

def stageEightConjugateEquationVector
    (configuration : StageEightVariationConfiguration) :
    DiracExteriorMatterCarrier :=
  configuration.geometry.volume •
    stageEightEquationVector configuration

/-! ## Breaking-scalar linearity and equation -/

theorem exteriorYukawaMassMap_add
    (first second : ExteriorBreakingScalarCarrier) :
    exteriorYukawaMassMap (first + second) =
      exteriorYukawaMassMap first + exteriorYukawaMassMap second := by
  apply LinearMap.ext
  intro matter
  change
    exteriorWedge 2 4 matter (first + second) =
      exteriorWedge 2 4 matter first + exteriorWedge 2 4 matter second
  exact map_add (exteriorWedge 2 4 matter) first second

theorem exteriorYukawaMassMap_smul
    (coefficient : ℂ) (scalar : ExteriorBreakingScalarCarrier) :
    exteriorYukawaMassMap (coefficient • scalar) =
      coefficient • exteriorYukawaMassMap scalar := by
  apply LinearMap.ext
  intro matter
  change
    exteriorWedge 2 4 matter (coefficient • scalar) =
      coefficient • exteriorWedge 2 4 matter scalar
  exact map_smul (exteriorWedge 2 4 matter) coefficient scalar

theorem exteriorYukawaInternalAction_add
    (first second : ExteriorBreakingScalarCarrier) :
    exteriorYukawaInternalAction (first + second) =
      exteriorYukawaInternalAction first +
        exteriorYukawaInternalAction second := by
  apply LinearMap.ext
  rintro ⟨degreeSix, degreeTwo, degreeFour⟩
  apply Prod.ext
  · exact LinearMap.congr_fun (exteriorYukawaMassMap_add first second)
      degreeTwo
  · simp [exteriorYukawaInternalAction]

theorem exteriorYukawaInternalAction_smul
    (coefficient : ℂ) (scalar : ExteriorBreakingScalarCarrier) :
    exteriorYukawaInternalAction (coefficient • scalar) =
      coefficient • exteriorYukawaInternalAction scalar := by
  apply LinearMap.ext
  rintro ⟨degreeSix, degreeTwo, degreeFour⟩
  apply Prod.ext
  · exact LinearMap.congr_fun
      (exteriorYukawaMassMap_smul coefficient scalar) degreeTwo
  · simp [exteriorYukawaInternalAction]

theorem diracExteriorYukawaInternalAction_add
    (first second : ExteriorBreakingScalarCarrier) :
    diracExteriorYukawaInternalAction (first + second) =
      diracExteriorYukawaInternalAction first +
        diracExteriorYukawaInternalAction second := by
  apply LinearMap.ext
  intro field
  funext spinIndex
  exact LinearMap.congr_fun (exteriorYukawaInternalAction_add first second)
    (field spinIndex)

theorem diracExteriorYukawaInternalAction_smul
    (coefficient : ℂ) (scalar : ExteriorBreakingScalarCarrier) :
    diracExteriorYukawaInternalAction (coefficient • scalar) =
      coefficient • diracExteriorYukawaInternalAction scalar := by
  apply LinearMap.ext
  intro field
  funext spinIndex
  exact LinearMap.congr_fun
    (exteriorYukawaInternalAction_smul coefficient scalar) (field spinIndex)

theorem chiralExteriorYukawaAction_add
    (first second : ExteriorBreakingScalarCarrier) :
    chiralExteriorYukawaAction (first + second) =
      chiralExteriorYukawaAction first +
        chiralExteriorYukawaAction second := by
  apply LinearMap.ext
  intro field
  change
    diracMatrixMatterAction leftChiralityProjector
        (diracMatrixMatterAction (diracGamma 0)
          (diracExteriorYukawaInternalAction (first + second)
            (diracMatrixMatterAction rightChiralityProjector field))) =
      diracMatrixMatterAction leftChiralityProjector
          (diracMatrixMatterAction (diracGamma 0)
            (diracExteriorYukawaInternalAction first
              (diracMatrixMatterAction rightChiralityProjector field))) +
        diracMatrixMatterAction leftChiralityProjector
          (diracMatrixMatterAction (diracGamma 0)
            (diracExteriorYukawaInternalAction second
              (diracMatrixMatterAction rightChiralityProjector field)))
  rw [LinearMap.congr_fun (diracExteriorYukawaInternalAction_add first second)]
  rw [LinearMap.add_apply, map_add, map_add]

theorem chiralExteriorYukawaAction_smul
    (coefficient : ℂ)
    (scalar : ExteriorBreakingScalarCarrier) :
    chiralExteriorYukawaAction (coefficient • scalar) =
      coefficient • chiralExteriorYukawaAction scalar := by
  apply LinearMap.ext
  intro field
  change
    diracMatrixMatterAction leftChiralityProjector
        (diracMatrixMatterAction (diracGamma 0)
          (diracExteriorYukawaInternalAction (coefficient • scalar)
            (diracMatrixMatterAction rightChiralityProjector field))) =
      coefficient •
        diracMatrixMatterAction leftChiralityProjector
          (diracMatrixMatterAction (diracGamma 0)
            (diracExteriorYukawaInternalAction scalar
              (diracMatrixMatterAction rightChiralityProjector field)))
  rw [LinearMap.congr_fun
    (diracExteriorYukawaInternalAction_smul coefficient scalar)]
  rw [LinearMap.smul_apply, map_smul, map_smul]

def stageEightBreakingEquation
    (configuration : StageEightVariationConfiguration)
    (variation : ExteriorBreakingScalarCarrier) : ℂ :=
  configuration.geometry.volume *
    configuration.conjugateMatter
      (chiralExteriorYukawaAction variation
        configuration.sourceMatter)

/-! ## Mother current and geometry sources -/

def stageEightMotherCurrent
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracMatterEnd) : ℂ :=
  configuration.geometry.volume *
    configuration.conjugateMatter
      (Complex.I •
        ∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (variation direction
              (configuration.targetMatter direction)))

def stageEightVolumeStress
    (configuration : StageEightVariationConfiguration) : ℂ :=
  configuration.conjugateMatter
    (stageEightEquationVector configuration)

def stageEightGammaStress
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracMatterEnd) : ℂ :=
  configuration.geometry.volume *
    configuration.conjugateMatter
      (Complex.I •
        ∑ direction : LorentzianIndex,
          variation direction
            (stageEightKineticResidual configuration direction))

def stageEightSpinStress
    (configuration : StageEightVariationConfiguration)
    (variation : LorentzianIndex → DiracMatterEnd) : ℂ :=
  configuration.geometry.volume *
    configuration.conjugateMatter
      (Complex.I •
        ∑ direction : LorentzianIndex,
          configuration.geometry.gammaAction direction
            (variation direction configuration.sourceMatter))

end
end SaturationMonoid.PhysicsCore.SU7ExteriorMatterFullVariations
