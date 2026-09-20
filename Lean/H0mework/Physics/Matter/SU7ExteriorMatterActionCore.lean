import H0mework.Physics.Matter.SU7ExteriorYukawaMassSpectrum

/-!
# Stage-8D finite-link matter action core

This module defines the Stage-8 matter action together with its field-replacement operations:
source/target/conjugate matter, the actual `Λ⁴V` breaking scalar, the finite
mother-connection link transport, and the finite geometry readouts (volume,
inverse-coframe Clifford action, and spin action).  Each first-variation law is
an exact affine identity for every complex coefficient.

The construction stays inside the finite-link jurisdiction established by
Stage 8A.  It therefore does not claim a smooth Fréchet derivative with respect
to an underlying coframe bundle.  No reference-SM mass table, arbitrary mass
matrix, or stored equivariance Boolean is consumed.
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

abbrev DiracMatterEnd := Module.End ℂ DiracExteriorMatterCarrier

structure StageEightMatterGeometryReadout where
  volume : ℂ
  gammaAction : LorentzianIndex → DiracMatterEnd
  spinAction : LorentzianIndex → DiracMatterEnd

structure StageEightVariationConfiguration where
  geometry : StageEightMatterGeometryReadout
  motherTransport : LorentzianIndex → DiracMatterEnd
  sourceMatter : DiracExteriorMatterCarrier
  targetMatter : LorentzianIndex → DiracExteriorMatterCarrier
  conjugateMatter : Module.Dual ℂ DiracExteriorMatterCarrier
  breakingScalar : ExteriorBreakingScalarCarrier

def stageEightKineticResidual
    (configuration : StageEightVariationConfiguration)
    (direction : LorentzianIndex) : DiracExteriorMatterCarrier :=
  configuration.motherTransport direction
      (configuration.targetMatter direction) -
    configuration.sourceMatter +
    configuration.geometry.spinAction direction
      configuration.sourceMatter

def stageEightKineticVector
    (configuration : StageEightVariationConfiguration) :
    DiracExteriorMatterCarrier :=
  Complex.I •
    ∑ direction : LorentzianIndex,
      configuration.geometry.gammaAction direction
        (stageEightKineticResidual configuration direction)

def stageEightYukawaVector
    (configuration : StageEightVariationConfiguration) :
    DiracExteriorMatterCarrier :=
  chiralExteriorYukawaAction configuration.breakingScalar
    configuration.sourceMatter

def stageEightEquationVector
    (configuration : StageEightVariationConfiguration) :
    DiracExteriorMatterCarrier :=
  stageEightKineticVector configuration +
    stageEightYukawaVector configuration

def stageEightMatterAction
    (configuration : StageEightVariationConfiguration) : ℂ :=
  configuration.geometry.volume *
    configuration.conjugateMatter
      (stageEightEquationVector configuration)

def stageEightGeometryReadoutOfActual
    (geometry : PointwiseLorentzianCoframeJet) :
    StageEightMatterGeometryReadout where
  volume := ((abs (Matrix.det geometry.coframe) : ℝ) : ℂ)
  gammaAction := fun direction =>
    diracMatrixMatterAction
      (inverseCoframeDiracGamma geometry direction)
  spinAction := fun direction =>
    diracSpinConnectionMatterAction geometry direction

def stageEightVariationConfigurationOfActual
    (geometry : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (matter : DiracExteriorMatterLinkJet)
    (breakingScalar : ExteriorBreakingScalarCarrier) :
    StageEightVariationConfiguration where
  geometry := stageEightGeometryReadoutOfActual geometry
  motherTransport := fun direction =>
    diracExteriorLinkAction
      (motherLinkFamilyOfConnection connection direction)
  sourceMatter := matter.sourceField
  targetMatter := matter.targetField
  conjugateMatter := matter.sourceConjugateField
  breakingScalar := breakingScalar

def stageEightActualYukawaDensity
    (geometry : PointwiseLorentzianCoframeJet)
    (matter : DiracExteriorMatterLinkJet)
    (breakingScalar : ExteriorBreakingScalarCarrier) : ℂ :=
  ((abs (Matrix.det geometry.coframe) : ℝ) : ℂ) *
    matter.sourceConjugateField
      (chiralExteriorYukawaAction breakingScalar matter.sourceField)

/-! ## Field replacements -/

def StageEightVariationConfiguration.withSourceMatter
    (configuration : StageEightVariationConfiguration)
    (sourceMatter : DiracExteriorMatterCarrier) :
    StageEightVariationConfiguration :=
  { configuration with sourceMatter := sourceMatter }

def StageEightVariationConfiguration.withTargetMatter
    (configuration : StageEightVariationConfiguration)
    (targetMatter : LorentzianIndex → DiracExteriorMatterCarrier) :
    StageEightVariationConfiguration :=
  { configuration with targetMatter := targetMatter }

def StageEightVariationConfiguration.withConjugateMatter
    (configuration : StageEightVariationConfiguration)
    (conjugateMatter : Module.Dual ℂ DiracExteriorMatterCarrier) :
    StageEightVariationConfiguration :=
  { configuration with conjugateMatter := conjugateMatter }

def StageEightVariationConfiguration.withBreakingScalar
    (configuration : StageEightVariationConfiguration)
    (breakingScalar : ExteriorBreakingScalarCarrier) :
    StageEightVariationConfiguration :=
  { configuration with breakingScalar := breakingScalar }

def StageEightVariationConfiguration.withMotherTransport
    (configuration : StageEightVariationConfiguration)
    (motherTransport : LorentzianIndex → DiracMatterEnd) :
    StageEightVariationConfiguration :=
  { configuration with motherTransport := motherTransport }

def StageEightVariationConfiguration.withGeometryVolume
    (configuration : StageEightVariationConfiguration)
    (volume : ℂ) : StageEightVariationConfiguration :=
  { configuration with geometry :=
      { configuration.geometry with volume := volume } }

def StageEightVariationConfiguration.withGeometryGamma
    (configuration : StageEightVariationConfiguration)
    (gammaAction : LorentzianIndex → DiracMatterEnd) :
    StageEightVariationConfiguration :=
  { configuration with geometry :=
      { configuration.geometry with gammaAction := gammaAction } }

def StageEightVariationConfiguration.withGeometrySpin
    (configuration : StageEightVariationConfiguration)
    (spinAction : LorentzianIndex → DiracMatterEnd) :
    StageEightVariationConfiguration :=
  { configuration with geometry :=
      { configuration.geometry with spinAction := spinAction } }

/-! ## Actual Stage-8A/8B action adapter -/

theorem stageEightMatterAction_ofActual_eq_link_add_yukawa
    (geometry : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (matter : DiracExteriorMatterLinkJet)
    (breakingScalar : ExteriorBreakingScalarCarrier) :
    stageEightMatterAction
        (stageEightVariationConfigurationOfActual
          geometry connection matter breakingScalar) =
      diracExteriorMatterLinkActionDensity geometry
        (motherLinkFamilyOfConnection connection) matter +
      stageEightActualYukawaDensity geometry matter breakingScalar := by
  change
    ((abs (Matrix.det geometry.coframe) : ℝ) : ℂ) *
        matter.sourceConjugateField
          (diracExteriorMatterLinkKineticVector geometry
              (motherLinkFamilyOfConnection connection) matter +
            chiralExteriorYukawaAction breakingScalar matter.sourceField) =
      ((abs (Matrix.det geometry.coframe) : ℝ) : ℂ) *
          matter.sourceConjugateField
            (diracExteriorMatterLinkKineticVector geometry
              (motherLinkFamilyOfConnection connection) matter) +
        ((abs (Matrix.det geometry.coframe) : ℝ) : ℂ) *
          matter.sourceConjugateField
            (chiralExteriorYukawaAction breakingScalar matter.sourceField)
  rw [map_add, mul_add]
end
end SaturationMonoid.PhysicsCore.SU7ExteriorMatterFullVariations
