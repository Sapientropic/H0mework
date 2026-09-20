import H0mework.Physics.GaugeSource.ReducedEntropyDescent

/-!
# Generic compact-variation API for reduced P286 dynamics

This module abstracts the reduced quartic calculation from the particular
origin window.  The algebraic base is still generated canonically by the
source constitutive readout, while the only additional datum is one genuine
compact smooth primitive connection variation.  It generates its raw
connection path, curvature jet, constitutive recomputation, exact quartic
relative action, and four integrable coefficients.

The API does not choose a variation and does not assert descent.  Centered or
other source-owned material windows may instantiate it; the first coefficient
must then be identified from that exact variation.
-/

namespace SaturationMonoid.PhysicsCore
namespace StageNineP286SourceNativeReducedCompactVariation

open MeasureTheory
open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeMotherAction
open StageNineFormNativeP286GaugeConnectionIntegratedVariation
open StageNineFormNativeP286GaugeConnectionLocalVariation
open StageNineFormNativeP286GaugeConstitutiveEliminationRegularity
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286SourceNativeReducedEntropyDescent
open StageNineTopologicalFourFormPairing
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance reducedCompactP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286SourceNativeReducedEntropyDescent.reducedEntropyP286ModuleFinite

local instance reducedCompactP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286SourceNativeReducedEntropyDescent.reducedEntropyP286CoordinateIndexFintype

local instance reducedCompactP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def p286ReducedCompactRawPath
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (parameter : ℝ) : StageNineHolonomicConfiguration :=
  varyP286GaugeConnectionCoordinate (p286ReducedEntropyBase source current)
    variation parameter

def p286ReducedCompactJointPath
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (parameter : ℝ) : StageNineHolonomicConfiguration :=
  formNativeP286GaugeConstitutiveReadout source
    (p286ReducedCompactRawPath source current variation parameter)

def p286ReducedCompactLinearCurvature
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (point : BasePoint) : FormNativeP286GaugeCoordinateTwoForm :=
  p286GaugeConnectionLinearCurvatureVariation
    (p286ReducedEntropyBase source current) variation point

def p286ReducedCompactQuadraticCurvature
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (point : BasePoint) : FormNativeP286GaugeCoordinateTwoForm :=
  p286GaugeConnectionQuadraticCurvatureVariation variation point

def p286ReducedCompactLocalFirstCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (point : BasePoint) : ℝ :=
  holonomicFormNativeP286GaugeConnectionFirstVariationDensity source 0
    (p286ReducedEntropyBase source current) variation point

def p286ReducedCompactLocalSecondCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (point : BasePoint) : ℝ :=
  let base := p286ReducedEntropyBase source current
  let linear := p286ReducedCompactLinearCurvature source current variation point
  let quadratic := p286ReducedCompactQuadraticCurvature variation point
  holonomicFormNativeP286GaugeConnectionSecondVariationDensity source 0 base
      variation point -
    formNativeP286GaugeConnectionBFFirstVariationDensity
      (toContinuumPointField base point) quadratic +
    p286ReducedGaugeSecondCoefficient (sourceGeneratedUnifiedCouplings source)
      (base.coframe point)
      (holonomicP286GaugeCurvatureCoordinate base point) linear quadratic

def p286ReducedCompactLocalThirdCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (point : BasePoint) : ℝ :=
  p286ReducedGaugeThirdCoefficient (sourceGeneratedUnifiedCouplings source)
    ((p286ReducedEntropyBase source current).coframe point)
    (p286ReducedCompactLinearCurvature source current variation point)
    (p286ReducedCompactQuadraticCurvature variation point)

def p286ReducedCompactLocalFourthCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (point : BasePoint) : ℝ :=
  p286ReducedGaugeFourthCoefficient (sourceGeneratedUnifiedCouplings source)
    ((p286ReducedEntropyBase source current).coframe point)
    (p286ReducedCompactQuadraticCurvature variation point)

theorem p286ReducedCompactRawPath_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (parameter : ℝ) :
    (p286ReducedCompactRawPath source current variation parameter
      ).Nondegenerate := by
  intro point
  change Matrix.det ((p286ReducedEntropyBase source current).coframe point) ≠ 0
  exact p286ReducedEntropyBase_nondegenerate source current nondegenerate point

theorem p286ReducedCompactRawLocalDensity_quadratic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (parameter : ℝ)
    (point : BasePoint) :
    sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField
          (p286ReducedCompactRawPath source current variation parameter)
          point) =
      sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField (p286ReducedEntropyBase source current)
            point) +
        parameter *
          p286ReducedCompactLocalFirstCoefficient source current variation
            point +
        parameter ^ 2 *
          holonomicFormNativeP286GaugeConnectionSecondVariationDensity source
            0 (p286ReducedEntropyBase source current) variation point := by
  exact holonomicFormNativeUnifiedLocalDensity_p286Connection_quadratic
    source 0 (p286ReducedEntropyBase source current)
    (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
    variation parameter point

theorem p286ReducedCompactRawGaugeDensity_quadratic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (parameter : ℝ)
    (point : BasePoint) :
    generatedFormNativeGaugeDensityAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        (toContinuumPointField
          (p286ReducedCompactRawPath source current variation parameter)
          point) =
      generatedFormNativeGaugeDensityAtBoundary
          (sourceGeneratedUnifiedCouplings source)
          (toContinuumPointField (p286ReducedEntropyBase source current)
            point) +
        parameter *
          formNativeP286GaugeConnectionBFFirstVariationDensity
            (toContinuumPointField (p286ReducedEntropyBase source current)
              point)
            (p286ReducedCompactLinearCurvature source current variation
              point) +
        parameter ^ 2 *
          formNativeP286GaugeConnectionBFFirstVariationDensity
            (toContinuumPointField (p286ReducedEntropyBase source current)
              point)
            (p286ReducedCompactQuadraticCurvature variation point) := by
  rw [p286ReducedCompactRawPath,
    toContinuumPointField_varyP286GaugeConnectionCoordinate
      (p286ReducedEntropyBase source current)
      (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
      variation parameter point]
  unfold variedP286CurvatureCoordinate p286ReducedCompactLinearCurvature
    p286ReducedCompactQuadraticCurvature
  exact generatedFormNativeGaugeDensityAtBoundary_connectionJets_quadratic
    (sourceGeneratedUnifiedCouplings source)
    (toContinuumPointField (p286ReducedEntropyBase source current) point)
    (p286GaugeConnectionLinearCurvatureVariation
      (p286ReducedEntropyBase source current) variation point)
    (p286GaugeConnectionQuadraticCurvatureVariation variation point)
    (variedP286ScalarCovariantDerivative
      (p286ReducedEntropyBase source current) variation parameter point)
    (variedP286MatterCovariantDerivative
      (p286ReducedEntropyBase source current) variation parameter point)
    parameter

theorem p286ReducedCompactGaugeFirstCoefficient_eq_raw
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (point : BasePoint) :
    p286ReducedGaugeFirstCoefficient
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (holonomicP286GaugeCurvatureCoordinate
          (p286ReducedEntropyBase source current) point)
        (p286ReducedCompactLinearCurvature source current variation point) =
      formNativeP286GaugeConnectionBFFirstVariationDensity
        (toContinuumPointField (p286ReducedEntropyBase source current) point)
        (p286ReducedCompactLinearCurvature source current variation point) := by
  rw [p286ReducedGaugeFirstCoefficient_eq_connection
    (sourceGeneratedUnifiedCouplings source)
    ((p286ReducedEntropyBase source current).coframe point)
    (p286ReducedEntropyBase_nondegenerate source current nondegenerate point)]
  rw [← p286ReducedEntropyBase_auxiliaryCoordinate source current point]
  exact
    (formNativeP286GaugeConnectionBFFirstVariationDensity_eq_coordinate
      (toContinuumPointField (p286ReducedEntropyBase source current) point)
      (p286ReducedCompactLinearCurvature source current variation point)).symm

theorem p286ReducedCompactJointLocalDensity_quartic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (parameter : ℝ)
    (point : BasePoint) :
    sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField
          (p286ReducedCompactJointPath source current variation parameter)
          point) =
      sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField (p286ReducedEntropyBase source current)
            point) +
        parameter *
          p286ReducedCompactLocalFirstCoefficient source current variation
            point +
        parameter ^ 2 *
          p286ReducedCompactLocalSecondCoefficient source current variation
            point +
        parameter ^ 3 *
          p286ReducedCompactLocalThirdCoefficient source current variation
            point +
        parameter ^ 4 *
          p286ReducedCompactLocalFourthCoefficient source current variation
            point := by
  have jointIdentity :=
    sourceGeneratedFormNativeLocalDensity_constitutiveReadout_eq source
      (p286ReducedCompactRawPath source current variation parameter)
      (p286ReducedCompactRawPath_nondegenerate source current nondegenerate
        variation parameter) point
  change
    sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField
          (p286ReducedCompactJointPath source current variation parameter)
          point) = _ at jointIdentity
  rw [jointIdentity]
  rw [p286ReducedCompactRawLocalDensity_quadratic source current smooth
    nondegenerate variation parameter point]
  rw [p286ReducedCompactRawGaugeDensity_quadratic source current smooth
    nondegenerate variation parameter point]
  have curvatureExpansion :=
    holonomicP286GaugeCurvatureCoordinate_expansion
      (p286ReducedEntropyBase source current)
      (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
      variation parameter point
  change
    holonomicP286GaugeCurvatureCoordinate
        (p286ReducedCompactRawPath source current variation parameter) point =
      holonomicP286GaugeCurvatureCoordinate
          (p286ReducedEntropyBase source current) point +
        parameter •
          p286ReducedCompactLinearCurvature source current variation point +
        parameter ^ 2 •
          p286ReducedCompactQuadraticCurvature variation point
      at curvatureExpansion
  have reducedExpansion :
      p286ReducedGaugeDensity (sourceGeneratedUnifiedCouplings source)
          ((p286ReducedCompactRawPath source current variation parameter
            ).coframe point)
          (holonomicP286GaugeCurvatureCoordinate
            (p286ReducedCompactRawPath source current variation parameter)
            point) =
        generatedFormNativeGaugeDensityAtBoundary
            (sourceGeneratedUnifiedCouplings source)
            (toContinuumPointField (p286ReducedEntropyBase source current)
              point) +
          parameter *
            formNativeP286GaugeConnectionBFFirstVariationDensity
              (toContinuumPointField (p286ReducedEntropyBase source current)
                point)
              (p286ReducedCompactLinearCurvature source current variation
                point) +
          parameter ^ 2 *
            p286ReducedGaugeSecondCoefficient
              (sourceGeneratedUnifiedCouplings source)
              ((p286ReducedEntropyBase source current).coframe point)
              (holonomicP286GaugeCurvatureCoordinate
                (p286ReducedEntropyBase source current) point)
              (p286ReducedCompactLinearCurvature source current variation
                point)
              (p286ReducedCompactQuadraticCurvature variation point) +
          parameter ^ 3 *
            p286ReducedCompactLocalThirdCoefficient source current variation
              point +
          parameter ^ 4 *
            p286ReducedCompactLocalFourthCoefficient source current variation
              point := by
    change
      p286ReducedGaugeDensity (sourceGeneratedUnifiedCouplings source)
          ((p286ReducedEntropyBase source current).coframe point)
          (holonomicP286GaugeCurvatureCoordinate
            (p286ReducedCompactRawPath source current variation parameter)
            point) = _
    rw [curvatureExpansion, p286ReducedGaugeDensity_quartic]
    rw [← p286ReducedEntropyBaseGaugeDensity_eq_reduced source current
      nondegenerate point]
    rw [p286ReducedCompactGaugeFirstCoefficient_eq_raw source current
      nondegenerate variation point]
    rfl
  rw [reducedExpansion]
  unfold p286ReducedCompactLocalSecondCoefficient
    p286ReducedCompactLocalThirdCoefficient
    p286ReducedCompactLocalFourthCoefficient
  dsimp only
  ring

/-! ## Generic compact coefficient regularity -/

private theorem p286ReducedCompactLinearCurvature_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous
      (p286ReducedCompactLinearCurvature source current variation) :=
  p286GaugeConnectionLinearCurvatureVariation_continuous
    (p286ReducedEntropyBase source current)
    (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
    variation

private theorem p286ReducedCompactQuadraticCurvature_continuous
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous (p286ReducedCompactQuadraticCurvature variation) :=
  p286GaugeConnectionQuadraticCurvatureVariation_continuous variation

private theorem p286ReducedCompactEliminatedLinear_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (p286ReducedCompactLinearCurvature source current variation point) :=
  p286EliminatedAuxiliaryCoordinate_continuous
    (sourceGeneratedUnifiedCouplings source)
    (p286ReducedEntropyBase source current).coframe
    (p286ReducedCompactLinearCurvature source current variation)
    (p286ReducedEntropyCoframe_continuous source current smooth nondegenerate)
    (p286ReducedEntropyBase_nondegenerate source current nondegenerate)
    (p286ReducedCompactLinearCurvature_continuous source current smooth
      nondegenerate variation)

private theorem p286ReducedCompactEliminatedQuadratic_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (p286ReducedCompactQuadraticCurvature variation point) :=
  p286EliminatedAuxiliaryCoordinate_continuous
    (sourceGeneratedUnifiedCouplings source)
    (p286ReducedEntropyBase source current).coframe
    (p286ReducedCompactQuadraticCurvature variation)
    (p286ReducedEntropyCoframe_continuous source current smooth nondegenerate)
    (p286ReducedEntropyBase_nondegenerate source current nondegenerate)
    (p286ReducedCompactQuadraticCurvature_continuous variation)

theorem p286ReducedCompactLocalThirdCoefficient_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous (p286ReducedCompactLocalThirdCoefficient source current
      variation) := by
  have firstWedge := p286CoordinateWedge_continuous
    (fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (p286ReducedCompactLinearCurvature source current variation point))
    (p286ReducedCompactQuadraticCurvature variation)
    (p286ReducedCompactEliminatedLinear_continuous source current smooth
      nondegenerate variation)
    (p286ReducedCompactQuadraticCurvature_continuous variation)
  have secondWedge := p286CoordinateWedge_continuous
    (fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (p286ReducedCompactQuadraticCurvature variation point))
    (p286ReducedCompactLinearCurvature source current variation)
    (p286ReducedCompactEliminatedQuadratic_continuous source current smooth
      nondegenerate variation)
    (p286ReducedCompactLinearCurvature_continuous source current smooth
      nondegenerate variation)
  change Continuous fun point =>
    (1 / 2 : ℝ) *
      (generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
          (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
            (sourceGeneratedUnifiedCouplings source)
            ((p286ReducedEntropyBase source current).coframe point)
            (p286ReducedCompactLinearCurvature source current variation point))
          (p286ReducedCompactQuadraticCurvature variation point) +
        generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
          (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
            (sourceGeneratedUnifiedCouplings source)
            ((p286ReducedEntropyBase source current).coframe point)
            (p286ReducedCompactQuadraticCurvature variation point))
          (p286ReducedCompactLinearCurvature source current variation point))
  exact continuous_const.mul (firstWedge.add secondWedge)

theorem p286ReducedCompactLocalFourthCoefficient_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous (p286ReducedCompactLocalFourthCoefficient source current
      variation) := by
  have wedge := p286CoordinateWedge_continuous
    (fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        ((p286ReducedEntropyBase source current).coframe point)
        (p286ReducedCompactQuadraticCurvature variation point))
    (p286ReducedCompactQuadraticCurvature variation)
    (p286ReducedCompactEliminatedQuadratic_continuous source current smooth
      nondegenerate variation)
    (p286ReducedCompactQuadraticCurvature_continuous variation)
  change Continuous fun point =>
    (1 / 2 : ℝ) *
      generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
        (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
          (sourceGeneratedUnifiedCouplings source)
          ((p286ReducedEntropyBase source current).coframe point)
          (p286ReducedCompactQuadraticCurvature variation point))
        (p286ReducedCompactQuadraticCurvature variation point)
  exact continuous_const.mul wedge

theorem p286ReducedCompactLocalSecondCoefficient_continuous
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Continuous (p286ReducedCompactLocalSecondCoefficient source current
      variation) := by
  let base := p286ReducedEntropyBase source current
  have rawSecond :=
    holonomicFormNativeP286GaugeConnectionSecondVariationDensity_continuous
      source base (p286ReducedEntropyBase_smooth source current smooth
        nondegenerate)
      (p286ReducedEntropyBase_nondegenerate source current nondegenerate)
      variation
  have rawGaugeQuadratic :=
    holonomicFormNativeP286GaugeConnectionBFSecondDensity_continuous base
      (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
      variation
  have baseQuadraticWedge := p286CoordinateWedge_continuous
    (fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source) (base.coframe point)
        (holonomicP286GaugeCurvatureCoordinate base point))
    (p286ReducedCompactQuadraticCurvature variation)
    (p286ReducedEntropyEliminatedBase_continuous source current smooth
      nondegenerate)
    (p286ReducedCompactQuadraticCurvature_continuous variation)
  have linearLinearWedge := p286CoordinateWedge_continuous
    (fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source) (base.coframe point)
        (p286ReducedCompactLinearCurvature source current variation point))
    (p286ReducedCompactLinearCurvature source current variation)
    (p286ReducedCompactEliminatedLinear_continuous source current smooth
      nondegenerate variation)
    (p286ReducedCompactLinearCurvature_continuous source current smooth
      nondegenerate variation)
  have quadraticBaseWedge := p286CoordinateWedge_continuous
    (fun point =>
      formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
        (sourceGeneratedUnifiedCouplings source) (base.coframe point)
        (p286ReducedCompactQuadraticCurvature variation point))
    (holonomicP286GaugeCurvatureCoordinate base)
    (p286ReducedCompactEliminatedQuadratic_continuous source current smooth
      nondegenerate variation)
    (p286ReducedEntropyCurvature_continuous source current smooth
      nondegenerate)
  have reducedSecond : Continuous fun point =>
      (1 / 2 : ℝ) *
        (generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
              (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
                (sourceGeneratedUnifiedCouplings source) (base.coframe point)
                (holonomicP286GaugeCurvatureCoordinate base point))
              (p286ReducedCompactQuadraticCurvature variation point) +
          generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
              (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
                (sourceGeneratedUnifiedCouplings source) (base.coframe point)
                (p286ReducedCompactLinearCurvature source current variation
                  point))
              (p286ReducedCompactLinearCurvature source current variation
                point) +
            generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
              (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
                (sourceGeneratedUnifiedCouplings source) (base.coframe point)
                (p286ReducedCompactQuadraticCurvature variation point))
              (holonomicP286GaugeCurvatureCoordinate base point)) :=
    continuous_const.mul
      ((baseQuadraticWedge.add linearLinearWedge).add quadraticBaseWedge)
  change Continuous fun point =>
    holonomicFormNativeP286GaugeConnectionSecondVariationDensity source 0
          base variation point -
        formNativeP286GaugeConnectionBFFirstVariationDensity
          (toContinuumPointField base point)
          (p286ReducedCompactQuadraticCurvature variation point) +
      (1 / 2 : ℝ) *
        (generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
              (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
                (sourceGeneratedUnifiedCouplings source) (base.coframe point)
                (holonomicP286GaugeCurvatureCoordinate base point))
              (p286ReducedCompactQuadraticCurvature variation point) +
          generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
              (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
                (sourceGeneratedUnifiedCouplings source) (base.coframe point)
                (p286ReducedCompactLinearCurvature source current variation
                  point))
              (p286ReducedCompactLinearCurvature source current variation
                point) +
            generatedTwoFormWedgeCoefficient p286CoordinateLiePairing
              (formNativeP286GaugeEliminatedAuxiliaryCoordinateAtBoundary
                (sourceGeneratedUnifiedCouplings source) (base.coframe point)
                (p286ReducedCompactQuadraticCurvature variation point))
              (holonomicP286GaugeCurvatureCoordinate base point))
  exact (rawSecond.sub rawGaugeQuadratic).add reducedSecond

theorem p286ReducedCompactLocalFirstCoefficient_compact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    HasCompactSupport
      (p286ReducedCompactLocalFirstCoefficient source current variation) :=
  holonomicFormNativeP286GaugeConnectionFirstVariationDensity_compact source 0
    (p286ReducedEntropyBase source current) variation

theorem p286ReducedCompactLocalSecondCoefficient_compact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    HasCompactSupport
      (p286ReducedCompactLocalSecondCoefficient source current variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  filter_upwards
    [compactP286GaugeConnectionVariation_eventually_jet_zero variation] with
    point jetZero
  have linearZero :
      p286ReducedCompactLinearCurvature source current variation point = 0 :=
    p286GaugeConnectionLinearCurvatureVariation_eq_zero_of_jet_zero
      (p286ReducedEntropyBase source current) variation point jetZero.1
      jetZero.2
  have quadraticZero :
      p286ReducedCompactQuadraticCurvature variation point = 0 :=
    p286GaugeConnectionQuadraticCurvatureVariation_eq_zero variation point
      jetZero.1
  unfold p286ReducedCompactLocalSecondCoefficient
  dsimp only
  rw [holonomicFormNativeP286GaugeConnectionSecondVariationDensity_eq_zero
    source 0 (p286ReducedEntropyBase source current) variation point
    jetZero.1]
  rw [linearZero, quadraticZero]
  simp [p286ReducedGaugeSecondCoefficient,
    formNativeP286GaugeConnectionBFFirstVariationDensity]

theorem p286ReducedCompactLocalThirdCoefficient_compact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    HasCompactSupport
      (p286ReducedCompactLocalThirdCoefficient source current variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  filter_upwards
    [compactP286GaugeConnectionVariation_eventually_jet_zero variation] with
    point jetZero
  have linearZero :
      p286ReducedCompactLinearCurvature source current variation point = 0 :=
    p286GaugeConnectionLinearCurvatureVariation_eq_zero_of_jet_zero
      (p286ReducedEntropyBase source current) variation point jetZero.1
      jetZero.2
  have quadraticZero :
      p286ReducedCompactQuadraticCurvature variation point = 0 :=
    p286GaugeConnectionQuadraticCurvatureVariation_eq_zero variation point
      jetZero.1
  unfold p286ReducedCompactLocalThirdCoefficient
  rw [linearZero, quadraticZero]
  simp [p286ReducedGaugeThirdCoefficient]

theorem p286ReducedCompactLocalFourthCoefficient_compact
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    HasCompactSupport
      (p286ReducedCompactLocalFourthCoefficient source current variation) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  filter_upwards
    [compactP286GaugeConnectionVariation_eventually_jet_zero variation] with
    point jetZero
  have quadraticZero :
      p286ReducedCompactQuadraticCurvature variation point = 0 :=
    p286GaugeConnectionQuadraticCurvatureVariation_eq_zero variation point
      jetZero.1
  unfold p286ReducedCompactLocalFourthCoefficient
  rw [quadraticZero]
  simp [p286ReducedGaugeFourthCoefficient]

theorem p286ReducedCompactLocalFirstCoefficient_integrable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Integrable
      (p286ReducedCompactLocalFirstCoefficient source current variation) :=
  holonomicFormNativeP286GaugeConnectionFirstVariationDensity_integrable
    source (p286ReducedEntropyBase source current)
    (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
    (p286ReducedEntropyBase_nondegenerate source current nondegenerate)
    variation

theorem p286ReducedCompactLocalSecondCoefficient_integrable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Integrable
      (p286ReducedCompactLocalSecondCoefficient source current variation) :=
  (p286ReducedCompactLocalSecondCoefficient_continuous source current smooth
    nondegenerate variation).integrable_of_hasCompactSupport
      (p286ReducedCompactLocalSecondCoefficient_compact source current
        variation)

theorem p286ReducedCompactLocalThirdCoefficient_integrable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Integrable
      (p286ReducedCompactLocalThirdCoefficient source current variation) :=
  (p286ReducedCompactLocalThirdCoefficient_continuous source current smooth
    nondegenerate variation).integrable_of_hasCompactSupport
      (p286ReducedCompactLocalThirdCoefficient_compact source current
        variation)

theorem p286ReducedCompactLocalFourthCoefficient_integrable
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) :
    Integrable
      (p286ReducedCompactLocalFourthCoefficient source current variation) :=
  (p286ReducedCompactLocalFourthCoefficient_continuous source current smooth
    nondegenerate variation).integrable_of_hasCompactSupport
      (p286ReducedCompactLocalFourthCoefficient_compact source current
        variation)

theorem p286Integral_quartic
    (first second third fourth : BasePoint → ℝ)
    (firstIntegrable : Integrable first)
    (secondIntegrable : Integrable second)
    (thirdIntegrable : Integrable third)
    (fourthIntegrable : Integrable fourth)
    (parameter : ℝ) :
    (∫ point : BasePoint,
      parameter * first point + parameter ^ 2 * second point +
        parameter ^ 3 * third point + parameter ^ 4 * fourth point) =
      parameter * (∫ point : BasePoint, first point) +
        parameter ^ 2 * (∫ point : BasePoint, second point) +
        parameter ^ 3 * (∫ point : BasePoint, third point) +
        parameter ^ 4 * (∫ point : BasePoint, fourth point) := by
  let firstScaled := fun point : BasePoint => parameter * first point
  let secondScaled := fun point : BasePoint => parameter ^ 2 * second point
  let thirdScaled := fun point : BasePoint => parameter ^ 3 * third point
  let fourthScaled := fun point : BasePoint => parameter ^ 4 * fourth point
  have firstScaledIntegrable : Integrable firstScaled :=
    firstIntegrable.const_mul parameter
  have secondScaledIntegrable : Integrable secondScaled :=
    secondIntegrable.const_mul (parameter ^ 2)
  have thirdScaledIntegrable : Integrable thirdScaled :=
    thirdIntegrable.const_mul (parameter ^ 3)
  have fourthScaledIntegrable : Integrable fourthScaled :=
    fourthIntegrable.const_mul (parameter ^ 4)
  have firstSecond := firstScaledIntegrable.add secondScaledIntegrable
  have firstThird := firstSecond.add thirdScaledIntegrable
  change integral volume
      (((firstScaled + secondScaled) + thirdScaled) + fourthScaled) = _
  calc
    _ = integral volume ((firstScaled + secondScaled) + thirdScaled) +
          integral volume fourthScaled := by
        change (∫ point : BasePoint,
          ((firstScaled + secondScaled) + thirdScaled) point +
            fourthScaled point) = _
        exact integral_add firstThird fourthScaledIntegrable
    _ = (integral volume (firstScaled + secondScaled) +
          integral volume thirdScaled) + integral volume fourthScaled := by
        rw [show integral volume ((firstScaled + secondScaled) + thirdScaled) =
          integral volume (firstScaled + secondScaled) +
            integral volume thirdScaled by
          change (∫ point : BasePoint,
            (firstScaled + secondScaled) point + thirdScaled point) = _
          exact integral_add firstSecond thirdScaledIntegrable]
    _ = ((integral volume firstScaled + integral volume secondScaled) +
          integral volume thirdScaled) + integral volume fourthScaled := by
        rw [show integral volume (firstScaled + secondScaled) =
          integral volume firstScaled + integral volume secondScaled by
          change (∫ point : BasePoint,
            firstScaled point + secondScaled point) = _
          exact integral_add firstScaledIntegrable secondScaledIntegrable]
    _ = _ := by
      unfold firstScaled secondScaled thirdScaled fourthScaled
      rw [integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const_mul]

def p286ReducedCompactFirstCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) : ℝ :=
  ∫ point : BasePoint,
    p286ReducedCompactLocalFirstCoefficient source current variation point

def p286ReducedCompactSecondCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) : ℝ :=
  ∫ point : BasePoint,
    p286ReducedCompactLocalSecondCoefficient source current variation point

def p286ReducedCompactThirdCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) : ℝ :=
  ∫ point : BasePoint,
    p286ReducedCompactLocalThirdCoefficient source current variation point

def p286ReducedCompactFourthCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm) : ℝ :=
  ∫ point : BasePoint,
    p286ReducedCompactLocalFourthCoefficient source current variation point

def p286ReducedCompactRelativeAction
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (parameter : ℝ) : ℝ :=
  ∫ point : BasePoint,
    sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField
          (p286ReducedCompactJointPath source current variation parameter)
          point) -
      sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField (p286ReducedEntropyBase source current) point)

theorem p286ReducedCompactRelativeAction_quartic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation P286GaugeOneForm)
    (parameter : ℝ) :
    p286ReducedCompactRelativeAction source current variation parameter =
      parameter * p286ReducedCompactFirstCoefficient source current variation +
        parameter ^ 2 *
          p286ReducedCompactSecondCoefficient source current variation +
        parameter ^ 3 *
          p286ReducedCompactThirdCoefficient source current variation +
        parameter ^ 4 *
          p286ReducedCompactFourthCoefficient source current variation := by
  unfold p286ReducedCompactRelativeAction
  rw [show (fun point : BasePoint =>
      sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField
            (p286ReducedCompactJointPath source current variation parameter)
            point) -
        sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField (p286ReducedEntropyBase source current)
            point)) =
      fun point =>
        parameter *
            p286ReducedCompactLocalFirstCoefficient source current variation
              point +
          parameter ^ 2 *
            p286ReducedCompactLocalSecondCoefficient source current variation
              point +
          parameter ^ 3 *
            p286ReducedCompactLocalThirdCoefficient source current variation
              point +
          parameter ^ 4 *
            p286ReducedCompactLocalFourthCoefficient source current variation
              point by
    funext point
    rw [p286ReducedCompactJointLocalDensity_quartic source current smooth
      nondegenerate variation parameter point]
    ring]
  rw [p286Integral_quartic
    (p286ReducedCompactLocalFirstCoefficient source current variation)
    (p286ReducedCompactLocalSecondCoefficient source current variation)
    (p286ReducedCompactLocalThirdCoefficient source current variation)
    (p286ReducedCompactLocalFourthCoefficient source current variation)
    (p286ReducedCompactLocalFirstCoefficient_integrable source current smooth
      nondegenerate variation)
    (p286ReducedCompactLocalSecondCoefficient_integrable source current smooth
      nondegenerate variation)
    (p286ReducedCompactLocalThirdCoefficient_integrable source current smooth
      nondegenerate variation)
    (p286ReducedCompactLocalFourthCoefficient_integrable source current smooth
      nondegenerate variation) parameter]
  rfl

end
end StageNineP286SourceNativeReducedCompactVariation
end PhysicsCore
end SaturationMonoid
