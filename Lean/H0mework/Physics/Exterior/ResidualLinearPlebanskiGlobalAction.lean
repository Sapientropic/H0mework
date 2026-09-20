import H0mework.Physics.Geometry.IIPlusRestriction
import H0mework.Physics.Coframe.CoframeTwoFormPairing

/-!
# S9-J0-A1: global residual-linear Plebanski action and actual `II+` restriction

This module opens the positive side of the gravity formulation-jurisdiction
gate.  It defines the branch-selected residual-linear candidate action

`S_BF,χ + ⟨λ, B - II+(e)⟩ + S_m`

on the existing global Stage-9 field carrier.  The wedge pairing is represented
by the dynamical coframe pairing with exactly one spacetime Hodge.  Its
coefficient is fixed to one by the existing local-action convention; no new
coupling, source slot, branch receipt, residual value, or fixed `U*` enters.

The main theorem restricts the same global action along the computed nonlinear
substitution `B := II+(e)` and identifies the resulting Bochner integral with
the reduced BF--matter integral.  This is an action-provenance / reduction
seam.  It is not yet a first-variation chain rule, reaction uniqueness,
Lorentz covariance, Einstein--Cartan critical-locus equivalence, finite-action
receipt, stationarity theorem, or source-generated solution.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineResidualLinearPlebanskiGlobalAction

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineCoframeTwoFormPairing
open EmpiricalReferenceScaleCouplingBoundary
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

/-! Preserve the historical namespace surface while the actual restriction
implementation now belongs to the formulation-neutral module. -/
export StageNineIIPlusRestriction
  (restrictContinuumPointFieldToIIPlus
    restrictContinuumPointFieldToIIPlus_coframe
    restrictContinuumPointFieldToIIPlus_gravityAuxiliary
    restrictContinuumPointFieldToIIPlus_multiplier
    restrictContinuumFieldSectionToIIPlus
    restrictHolonomicConfigurationToIIPlus
    restrictHolonomicConfigurationToIIPlus_coframe
    restrictHolonomicConfigurationToIIPlus_gravityAuxiliary
    restrictHolonomicConfigurationToIIPlus_multiplier
    toContinuumPointField_restrictHolonomicConfigurationToIIPlus
    restrictHolonomicConfigurationToIIPlus_nondegenerate_iff
    coframeWedge_contDiff
    physicalIIPlusBivector_contDiff
    restrictHolonomicConfigurationToIIPlus_smooth
    generatedGravitySimplicityResidual_restrictToIIPlus)

/-- Global residual-linear simplicity density.  The spacetime Hodge occurs
exactly once, converting the dynamical metric pairing into the form-wedge
pairing.  `physicalIIPlusBivector` already contains the internal dual. -/
def generatedGravityResidualLinearSimplicityDensity
    (field : StageNineContinuumPointField) : ℝ :=
  gravityCoframePairing field.coframe field.gravitySimplicityMultiplier
    (gravitySpacetimeHodge field.coframe
      (generatedGravitySimplicityResidual field))

/-- Candidate A local density, retaining the already generated BF, gauge,
scalar, and matter core and replacing only the historical squared simplicity
channel by the residual-linear reaction channel. -/
def generatedResidualLinearUnifiedLocalDensityAtBoundary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) : ℝ :=
  generatedVolumeDensity field *
    (generatedGravityResidualLinearSimplicityDensity field +
      generatedUnifiedLocalDensityCoreAtBoundary
        source boundary chart point field)

theorem generatedGravityResidualLinearSimplicityDensity_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    generatedGravityResidualLinearSimplicityDensity
        (transportContinuumPointField source initial terminal point field) =
      generatedGravityResidualLinearSimplicityDensity field :=
  rfl

/-- Descent through the already generated Stage-9 gauge chart transition.
This does not claim local Lorentz covariance: that action moves the coframe
and gravity fields and remains a separate J0 gate. -/
theorem generatedResidualLinearUnifiedLocalDensity_overlap
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (initial terminal : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    generatedResidualLinearUnifiedLocalDensityAtBoundary source boundary
        terminal point
        (transportContinuumPointField source initial terminal point field) =
      generatedResidualLinearUnifiedLocalDensityAtBoundary source boundary
        initial point field := by
  have scalarKineticEquality := generatedScalarKineticDensity_overlap
    source initial terminal point field
  have scalarPotentialEquality :
      generatedScalarPotential source terminal point
          (transportContinuumPointField source initial terminal point field).scalar =
        generatedScalarPotential source initial point field.scalar :=
    generatedScalarPotential_overlap_invariant
      source initial terminal point field.scalar
  have matterEquality := generatedContinuumMatterDensity_overlap
    source initial terminal point field
  unfold generatedResidualLinearUnifiedLocalDensityAtBoundary
    generatedUnifiedLocalDensityCoreAtBoundary
    generatedUnifiedLocalDensityNonGravityCoreAtBoundary
  rw [scalarKineticEquality, scalarPotentialEquality, matterEquality]
  rfl

/-- Actual four-dimensional Bochner integral of candidate A.  Finiteness is
tracked separately by `ResidualLinearHolonomicLocalDensityIntegrable`. -/
def integratedResidualLinearUnifiedActionAtBoundary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart)
    (field : StageNineContinuumFieldSection) : ℝ :=
  ∫ point : BasePoint,
    generatedResidualLinearUnifiedLocalDensityAtBoundary
      source boundary chart point (field point)

theorem integratedResidualLinearUnifiedActionAtBoundary_chartInvariant
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (initial terminal : StageNineChart)
    (field : StageNineContinuumFieldSection) :
    integratedResidualLinearUnifiedActionAtBoundary source boundary terminal
        (transportContinuumFieldSection source initial terminal field) =
      integratedResidualLinearUnifiedActionAtBoundary source boundary initial
        field := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with point
  exact generatedResidualLinearUnifiedLocalDensity_overlap
    source boundary initial terminal point (field point)

/-- Root-facing candidate action: only the already source-generated coupling
block is inserted here.  The source does not select the formulation or carry
an action/branch receipt. -/
def sourceGeneratedIntegratedResidualLinearUnifiedAction
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (field : StageNineContinuumFieldSection) : ℝ :=
  integratedResidualLinearUnifiedActionAtBoundary source
    (sourceGeneratedUnifiedCouplings source) chart field

theorem sourceGeneratedIntegratedResidualLinearUnifiedAction_chartInvariant
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (field : StageNineContinuumFieldSection) :
    sourceGeneratedIntegratedResidualLinearUnifiedAction source terminal
        (transportContinuumFieldSection source initial terminal field) =
      sourceGeneratedIntegratedResidualLinearUnifiedAction source initial
        field :=
  integratedResidualLinearUnifiedActionAtBoundary_chartInvariant source
    (sourceGeneratedUnifiedCouplings source) initial terminal field

def holonomicResidualLinearIntegratedUnifiedAction
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : ℝ :=
  sourceGeneratedIntegratedResidualLinearUnifiedAction source chart
    (toContinuumFieldSection configuration)

/-- Integrability belongs to candidate A itself.  The historical squared-law
integrability predicate is not reused. -/
def ResidualLinearHolonomicLocalDensityIntegrable
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  MeasureTheory.Integrable fun point =>
    generatedResidualLinearUnifiedLocalDensityAtBoundary source
      (sourceGeneratedUnifiedCouplings source) chart point
      (toContinuumPointField configuration point)

@[simp] theorem generatedGravityResidualLinearSimplicityDensity_restrictToIIPlus
    (field : StageNineContinuumPointField) :
    generatedGravityResidualLinearSimplicityDensity
        (restrictContinuumPointFieldToIIPlus field) = 0 := by
  simp [generatedGravityResidualLinearSimplicityDensity,
    gravitySpacetimeHodge, gravityCoframePairing,
    coframeTwoFormMetricPairing]

/-- Pointwise exact restriction of the same candidate action density. -/
theorem generatedResidualLinearUnifiedLocalDensity_restrictToIIPlus
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    generatedResidualLinearUnifiedLocalDensityAtBoundary source boundary
        chart point (restrictContinuumPointFieldToIIPlus field) =
      generatedVolumeDensity (restrictContinuumPointFieldToIIPlus field) *
        generatedUnifiedLocalDensityCoreAtBoundary source boundary chart point
          (restrictContinuumPointFieldToIIPlus field) := by
  simp [generatedResidualLinearUnifiedLocalDensityAtBoundary]

/-- The reduced action is not independently supplied.  It is the BF--matter
core evaluated on the actual nonlinear `II+` restriction. -/
def holonomicIIPlusReducedIntegratedUnifiedAction
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : ℝ :=
  ∫ point : BasePoint,
    let restricted := restrictContinuumPointFieldToIIPlus
      (toContinuumPointField configuration point)
    generatedVolumeDensity restricted *
      generatedUnifiedLocalDensityCoreAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point restricted

/-- First positive J0-A seam: the same global action restricted by the actual
computed `II+` substitution is exactly the reduced BF--matter action. -/
theorem holonomicResidualLinearIntegratedAction_restrictIIPlus
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) :
    holonomicResidualLinearIntegratedUnifiedAction source chart
        (restrictHolonomicConfigurationToIIPlus configuration) =
      holonomicIIPlusReducedIntegratedUnifiedAction source chart
        configuration := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with point
  change generatedResidualLinearUnifiedLocalDensityAtBoundary source
      (sourceGeneratedUnifiedCouplings source) chart point
        (toContinuumPointField
          (restrictHolonomicConfigurationToIIPlus configuration) point) = _
  rw [toContinuumPointField_restrictHolonomicConfigurationToIIPlus]
  exact generatedResidualLinearUnifiedLocalDensity_restrictToIIPlus
    source (sourceGeneratedUnifiedCouplings source) chart point
      (toContinuumPointField configuration point)

end

end SaturationMonoid.PhysicsCore.StageNineResidualLinearPlebanskiGlobalAction
