import H0mework.Physics.Gauge.TopologicalGravityCurvatureVariancePairing
import H0mework.Physics.Geometry.IIPlusRestriction

/-!
# Historical-Yukawa form-native Stage-9 mother action

This module records the first metric-free form-native action epoch.  Its
gravity and gauge BF legs use the metric-free oriented wedge directly:

```text
gravity   : W22(B, N(F_raw)) - 1/2 W22(B, star_internal B)
constraint: W22(lambda, B - II+(e))
gauge_i   : W_lie(B_i, F_i) - 1/2 W_lie(B_i, K_{e,i} B_i).
```

Here `N` is the existing once-only historical-curvature variance raise and
`K_{e,i} = g_i^2 * star_e` is computed from the existing dynamical coframe
Hodge and either the explicit boundary or the source-generated coupling
block.  The coframe does not enter the topological BF or holonomic-constraint
pairings.  It enters a gauge BF block only through `K_e`.  Scalar kinetic,
scalar potential, and Dirac--Yukawa component densities instead receive the
separate coordinate volume factor `generatedVolumeDensity`.

No historical unified density core, old action response, fixed actual,
stationarity certificate, new coupling, or source slot is used.  The computed
substitution `B := II+(e)` comes from the formulation-neutral restriction
module; the final restriction theorem is an action-value seam, not a
transported old root credential.

Its component producers and action-dependent theorems remain correct for this
historical hash.  After `StageNineDiracDualFormNativeMotherAction` opens the
repaired Dirac-dual epoch, however, this whole-density definition is no longer
the active root because its matter block still contains the rejected
cross-chiral Yukawa operator.  It must not supply repaired-root stationarity
or covariance receipts.
-/

namespace SaturationMonoid.PhysicsCore.StageNineFormNativeMotherAction

open EmpiricalReferenceScaleCouplingBoundary
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineTopologicalFourFormPairing
open StageNineTopologicalGravityCurvatureVariancePairing

noncomputable section

set_option autoImplicit false

/-! ## Form-native pointwise coefficients -/

/-- The existing boundary/coframe-generated gauge constitutive operator
`K_e = g^2 * star_e`, packaged without adding any coupling or field slot. -/
def gaugeConstitutiveOperatorAtBoundary
    (coframe : LorentzianCoframe) (couplingSquared : ℝˣ) :
    GaugeTwoForm →ₗ[ℝ] GaugeTwoForm :=
  (couplingSquared : ℝ) • coframeGaugeSpacetimeHodgeLinear coframe

/-- Generic direct spacetime wedge for one Lie-valued gauge block.  The
fiber pairing contracts only the Lie carrier; spacetime orientation is the
metric-free `W22` orientation. -/
def generatedFormNativeGaugeSectorBFDensity
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (pairing : V → V → ℝ)
    (constitutive : GaugeTwoForm →ₗ[ℝ] GaugeTwoForm)
    (curvature auxiliary : Fin 6 → V) : ℝ :=
  generatedTwoFormWedgeCoefficient pairing auxiliary curvature -
    (1 / 2 : ℝ) *
      generatedTwoFormWedgeCoefficient pairing auxiliary
        (liftGaugeTwoFormOperator constitutive auxiliary)

/-- Corrected gravity BF/constitutive coefficient.  The historical lowered
curvature is raised exactly once by `gravityTopologicalBFCoefficient`; the
internal Hodge in the quadratic leg is applied exactly once. -/
def generatedFormNativeGravityBFDensity
    (field : StageNineContinuumPointField) : ℝ :=
  gravityTopologicalBFCoefficient field.gravityAuxiliary
      field.gravityCurvature -
    (1 / 2 : ℝ) *
      gravityTopologicalWedgeCoefficient field.gravityAuxiliary
        (gravityInternalDualEquiv field.gravityAuxiliary)

/-- Direct holonomic reaction term.  It has no coframe pairing, spacetime
Hodge, volume factor, or squared residual. -/
def generatedFormNativeGravityConstraintDensity
    (field : StageNineContinuumPointField) : ℝ :=
  gravityTopologicalWedgeCoefficient field.gravitySimplicityMultiplier
    (generatedGravitySimplicityResidual field)

/-- Sum of the three direct gauge BF/constitutive blocks at an explicit
reference-scale boundary.  Every `K_e` is computed from the same live
coframe; only its already typed coupling differs by gauge block. -/
def generatedFormNativeGaugeDensityAtBoundary
    (boundary : EmpiricalReferenceScaleCouplings)
    (field : StageNineContinuumPointField) : ℝ :=
  generatedFormNativeGaugeSectorBFDensity
      (@specialUnitaryLiePairing (Fin 3) _ _)
      (gaugeConstitutiveOperatorAtBoundary field.coframe
        boundary.strongCouplingSquared)
      (fun pair => (field.gaugeCurvature pair).1)
      (fun pair => (field.gaugeAuxiliary pair).1) +
    generatedFormNativeGaugeSectorBFDensity
      (@specialUnitaryLiePairing (Fin 2) _ _)
      (gaugeConstitutiveOperatorAtBoundary field.coframe
        boundary.weakCouplingSquared)
      (fun pair => (field.gaugeCurvature pair).2.1)
      (fun pair => (field.gaugeAuxiliary pair).2.1) +
    generatedFormNativeGaugeSectorBFDensity hyperchargeLiePairing
      (gaugeConstitutiveOperatorAtBoundary field.coframe
        boundary.hyperchargeCouplingSquared)
      (fun pair => (field.gaugeCurvature pair).2.2)
      (fun pair => (field.gaugeAuxiliary pair).2.2)

/-- The component scalar and Dirac--Yukawa density, with its own coordinate
volume factor.  No topological BF term is placed inside this factor. -/
def generatedFormNativeMatterDensity
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) : ℝ :=
  generatedVolumeDensity field *
    (generatedScalarKineticDensity source chart point field -
      generatedScalarPotential source chart point field.scalar +
      generatedContinuumMatterDensity source chart point field)

/-- The corrected local mother-action coefficient at an explicit coupling
boundary.  In particular, this definition does not call either historical
`generatedUnifiedLocalDensityCoreAtBoundary` definition. -/
def generatedFormNativeUnifiedLocalDensityAtBoundary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) : ℝ :=
  generatedFormNativeGravityBFDensity field +
    generatedFormNativeGravityConstraintDensity field +
    generatedFormNativeGaugeDensityAtBoundary boundary field +
    generatedFormNativeMatterDensity source chart point field

/-- The same local coefficient after the source has generated its coupling
boundary.  The source does not carry an action or formulation receipt. -/
def sourceGeneratedFormNativeUnifiedLocalDensity
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) : ℝ :=
  generatedFormNativeUnifiedLocalDensityAtBoundary source
    (sourceGeneratedUnifiedCouplings source) chart point field

/-! ## Gauge-chart descent -/

/-- Pointwise descent through the existing Stage-9 gauge chart transition.
Gravity and gauge curvature/auxiliary coordinates are unchanged by this
transition; the three frame-relative matter readouts use their existing
overlap theorems.  This is not a local Spin/Lorentz covariance theorem. -/
theorem generatedFormNativeUnifiedLocalDensityAtBoundary_overlap
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (initial terminal : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    generatedFormNativeUnifiedLocalDensityAtBoundary source boundary terminal
        point
        (transportContinuumPointField source initial terminal point field) =
      generatedFormNativeUnifiedLocalDensityAtBoundary source boundary initial
        point field := by
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
  unfold generatedFormNativeUnifiedLocalDensityAtBoundary
    generatedFormNativeMatterDensity
  rw [scalarKineticEquality, scalarPotentialEquality, matterEquality]
  rfl

theorem sourceGeneratedFormNativeUnifiedLocalDensity_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField) :
    sourceGeneratedFormNativeUnifiedLocalDensity source terminal point
        (transportContinuumPointField source initial terminal point field) =
      sourceGeneratedFormNativeUnifiedLocalDensity source initial point
        field :=
  generatedFormNativeUnifiedLocalDensityAtBoundary_overlap source
    (sourceGeneratedUnifiedCouplings source) initial terminal point field

/-! ## Global and holonomic mouths -/

/-- Actual four-dimensional Bochner integral of the corrected action at an
explicit coupling boundary.  Finiteness is tracked by the dedicated
integrability predicate below. -/
def integratedFormNativeUnifiedActionAtBoundary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart)
    (field : StageNineContinuumFieldSection) : ℝ :=
  ∫ point : BasePoint,
    generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
      point (field point)

theorem integratedFormNativeUnifiedActionAtBoundary_chartInvariant
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (initial terminal : StageNineChart)
    (field : StageNineContinuumFieldSection) :
    integratedFormNativeUnifiedActionAtBoundary source boundary terminal
        (transportContinuumFieldSection source initial terminal field) =
      integratedFormNativeUnifiedActionAtBoundary source boundary initial
        field := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with point
  exact generatedFormNativeUnifiedLocalDensityAtBoundary_overlap
    source boundary initial terminal point (field point)

/-- Source-facing integrated action of the active form-native candidate.  Only the already source-generated
coupling block is installed; no empirical table or action certificate is a
source-facing premise. -/
def sourceGeneratedIntegratedFormNativeUnifiedAction
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (field : StageNineContinuumFieldSection) : ℝ :=
  integratedFormNativeUnifiedActionAtBoundary source
    (sourceGeneratedUnifiedCouplings source) chart field

theorem sourceGeneratedIntegratedFormNativeUnifiedAction_chartInvariant
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (field : StageNineContinuumFieldSection) :
    sourceGeneratedIntegratedFormNativeUnifiedAction source terminal
        (transportContinuumFieldSection source initial terminal field) =
      sourceGeneratedIntegratedFormNativeUnifiedAction source initial field :=
  integratedFormNativeUnifiedActionAtBoundary_chartInvariant source
    (sourceGeneratedUnifiedCouplings source) initial terminal field

/-- Holonomic mouth: curvature and covariant derivatives are regenerated
from the primitive connection/coframe/matter configuration by
`toContinuumFieldSection`; they are not independently supplied to the action. -/
def holonomicFormNativeIntegratedUnifiedAction
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : ℝ :=
  sourceGeneratedIntegratedFormNativeUnifiedAction source chart
    (toContinuumFieldSection configuration)

/-- Integrability belongs to the corrected density itself.  This is an
analytic condition on a candidate over the noncompact base, not source data,
stationarity, or a field-equation receipt. -/
def FormNativeHolonomicLocalDensityIntegrable
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  MeasureTheory.Integrable fun point =>
    sourceGeneratedFormNativeUnifiedLocalDensity source chart point
      (toContinuumPointField configuration point)

/-! ## Computed `II+` action-value restriction -/

/-- The corrected density with the holonomic-constraint channel omitted.
This is used only as the readout target of the actual computed
`B := II+(e)` substitution below. -/
def generatedFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) : ℝ :=
  generatedFormNativeGravityBFDensity field +
    generatedFormNativeGaugeDensityAtBoundary boundary field +
    generatedFormNativeMatterDensity source chart point field

@[simp] theorem generatedFormNativeGravityConstraintDensity_restrictToIIPlus
    (field : StageNineContinuumPointField) :
    generatedFormNativeGravityConstraintDensity
        (restrictContinuumPointFieldToIIPlus field) = 0 := by
  simp [generatedFormNativeGravityConstraintDensity]

/-- Pointwise action-value seam: the direct constraint term vanishes after
the computed nonlinear substitution.  No old action density is used. -/
theorem generatedFormNativeUnifiedLocalDensity_restrictToIIPlus
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart) (point : BasePoint)
    (field : StageNineContinuumPointField) :
    generatedFormNativeUnifiedLocalDensityAtBoundary source boundary chart
        point (restrictContinuumPointFieldToIIPlus field) =
      generatedFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
        source boundary chart point
        (restrictContinuumPointFieldToIIPlus field) := by
  unfold generatedFormNativeUnifiedLocalDensityAtBoundary
    generatedFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
  rw [generatedFormNativeGravityConstraintDensity_restrictToIIPlus]
  ring

/-- The form-native reduced action is computed by evaluating the same
gravity/gauge/matter legs on the nonlinear `II+` restriction. -/
def holonomicIIPlusReducedFormNativeIntegratedUnifiedAction
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : ℝ :=
  ∫ point : BasePoint,
    generatedFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary source
      (sourceGeneratedUnifiedCouplings source) chart point
      (restrictContinuumPointFieldToIIPlus
        (toContinuumPointField configuration point))

/-- The corrected holonomic action restricted by the computed `II+` map is
exactly its reduced action value.  This is producer soundness/action
provenance, not an independent equation or critical-locus equivalence. -/
theorem holonomicFormNativeIntegratedAction_restrictIIPlus
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) :
    holonomicFormNativeIntegratedUnifiedAction source chart
        (restrictHolonomicConfigurationToIIPlus configuration) =
      holonomicIIPlusReducedFormNativeIntegratedUnifiedAction source chart
        configuration := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with point
  change
    generatedFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point
        (toContinuumPointField
          (restrictHolonomicConfigurationToIIPlus configuration) point) = _
  rw [toContinuumPointField_restrictHolonomicConfigurationToIIPlus]
  exact generatedFormNativeUnifiedLocalDensity_restrictToIIPlus source
    (sourceGeneratedUnifiedCouplings source) chart point
    (toContinuumPointField configuration point)

end

end SaturationMonoid.PhysicsCore.StageNineFormNativeMotherAction
