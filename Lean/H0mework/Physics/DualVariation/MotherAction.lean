import H0mework.Physics.Exterior.MotherAction
import H0mework.Physics.Dirac.DiracDualYukawaLocalSpinDensity
import H0mework.Physics.Dirac.ScalarLocalSpinDensity

/-!
# Dirac-dual form-native Stage-9 mother action

This module opens the unique repaired form-native action epoch.  It retains
the already audited metric-free gravity, holonomic-constraint, and gauge BF
blocks, but replaces the historical cross-chiral Yukawa summand by the
source-generated Dirac-dual operator fixed in
`StageNineDiracDualYukawaSpinJurisdiction`.

The matter block is assembled directly as

```text
volume * (scalar kinetic - scalar potential)
+ volume * Dirac-dual(Dirac kinetic)
+ volume * Dirac-dual(repaired right-chiral Yukawa).
```

In particular, the new root is not defined by subtracting a term from the
historical action.  `StageNineFormNativeMotherAction` remains imported only
for the unchanged gravity/gauge component producers and for historical-hash
regressions while their action-dependent consumers are migrated.

The local-Spin theorems below close the repaired matter block only.  They do
not claim covariance of the complete holonomic root, derive an
Euler--Lagrange equation, or provide a stationary actual.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeMotherAction

open EmpiricalReferenceScaleCouplingBoundary
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracKineticLocalSpinConnection
open StageNineDiracKineticLocalSpinDensity
open StageNineDiracKineticLocalSpinDifferential
open StageNineEnrichedProofFreeSource
open StageNineFormNativeMotherAction
open StageNineGlobalBundle
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineScalarLocalSpinDensity
open StageNineSpinMatterBundle

open scoped ContDiff MatrixGroups

noncomputable section

set_option autoImplicit false

/-! ## Repaired Dirac-dual and matter blocks -/

/-- The complete forward matter vector of the repaired epoch.  The kinetic
and Yukawa operators are both generated before the independent dual evaluates
them. -/
def generatedContinuumDiracDualMatterVector
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    DiracExteriorMatterCarrier :=
  generatedContinuumMatterKineticVector source chart point field +
    generatedContinuumDiracDualYukawaVector source chart point field

/-- The separately densitized kinetic and repaired Yukawa coefficients. -/
def generatedDensitizedContinuumDiracDualMatterDensity
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) : ℝ :=
  generatedDensitizedContinuumMatterKineticDensity source chart point field +
    generatedDensitizedContinuumDiracDualYukawaDensity source chart point field

/-- The two separately audited terms are exactly evaluation of the one
complete forward vector by the same independent dual and volume density. -/
theorem generatedDensitizedContinuumDiracDualMatterDensity_eq_vectorPairing
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    generatedDensitizedContinuumDiracDualMatterDensity source chart point
        field =
      generatedVolumeDensity field *
        (matterDualFrameRelative source chart point field.conjugateMatter
          (generatedContinuumDiracDualMatterVector source chart point
            field)).re := by
  simp only [generatedDensitizedContinuumDiracDualMatterDensity,
    generatedDensitizedContinuumMatterKineticDensity,
    generatedDensitizedContinuumDiracDualYukawaDensity,
    generatedContinuumDiracDualMatterVector, map_add, Complex.add_re]
  ring

/-- Gauge-chart descent of the complete forward Dirac-dual vector. -/
theorem generatedContinuumDiracDualMatterVector_overlap
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    generatedContinuumDiracDualMatterVector source terminal point
        (transportContinuumPointField source initial terminal point field) =
      generatedContinuumDiracDualMatterVector source initial point field := by
  unfold generatedContinuumDiracDualMatterVector
  rw [generatedContinuumMatterKineticVector_overlap,
    generatedContinuumDiracDualYukawaVector_overlap]

/-- Gauge-chart descent of the complete densitized Dirac-dual block. -/
theorem generatedDensitizedContinuumDiracDualMatterDensity_overlap
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    generatedDensitizedContinuumDiracDualMatterDensity source terminal point
        (transportContinuumPointField source initial terminal point field) =
      generatedDensitizedContinuumDiracDualMatterDensity source initial point
        field := by
  unfold generatedDensitizedContinuumDiracDualMatterDensity
  rw [generatedDensitizedContinuumMatterKineticDensity_overlap,
    generatedDensitizedContinuumDiracDualYukawaDensity_overlap]

/-- The complete forward matter vector intertwines the primitive local Spin
action.  Smoothness and Lorentz-skewness are needed only by its kinetic leg. -/
theorem generatedContinuumDiracDualMatterVector_localSpin_covariant
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (matterSmooth : ContDiff ℝ ∞ (fun candidate =>
      matterCoordinateEquiv (configuration.matter candidate)))
    (point : BasePoint)
    (connectionSkew :
      LorentzSkew (configuration.gravityConnection point)) :
    generatedContinuumDiracDualMatterVector source chart point
        (toContinuumPointField
          (localSpinDiracKineticAction spinField configuration) point) =
      spinDiracMatterRepresentation (spinField point)
        (generatedContinuumDiracDualMatterVector source chart point
          (toContinuumPointField configuration point)) := by
  unfold generatedContinuumDiracDualMatterVector
  rw [generatedContinuumMatterKineticVector_localSpin_covariant
      source chart spinField configuration spinSmooth matterSmooth point
      connectionSkew,
    generatedContinuumDiracDualYukawaVector_localSpin_covariant,
    map_add]

/-- Pointwise local-Spin invariance of the complete densitized Dirac-dual
block on the same holonomic configuration. -/
theorem generatedDensitizedContinuumDiracDualMatterDensity_localSpin_invariant
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (matterSmooth : ContDiff ℝ ∞ (fun candidate =>
      matterCoordinateEquiv (configuration.matter candidate)))
    (point : BasePoint)
    (connectionSkew :
      LorentzSkew (configuration.gravityConnection point)) :
    generatedDensitizedContinuumDiracDualMatterDensity source chart point
        (toContinuumPointField
          (localSpinDiracKineticAction spinField configuration) point) =
      generatedDensitizedContinuumDiracDualMatterDensity source chart point
        (toContinuumPointField configuration point) := by
  unfold generatedDensitizedContinuumDiracDualMatterDensity
  rw [generatedDensitizedContinuumMatterKineticDensity_localSpin_invariant
      source chart spinField configuration spinSmooth matterSmooth point
      connectionSkew,
    generatedDensitizedContinuumDiracDualYukawaDensity_localSpin_invariant]

/-- Complete repaired matter block.  Each component carries its own volume
factor, so no topological BF coefficient is accidentally densitized. -/
def generatedDiracDualFormNativeMatterDensity
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) : ℝ :=
  generatedDensitizedContinuumScalarDensity source chart point field +
    generatedDensitizedContinuumDiracDualMatterDensity source chart point field

theorem generatedDiracDualFormNativeMatterDensity_overlap
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    generatedDiracDualFormNativeMatterDensity source terminal point
        (transportContinuumPointField source initial terminal point field) =
      generatedDiracDualFormNativeMatterDensity source initial point field := by
  unfold generatedDiracDualFormNativeMatterDensity
  rw [generatedDensitizedContinuumScalarDensity_overlap,
    generatedDensitizedContinuumDiracDualMatterDensity_overlap]

/-- Pointwise local-Spin invariance of the repaired scalar plus Dirac-dual
matter block. -/
theorem generatedDiracDualFormNativeMatterDensity_localSpin_invariant
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (matterSmooth : ContDiff ℝ ∞ (fun candidate =>
      matterCoordinateEquiv (configuration.matter candidate)))
    (point : BasePoint)
    (connectionSkew :
      LorentzSkew (configuration.gravityConnection point)) :
    generatedDiracDualFormNativeMatterDensity source chart point
        (toContinuumPointField
          (localSpinDiracKineticAction spinField configuration) point) =
      generatedDiracDualFormNativeMatterDensity source chart point
        (toContinuumPointField configuration point) := by
  unfold generatedDiracDualFormNativeMatterDensity
  rw [generatedDensitizedContinuumScalarDensity_localSpin_invariant,
    generatedDensitizedContinuumDiracDualMatterDensity_localSpin_invariant
      source chart spinField configuration spinSmooth matterSmooth point
      connectionSkew]

/-! ## Unique repaired form-native root -/

/-- Authoritative local coefficient of the repaired Dirac-dual epoch at an
explicit coupling boundary.  The definition is a direct assembly of the
five live component blocks, not a delta applied to the historical root. -/
def generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) : ℝ :=
  generatedFormNativeGravityBFDensity field +
    generatedFormNativeGravityConstraintDensity field +
    generatedFormNativeGaugeDensityAtBoundary boundary field +
    generatedDiracDualFormNativeMatterDensity source chart point field

/-- Source-facing local root.  The only installed boundary is the existing
source-generated coupling block. -/
def sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) : ℝ :=
  generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
    (sourceGeneratedUnifiedCouplings source) chart point field

theorem generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary_overlap
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (initial terminal : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
        terminal point
        (transportContinuumPointField source initial terminal point field) =
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
        initial point field := by
  unfold generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
  rw [generatedDiracDualFormNativeMatterDensity_overlap]
  rfl

theorem sourceGeneratedDiracDualFormNativeUnifiedLocalDensity_overlap
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source terminal point
        (transportContinuumPointField source initial terminal point field) =
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source initial point
        field :=
  generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary_overlap source
    (sourceGeneratedUnifiedCouplings source) initial terminal point field

/-! ## Global and holonomic mouths -/

/-- Four-dimensional integral of the repaired root at an explicit coupling
boundary. -/
def integratedDiracDualFormNativeUnifiedActionAtBoundary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart)
    (field : StageNineContinuumFieldSection) : ℝ :=
  ∫ point : BasePoint,
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
      chart point (field point)

theorem integratedDiracDualFormNativeUnifiedActionAtBoundary_chartInvariant
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (initial terminal : StageNineChart)
    (field : StageNineContinuumFieldSection) :
    integratedDiracDualFormNativeUnifiedActionAtBoundary source boundary
        terminal (transportContinuumFieldSection source initial terminal field) =
      integratedDiracDualFormNativeUnifiedActionAtBoundary source boundary
        initial field := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with point
  exact
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary_overlap source
      boundary initial terminal point (field point)

/-- Source-facing integrated action of the unique repaired form-native
epoch. -/
def sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (field : StageNineContinuumFieldSection) : ℝ :=
  integratedDiracDualFormNativeUnifiedActionAtBoundary source
    (sourceGeneratedUnifiedCouplings source) chart field

theorem sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction_chartInvariant
    (source : SmoothUnifiedSource)
    (initial terminal : StageNineChart)
    (field : StageNineContinuumFieldSection) :
    sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction source terminal
        (transportContinuumFieldSection source initial terminal field) =
      sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction source initial
        field :=
  integratedDiracDualFormNativeUnifiedActionAtBoundary_chartInvariant source
    (sourceGeneratedUnifiedCouplings source) initial terminal field

/-- Holonomic mouth of the repaired root.  Curvatures and covariant
derivatives are regenerated from the primitive configuration. -/
def holonomicDiracDualFormNativeIntegratedUnifiedAction
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : ℝ :=
  sourceGeneratedIntegratedDiracDualFormNativeUnifiedAction source chart
    (toContinuumFieldSection configuration)

/-- Analytic integrability predicate belonging to the repaired density. -/
def DiracDualFormNativeHolonomicLocalDensityIntegrable
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  MeasureTheory.Integrable fun point =>
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source chart point
      (toContinuumPointField configuration point)

/-! ## Computed `II+` action-value restriction -/

/-- The repaired density with the direct holonomic-constraint channel
omitted. -/
def generatedDiracDualFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) : ℝ :=
  generatedFormNativeGravityBFDensity field +
    generatedFormNativeGaugeDensityAtBoundary boundary field +
    generatedDiracDualFormNativeMatterDensity source chart point field

/-- The direct constraint term vanishes after the computed nonlinear
`B := II+(e)` substitution in the repaired root as well. -/
theorem generatedDiracDualFormNativeUnifiedLocalDensity_restrictToIIPlus
    (source : SmoothUnifiedSource)
    (boundary : EmpiricalReferenceScaleCouplings)
    (chart : StageNineChart)
    (point : BasePoint)
    (field : StageNineContinuumPointField) :
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source boundary
        chart point (restrictContinuumPointFieldToIIPlus field) =
      generatedDiracDualFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
        source boundary chart point
        (restrictContinuumPointFieldToIIPlus field) := by
  unfold generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary
    generatedDiracDualFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
  rw [generatedFormNativeGravityConstraintDensity_restrictToIIPlus]
  ring

/-- Reduced repaired action obtained by evaluating every retained component
on the same computed `II+` restriction. -/
def holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) : ℝ :=
  ∫ point : BasePoint,
    generatedDiracDualFormNativeUnifiedLocalDensityWithoutConstraintAtBoundary
      source (sourceGeneratedUnifiedCouplings source) chart point
      (restrictContinuumPointFieldToIIPlus
        (toContinuumPointField configuration point))

/-- Computed action-value restriction for the repaired root.  This is
producer soundness, not a critical-locus equivalence theorem. -/
theorem holonomicDiracDualFormNativeIntegratedAction_restrictIIPlus
    (source : SmoothUnifiedSource)
    (chart : StageNineChart)
    (configuration : StageNineHolonomicConfiguration) :
    holonomicDiracDualFormNativeIntegratedUnifiedAction source chart
        (restrictHolonomicConfigurationToIIPlus configuration) =
      holonomicIIPlusReducedDiracDualFormNativeIntegratedUnifiedAction source
        chart configuration := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with point
  change
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) chart point
        (toContinuumPointField
          (restrictHolonomicConfigurationToIIPlus configuration) point) = _
  rw [toContinuumPointField_restrictHolonomicConfigurationToIIPlus]
  exact
    generatedDiracDualFormNativeUnifiedLocalDensity_restrictToIIPlus source
      (sourceGeneratedUnifiedCouplings source) chart point
      (toContinuumPointField configuration point)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeMotherAction
