import H0mework.Physics.Holonomic.HolonomicField

/-!
# Dependency-light `II+` restriction

This module owns the action-independent nonlinear substitution

`B := II+(e) = star_internal (e wedge e)`

on the existing continuum point field, field section, and primitive
holonomic configuration.  It also proves smoothness, nondegeneracy,
value-level point-field compatibility, and simplicity-residual readouts
needed by any candidate gravity action.  The actual whole-field Fréchet jet
chain rule is proved separately in
`StageNineFormNativeIIPlusJetKinematics`.

The restriction computes its bivector from the same live coframe.  It stores
no action, source, branch receipt, shell, stationarity, residual value,
coupling, or fixed actual.  In particular this module does not choose between
the historical residual-linear action and the corrected form-native action.
-/

namespace SaturationMonoid.PhysicsCore.StageNineIIPlusRestriction

open ProofFreeRicherAnholonomicSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

/-- Replace only the continuum bivector coordinate by the actual `II+`
computed from the same dynamical coframe. -/
def restrictContinuumPointFieldToIIPlus
    (field : StageNineContinuumPointField) : StageNineContinuumPointField :=
  { field with
    gravityAuxiliary := physicalIIPlusBivector field.coframe }

@[simp] theorem restrictContinuumPointFieldToIIPlus_coframe
    (field : StageNineContinuumPointField) :
    (restrictContinuumPointFieldToIIPlus field).coframe = field.coframe :=
  rfl

@[simp] theorem restrictContinuumPointFieldToIIPlus_gravityAuxiliary
    (field : StageNineContinuumPointField) :
    (restrictContinuumPointFieldToIIPlus field).gravityAuxiliary =
      physicalIIPlusBivector field.coframe :=
  rfl

@[simp] theorem restrictContinuumPointFieldToIIPlus_multiplier
    (field : StageNineContinuumPointField) :
    (restrictContinuumPointFieldToIIPlus field).gravitySimplicityMultiplier =
      field.gravitySimplicityMultiplier :=
  rfl

/-- Pointwise restriction lifted to a continuum section. -/
def restrictContinuumFieldSectionToIIPlus
    (field : StageNineContinuumFieldSection) :
    StageNineContinuumFieldSection :=
  fun point => restrictContinuumPointFieldToIIPlus (field point)

/-- Configuration-level actual substitution.  No branch witness or shell
receipt is stored: the new bivector section is computed pointwise. -/
def restrictHolonomicConfigurationToIIPlus
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { configuration with
    gravityAuxiliary := fun point =>
      physicalIIPlusBivector (configuration.coframe point) }

@[simp] theorem restrictHolonomicConfigurationToIIPlus_coframe
    (configuration : StageNineHolonomicConfiguration) :
    (restrictHolonomicConfigurationToIIPlus configuration).coframe =
      configuration.coframe :=
  rfl

@[simp] theorem restrictHolonomicConfigurationToIIPlus_gravityAuxiliary
    (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :
    (restrictHolonomicConfigurationToIIPlus configuration).gravityAuxiliary
        point =
      physicalIIPlusBivector (configuration.coframe point) :=
  rfl

@[simp] theorem restrictHolonomicConfigurationToIIPlus_multiplier
    (configuration : StageNineHolonomicConfiguration) :
    (restrictHolonomicConfigurationToIIPlus
      configuration).gravitySimplicityMultiplier =
      configuration.gravitySimplicityMultiplier :=
  rfl

/-- The derived continuum point-field constructor commutes definitionally
with the computed `II+` restriction.  This is a value-level seam; the point
field does not store the gravity-auxiliary first derivative. -/
theorem toContinuumPointField_restrictHolonomicConfigurationToIIPlus
    (configuration : StageNineHolonomicConfiguration) (point : BasePoint) :
    toContinuumPointField
        (restrictHolonomicConfigurationToIIPlus configuration) point =
      restrictContinuumPointFieldToIIPlus
        (toContinuumPointField configuration point) :=
  rfl

theorem restrictHolonomicConfigurationToIIPlus_nondegenerate_iff
    (configuration : StageNineHolonomicConfiguration) :
    (restrictHolonomicConfigurationToIIPlus configuration).Nondegenerate ↔
      configuration.Nondegenerate :=
  Iff.rfl

/-- The raw coframe wedge is a smooth finite-coordinate polynomial. -/
theorem coframeWedge_contDiff :
    ContDiff ℝ ∞ (coframeWedge : LorentzianCoframe → PhysicalBivector) := by
  apply contDiff_pi'
  intro internalPair
  apply contDiff_pi'
  intro spacetimePair
  unfold coframeWedge
  fun_prop

/-- The computed `II+` map is smooth independently of any action. -/
theorem physicalIIPlusBivector_contDiff :
    ContDiff ℝ ∞
      (physicalIIPlusBivector : LorentzianCoframe → PhysicalBivector) := by
  apply contDiff_pi'
  intro internalPair
  apply contDiff_pi'
  intro spacetimePair
  fin_cases internalPair
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      (contDiff_pi.mp
        (contDiff_pi.mp coframeWedge_contDiff 3) spacetimePair)
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      (contDiff_pi.mp
        (contDiff_pi.mp coframeWedge_contDiff 4) spacetimePair)
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      (contDiff_pi.mp
        (contDiff_pi.mp coframeWedge_contDiff 5) spacetimePair)
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      (contDiff_pi.mp
        (contDiff_pi.mp coframeWedge_contDiff 0) spacetimePair).neg
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      (contDiff_pi.mp
        (contDiff_pi.mp coframeWedge_contDiff 1) spacetimePair).neg
  · simpa [physicalIIPlusBivector, internalBivectorDual,
      lorentzianCoframeHodge] using
      (contDiff_pi.mp
        (contDiff_pi.mp coframeWedge_contDiff 2) spacetimePair).neg

theorem restrictHolonomicConfigurationToIIPlus_smooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) :
    (restrictHolonomicConfigurationToIIPlus configuration).Smooth := by
  constructor
  · exact smooth.1
  constructor
  · exact smooth.2.1
  constructor
  · have coframeSmooth : ContDiff ℝ ∞ configuration.coframe := by
      apply contDiff_pi'
      intro row
      apply contDiff_pi'
      intro column
      exact smooth.1 row column
    have simplicitySmooth : ContDiff ℝ ∞ fun point =>
        physicalIIPlusBivector (configuration.coframe point) :=
      physicalIIPlusBivector_contDiff.comp coframeSmooth
    intro internalPair spacetimePair
    exact contDiff_pi.mp
      (contDiff_pi.mp simplicitySmooth internalPair) spacetimePair
  · exact smooth.2.2.2

/-- The action-independent simplicity residual vanishes after the computed
`II+` substitution. -/
@[simp] theorem generatedGravitySimplicityResidual_restrictToIIPlus
    (field : StageNineContinuumPointField) :
    generatedGravitySimplicityResidual
        (restrictContinuumPointFieldToIIPlus field) = 0 := by
  simp [generatedGravitySimplicityResidual,
    restrictContinuumPointFieldToIIPlus]

end

end SaturationMonoid.PhysicsCore.StageNineIIPlusRestriction
