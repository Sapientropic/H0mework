import H0mework.Physics.SynchronizedJoint.CoframeContactLocalActualLift
import H0mework.Physics.JointVariation.SectionOperator
import H0mework.Physics.Exterior.GravityReactionInstallation

/-!
# Complete-joint spacetime section with a synchronized Cartan--EC tail

This module composes two already action-owned writes in their exact dependency
order:

```text
(source, current)
  -> one complete-joint four-dimensional spacetime section
  -> one synchronized Cartan--EC write at its canonical source occurrence
  -> one common global actual.
```

The public constructor consumes only `(source,current)`.  Its indexed
occurrence fixes the two-field inventory and their handoff before any output
is read.  No residual, support, target jet, completed actual, selector,
branch, zero-fiber receipt, or free coefficient enters either write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineIIPlusRestriction
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

local instance completeJointSectionSynchronizedP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance completeJointSectionSynchronizedP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance completeJointSectionSynchronizedP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-! ## Source/current-only composite write -/

/-- The globally assembled complete-joint section is the exact input of the
synchronized gravity leg. -/
def completeJointActionSpacetimeSectionCartanECSynchronizedPreCartanCurrent
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
    source current

/-- One global action write obtained by applying the synchronized Cartan--EC
leg to the already generated spacetime section at the canonical origin. -/
def
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
    source
    (completeJointActionSpacetimeSectionCartanECSynchronizedPreCartanCurrent
      source current)
    0

/-! ## Exact ordered occurrence -/

/-- The two native legs fixed before the common actual is emitted. -/
inductive CompleteJointActionSpacetimeSectionCartanECSynchronizedWriteLeg where
  | spacetimeSection
  | cartanECSynchronized
  deriving DecidableEq

/-- The native action operator attached to each leg. -/
def completeJointActionSpacetimeSectionCartanECSynchronizedActionWrite
    (source : SmoothUnifiedSource)
    (leg : CompleteJointActionSpacetimeSectionCartanECSynchronizedWriteLeg)
    (before : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  match leg with
  | .spacetimeSection =>
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
        source before
  | .cartanECSynchronized =>
      sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
        source before 0

/-- The canonical action occurrence is a singleton indexed by its exact
source and current.  It carries no alternative output or completion payload. -/
inductive CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence
    (_source : SmoothUnifiedSource)
    (_current : StageNineHolonomicConfiguration) where
  | canonical

/-- Source/current-only occurrence producer. -/
def sourceActionGeneratedCompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence
      source current :=
  .canonical

namespace CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence

/-- The exact before-actual of each native leg. -/
def before
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (_occurrence :
      CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence
        source current) :
    CompleteJointActionSpacetimeSectionCartanECSynchronizedWriteLeg →
      StageNineHolonomicConfiguration
  | .spacetimeSection => current
  | .cartanECSynchronized =>
      completeJointActionSpacetimeSectionCartanECSynchronizedPreCartanCurrent
        source current

/-- The exact after-actual of each native leg. -/
def after
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (_occurrence :
      CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence
        source current) :
    CompleteJointActionSpacetimeSectionCartanECSynchronizedWriteLeg →
      StageNineHolonomicConfiguration
  | .spacetimeSection =>
      completeJointActionSpacetimeSectionCartanECSynchronizedPreCartanCurrent
        source current
  | .cartanECSynchronized =>
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
        source current

/-- Every transition is the registered action operator applied to the exact
preceding actual. -/
theorem after_eq_actionWrite
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence
        source current)
    (leg : CompleteJointActionSpacetimeSectionCartanECSynchronizedWriteLeg) :
    occurrence.after leg =
      completeJointActionSpacetimeSectionCartanECSynchronizedActionWrite
        source leg (occurrence.before leg) := by
  cases leg <;>
    rfl

@[simp] theorem spacetimeSection_to_cartanECSynchronized_handoff
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence
        source current) :
    occurrence.after .spacetimeSection =
      occurrence.before .cartanECSynchronized :=
  rfl

/-- The one final actual emitted by the exact two-leg occurrence. -/
abbrev finalActual
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence
        source current) :
    StageNineHolonomicConfiguration :=
  occurrence.after .cartanECSynchronized

end CompleteJointActionSpacetimeSectionCartanECSynchronizedOccurrence

/-! ## Whole-field producer laws -/

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
      source current).gaugeConnection =
      (completeJointActionSpacetimeSectionCartanECSynchronizedPreCartanCurrent
        source current).gaugeConnection :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
      source current).gaugeAuxiliary =
      (completeJointActionSpacetimeSectionCartanECSynchronizedPreCartanCurrent
        source current).gaugeAuxiliary :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_scalar
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
      source current).scalar =
      (completeJointActionSpacetimeSectionCartanECSynchronizedPreCartanCurrent
        source current).scalar :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_matter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
      source current).matter =
      (completeJointActionSpacetimeSectionCartanECSynchronizedPreCartanCurrent
        source current).matter :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
      source current).conjugateMatter =
      (completeJointActionSpacetimeSectionCartanECSynchronizedPreCartanCurrent
        source current).conjugateMatter :=
  rfl

theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_coframe_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    ContDiff ℝ ∞
      (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
        source current).coframe := by
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contDiff
      source
      (completeJointActionSpacetimeSectionCartanECSynchronizedPreCartanCurrent
        source current)
      0

/-- Every component of the primitive Lorentz connection written by the
synchronized tail is globally smooth.  Its origin and curvature target are
computed once from the preceding actual; the emitted field is the canonical
centered normalized-affine primitive. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_gravityConnection_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (direction internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
        source current).gravityConnection point direction internalOut internalIn := by
  change ContDiff ℝ ∞ fun point =>
    coframeECContactCenteredNormalizedAffineLorentzConnectionField 0
        _ _ point direction internalOut internalIn
  simpa [coframeECContactCenteredNormalizedAffineLorentzConnectionField] using
    normalizedAffineLorentzConnectionField_smooth _ _
      direction internalOut internalIn

/-- The computed `II+` auxiliary written from the same affine coframe is
globally smooth componentwise. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_gravityAuxiliary_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
        source current).gravityAuxiliary point internalPair spacetimePair := by
  have auxiliarySmooth : ContDiff ℝ ∞ fun point =>
      physicalIIPlusBivector
        ((sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
          source current).coframe point) :=
    physicalIIPlusBivector_contDiff.comp
      (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_coframe_contDiff
        source current)
  change ContDiff ℝ ∞ fun point =>
    physicalIIPlusBivector
      ((sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
        source current).coframe point) internalPair spacetimePair
  exact contDiff_pi.mp (contDiff_pi.mp auxiliarySmooth internalPair)
    spacetimePair

/-- The live reaction emitted after the coframe, connection, and `II+` writes
is globally smooth componentwise. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_multiplier_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (internalPair spacetimePair : Fin 6) :
    ContDiff ℝ ∞ fun point =>
      (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
        source current).gravitySimplicityMultiplier point
          internalPair spacetimePair := by
  let prepared :=
    diracDualFormNativeCartanECSynchronizedCoframePreparedActual source
      (completeJointActionSpacetimeSectionCartanECSynchronizedPreCartanCurrent
        source current)
      0
  change ContDiff ℝ ∞ fun point =>
    formNativeGravityReactionField prepared point internalPair spacetimePair
  apply formNativeGravityReactionField_component_contDiff
  · intro direction internalOut internalIn
    exact
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_gravityConnection_contDiff
        source current direction internalOut internalIn
  · intro first second
    exact
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_gravityAuxiliary_contDiff
        source current first second

/-- A smooth complete-joint spacetime section remains one globally smooth
nine-field actual after the synchronized gravity tail.  The four gravity
fields use the explicit producer regularity above; the five untouched fields
are retained from the exact preceding actual. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_smooth_of_preCartan_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (preCartanSmooth :
      (completeJointActionSpacetimeSectionCartanECSynchronizedPreCartanCurrent
        source current).Smooth) :
    (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
      source current).Smooth := by
  unfold StageNineHolonomicConfiguration.Smooth at preCartanSmooth ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row column
    exact contDiff_pi.mp
      (contDiff_pi.mp
        (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_coframe_contDiff
          source current)
        row)
      column
  · exact
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_gravityConnection_contDiff
        source current
  · exact
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_gravityAuxiliary_contDiff
        source current
  · exact
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_multiplier_contDiff
        source current
  · simpa only [
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_gaugeConnection] using
      preCartanSmooth.2.2.2.2.1
  · simpa only [
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_gaugeAuxiliary] using
      preCartanSmooth.2.2.2.2.2.1
  · simpa only [
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_scalar] using
      preCartanSmooth.2.2.2.2.2.2.1
  · simpa only [
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_matter] using
      preCartanSmooth.2.2.2.2.2.2.2.1
  · simpa only [
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_conjugateMatter] using
      preCartanSmooth.2.2.2.2.2.2.2.2

theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
        source current) := by
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_simplicity
      source
      (completeJointActionSpacetimeSectionCartanECSynchronizedPreCartanCurrent
        source current)
      0

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedGlobalOperator
