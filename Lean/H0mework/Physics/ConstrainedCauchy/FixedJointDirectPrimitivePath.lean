import H0mework.Physics.SynchronizedJoint.CoframeContactLocalActualLift
import H0mework.Physics.JointVariation.SectionOperator
import H0mework.Physics.ConstrainedCauchy.FixedGlobalOperator
import H0mework.Physics.Exterior.GravityReactionInstallation
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterNaturality
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Fixed P506/L0 direct complete-joint primitive path

The complete-joint spacetime section is recentered directly at every actual
contact.  One synchronized Cartan--EC profile at that contact supplies both
the coframe and Lorentz first jets.  Their radial primitives are installed in
one common actual before the live gravity reaction is recomputed.

The three-leg occurrence is indexed by the primitive source and current and
records the exact handoffs between the section, joint path, and reaction legs.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyCompleteJointDirectPrimitivePath

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineIIPlusRestriction
open StageNineLorentzConnectionVariation
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-! ## One contact-indexed action profile -/

/-- The strongest complete-joint four-dimensional section already emitted by
the same source and current. -/
def directPrimitivePathPrefix
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
    source current

/-- Recenter the exact section input at the actual contact. -/
def directPrimitivePathProfileInput
    (sectionInput : StageNineHolonomicConfiguration)
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration sectionInput contact

/-- Run the native synchronized Cartan--EC action at that contact. -/
def directPrimitivePathProfileContact
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (contact : BasePoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift
    source (directPrimitivePathProfileInput sectionInput contact) 0

def directPrimitivePathCoframeFirstJet
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (contact : BasePoint) : PointwiseLorentzianCoframeJet :=
  diracDualFormNativeCartanECSynchronizedCoframeFirstJet source
    (directPrimitivePathProfileInput sectionInput contact) 0

/-- The coframe and connection readers consume the same synchronized profile
occurrence. -/
theorem directPrimitivePathCoframeFirstJet_eq_profileContact
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (contact : BasePoint) :
    directPrimitivePathCoframeFirstJet source sectionInput contact =
      holonomicCoframeFirstJetAt
        (directPrimitivePathProfileContact source sectionInput contact).coframe 0 := by
  simpa [directPrimitivePathCoframeFirstJet,
    directPrimitivePathProfileContact] using
    (sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframeFirstJet_contact
      source (directPrimitivePathProfileInput sectionInput contact) 0).symm

def directPrimitivePathCoframeJetOneForm
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (derivativeDirection : LorentzianIndex) : LorentzianCoframe :=
  fun internal coordinate =>
    (directPrimitivePathCoframeFirstJet source sectionInput contact).derivative
      derivativeDirection internal coordinate

def directPrimitivePathCoframeJetCoordinateCLM
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (internal coordinate : LorentzianIndex) : BasePoint →L[ℝ] ℝ :=
  ∑ derivativeDirection : LorentzianIndex,
    (baseCoordinate derivativeDirection).smulRight
      (directPrimitivePathCoframeJetOneForm source sectionInput contact
        derivativeDirection internal coordinate)

theorem directPrimitivePathCoframeJetCoordinateCLM_coordinate
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (derivativeDirection internal coordinate : LorentzianIndex) :
    directPrimitivePathCoframeJetCoordinateCLM
        source sectionInput contact internal coordinate
        (coordinateDirection derivativeDirection) =
      directPrimitivePathCoframeJetOneForm
        source sectionInput contact derivativeDirection internal coordinate := by
  fin_cases derivativeDirection <;>
    simp [directPrimitivePathCoframeJetCoordinateCLM,
      baseCoordinate, coordinateDirection, Fin.sum_univ_four]

def directPrimitivePathLoweredConnectionFirstJet
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) : ℝ :=
  minkowskiInternalSign (pairFirst internalPair) *
    gravityConnectionDerivative
      (directPrimitivePathProfileContact source sectionInput contact)
      0 derivativeDirection formDirection
      (pairFirst internalPair) (pairSecond internalPair)

def directPrimitivePathLorentzJetOneForm
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (derivativeDirection : LorentzianIndex) : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    directPrimitivePathLoweredConnectionFirstJet source sectionInput contact
      derivativeDirection formDirection internalPair

def directPrimitivePathLorentzJetCLM
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (contact : BasePoint) : BasePoint →L[ℝ] LorentzBivectorOneForm :=
  ∑ derivativeDirection : LorentzianIndex,
    (baseCoordinate derivativeDirection).smulRight
      (directPrimitivePathLorentzJetOneForm source sectionInput contact
        derivativeDirection)

theorem directPrimitivePathLorentzJetCLM_coordinate
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (contact : BasePoint)
    (derivativeDirection : LorentzianIndex) :
    directPrimitivePathLorentzJetCLM source sectionInput contact
        (coordinateDirection derivativeDirection) =
      directPrimitivePathLorentzJetOneForm
        source sectionInput contact derivativeDirection := by
  fin_cases derivativeDirection <;>
    ext formDirection internalPair <;>
    simp [directPrimitivePathLorentzJetCLM,
      baseCoordinate, coordinateDirection, Fin.sum_univ_four]

/-! ## One joint primitive path write -/

def directPrimitivePathCoframeRadialIncrement
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (point : BasePoint) : LorentzianCoframe :=
  fun internal coordinate =>
    ∫ᶜ contact in Path.segment (0 : BasePoint) point,
      directPrimitivePathCoframeJetCoordinateCLM source sectionInput contact
        internal coordinate

@[simp] theorem directPrimitivePathCoframeRadialIncrement_zero
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration) :
    directPrimitivePathCoframeRadialIncrement source sectionInput 0 = 0 := by
  ext internal coordinate
  simp [directPrimitivePathCoframeRadialIncrement]

def directPrimitivePathLorentzRadialIncrement
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (point : BasePoint) : LorentzBivectorOneForm :=
  ∫ᶜ contact in Path.segment (0 : BasePoint) point,
    directPrimitivePathLorentzJetCLM source sectionInput contact

@[simp] theorem directPrimitivePathLorentzRadialIncrement_zero
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration) :
    directPrimitivePathLorentzRadialIncrement source sectionInput 0 = 0 := by
  funext formDirection internalPair
  simp [directPrimitivePathLorentzRadialIncrement]

def directPrimitivePathCoframeField
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration) :
    BasePoint → LorentzianCoframe :=
  fun point =>
    sectionInput.coframe 0 +
      directPrimitivePathCoframeRadialIncrement source sectionInput point

@[simp] theorem directPrimitivePathCoframeField_zero
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration) :
    directPrimitivePathCoframeField source sectionInput 0 =
      sectionInput.coframe 0 := by
  rw [directPrimitivePathCoframeField,
    directPrimitivePathCoframeRadialIncrement_zero, add_zero]

def directPrimitivePathConnectionField
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration) : LorentzConnectionField :=
  fun point =>
    sectionInput.gravityConnection 0 +
      lorentzSkewConnectionOfBivectorOneForm
        (directPrimitivePathLorentzRadialIncrement source sectionInput point)

@[simp] theorem directPrimitivePathConnectionField_zero
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration) :
    directPrimitivePathConnectionField source sectionInput 0 =
      sectionInput.gravityConnection 0 := by
  funext formDirection internalOut internalIn
  simp [directPrimitivePathConnectionField]

/-- The second occurrence leg writes both primitive fields together and then
recomputes `B = II+(e)` on that same output. -/
def sourceActionGeneratedDiracDualDirectPrimitivePathWrite
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  let coframe := directPrimitivePathCoframeField source sectionInput
  { sectionInput with
    coframe := coframe
    gravityConnection := directPrimitivePathConnectionField source sectionInput
    gravityAuxiliary := fun point => physicalIIPlusBivector (coframe point) }

/-! ## Exact three-leg occurrence -/

inductive CompleteJointDirectPrimitivePathWriteLeg where
  | completeJointSection
  | jointPrimitivePath
  | liveReaction
  deriving DecidableEq

def completeJointDirectPrimitivePathActionWrite
    (source : SmoothUnifiedSource)
    (leg : CompleteJointDirectPrimitivePathWriteLeg)
    (before : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  match leg with
  | .completeJointSection =>
      sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionOperator
        source before
  | .jointPrimitivePath =>
      sourceActionGeneratedDiracDualDirectPrimitivePathWrite source before
  | .liveReaction => installFormNativeGravityReaction before

/-- One source/current-indexed occurrence for the three action writes. -/
inductive CompleteJointDirectPrimitivePathOccurrence
    (_source : SmoothUnifiedSource)
    (_current : StageNineHolonomicConfiguration) where
  | generated

def sourceActionGeneratedCompleteJointDirectPrimitivePathOccurrence
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    CompleteJointDirectPrimitivePathOccurrence source current :=
  .generated

namespace CompleteJointDirectPrimitivePathOccurrence

def before
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (_occurrence : CompleteJointDirectPrimitivePathOccurrence source current) :
    CompleteJointDirectPrimitivePathWriteLeg → StageNineHolonomicConfiguration
  | .completeJointSection => current
  | .jointPrimitivePath => directPrimitivePathPrefix source current
  | .liveReaction =>
      sourceActionGeneratedDiracDualDirectPrimitivePathWrite
        source (directPrimitivePathPrefix source current)

def after
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (_occurrence : CompleteJointDirectPrimitivePathOccurrence source current) :
    CompleteJointDirectPrimitivePathWriteLeg → StageNineHolonomicConfiguration
  | .completeJointSection => directPrimitivePathPrefix source current
  | .jointPrimitivePath =>
      sourceActionGeneratedDiracDualDirectPrimitivePathWrite
        source (directPrimitivePathPrefix source current)
  | .liveReaction =>
      installFormNativeGravityReaction
        (sourceActionGeneratedDiracDualDirectPrimitivePathWrite
          source (directPrimitivePathPrefix source current))

theorem after_eq_actionWrite
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence : CompleteJointDirectPrimitivePathOccurrence source current)
    (leg : CompleteJointDirectPrimitivePathWriteLeg) :
    occurrence.after leg =
      completeJointDirectPrimitivePathActionWrite
        source leg (occurrence.before leg) := by
  cases leg <;> rfl

@[simp] theorem completeJointSection_to_jointPrimitivePath_handoff
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence : CompleteJointDirectPrimitivePathOccurrence source current) :
    occurrence.after .completeJointSection =
      occurrence.before .jointPrimitivePath :=
  rfl

@[simp] theorem jointPrimitivePath_to_liveReaction_handoff
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence : CompleteJointDirectPrimitivePathOccurrence source current) :
    occurrence.after .jointPrimitivePath = occurrence.before .liveReaction :=
  rfl

abbrev finalActual
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence : CompleteJointDirectPrimitivePathOccurrence source current) :
    StageNineHolonomicConfiguration :=
  occurrence.after .liveReaction

end CompleteJointDirectPrimitivePathOccurrence

/-- Public source/current-only whole-field producer. -/
def sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  (sourceActionGeneratedCompleteJointDirectPrimitivePathOccurrence
    source current).finalActual

/-! ## Producer laws -/

theorem
    sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator_simplicity
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator
        source current) := by
  intro point
  rfl

theorem
    sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator_reactionSelfGenerated
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator
      source current).gravitySimplicityMultiplier =
      formNativeGravityReactionField
        (sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator
          source current) := by
  exact
    installFormNativeGravityReaction_reactionSelfGenerated
      (sourceActionGeneratedDiracDualDirectPrimitivePathWrite
        source (directPrimitivePathPrefix source current))

theorem
    sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator_auxiliaryEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    FormNativeGravityAuxiliaryEquation
      (sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator
        source current) := by
  exact
    installFormNativeGravityReaction_auxiliaryEquation
      (sourceActionGeneratedDiracDualDirectPrimitivePathWrite
        source (directPrimitivePathPrefix source current))

/-! ## Fixed P506/L0 specialization -/

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGlobalActual

def fixedP506L0ConstraintCauchyCompleteJointDirectPrimitivePathOccurrence :
    CompleteJointDirectPrimitivePathOccurrence Source Current :=
  sourceActionGeneratedCompleteJointDirectPrimitivePathOccurrence Source Current

def fixedP506L0ConstraintCauchyCompleteJointDirectPrimitivePathGlobalActual :
    StageNineHolonomicConfiguration :=
  fixedP506L0ConstraintCauchyCompleteJointDirectPrimitivePathOccurrence.finalActual

theorem
    fixedP506L0ConstraintCauchyCompleteJointDirectPrimitivePathGlobalActual_eq_actionWrite :
    fixedP506L0ConstraintCauchyCompleteJointDirectPrimitivePathGlobalActual =
      sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator
        Source Current :=
  rfl

theorem fixedP506L0ConstraintCauchyCompleteJointDirectPrimitivePath_simplicity :
    FormNativeGravitySimplicityEquation
      fixedP506L0ConstraintCauchyCompleteJointDirectPrimitivePathGlobalActual := by
  exact
    sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator_simplicity
      Source Current

theorem
    fixedP506L0ConstraintCauchyCompleteJointDirectPrimitivePath_auxiliaryEquation :
    FormNativeGravityAuxiliaryEquation
      fixedP506L0ConstraintCauchyCompleteJointDirectPrimitivePathGlobalActual := by
  exact
    sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator_auxiliaryEquation
      Source Current

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyCompleteJointDirectPrimitivePath
