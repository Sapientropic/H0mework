import H0mework.Versions.R2.Foundation.Cofinal.TemporalAnswer
import H0mework.Physics.ConstrainedCauchy.FixedDirectPrefixQuadraticCoframeBoundary
import H0mework.Physics.SafeCauchy.FixedRootRealization
import H0mework.Physics.SafeCauchy.FixedJointGlobalDevelopment
import H0mework.Physics.SafeCauchy.FixedJointGlobalECJetRegularity
import H0mework.Physics.SafeCauchy.FixedJointGlobalSmooth
import H0mework.Physics.SafeCauchy.FixedJointGlobalOriginResidualClosure
import H0mework.Physics.SafeCauchy.FixedECPathGravityTailInputRegularity
import H0mework.Physics.SynchronizedJoint.GravityTailOriginSettlement
import H0mework.Physics.GravityTail.FixedPrimitiveSeamClosure
import H0mework.Physics.ConstrainedCauchy.FixedWholeSpacetimeAssembly
import H0mework.Physics.Geometry.GravityTailPrimitiveFactorDisposition
import H0mework.Physics.GaugeAction.P286JointYangMillsGradientFlowRegularity
import H0mework.Physics.SynchronizedJoint.GravityTailJointPathGLCoframe

/-!
# Fixed P506/L0 gravity-tail action as one source-native root write
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace PhysicsCore
namespace StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathGLCoframe
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyDirectPrefixQuadraticCoframeBoundary
open StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeRootRealization
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalECJetRegularity
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalSmooth
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalOriginResidualClosure
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeECPathGravityTailInputRegularity
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailOriginSettlement
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailAllPointResidualNormalForm
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailJointPath
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyWholeSpacetimeAssembly
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineGravityTailPrimitiveFactorDisposition
open StageNineP286JointYangMillsGradientFlow
open StageNineP286JointYangMillsGradientFlowRegularity
open StageNineP286ActionCauchySplit
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineScalarPointwiseEquation
open StageNineSourceActionGeneratedSameHessianCauchySafeRealization

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev CartanBase : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECCauchyTemporalBase

private abbrev SafeRealizationOccurrence :=
  fixedP506L0CartanECConstraintCauchySafeRootRealizationOccurrence

private abbrev SafePrepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafePreparedActual

private abbrev SafeOccurrence :=
  fixedP506L0CartanECConstraintCauchySafeOccurrence

private abbrev SafeBase : StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source SafePrepared

private abbrev SafeJointOccurrence :=
  fixedP506L0CartanECConstraintCauchySafeJointGlobalOccurrence

private abbrev SafeECPath : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalECPathCurrent Source SafeBase

private abbrev SafeFinal : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeJointGlobalActual

private abbrev InitialConfiguration : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintPreparedActual

/-! ## One source-owned alternating physical current -/

/-- The dependent settlement token generated by the exact same-Hessian
Cauchy-safe repair and carried through every later physical current.  It has
no target, proof, or completed-geometry field; those are eliminated from the
fixed source occurrence below. -/
structure QuadraticCofaceSettlement where
  private mk ::

def quadraticCofaceSettlement : QuadraticCofaceSettlement := ⟨⟩

/-- The settlement target is eliminated from the zero-field token through
the fixed source-generated realization occurrence. -/
def QuadraticCofaceSettlement.target
    (_settlement : QuadraticCofaceSettlement) :
    StageNineHolonomicConfiguration :=
  SafePrepared

@[simp] theorem quadraticCofaceSettlement_target_eq_fixedOccurrence :
    quadraticCofaceSettlement.target = SafeRealizationOccurrence.after :=
  fixedP506L0CartanECConstraintCauchySafeRootRealization_after_eq_safePrepared.symm

@[simp] theorem quadraticCofaceSettlement_target_eq_sourceGeneratedWrite :
    quadraticCofaceSettlement.target =
      sourceActionGeneratedSameHessianCauchySafeRealizationWrite
        Source CartanBase := by
  rw [quadraticCofaceSettlement_target_eq_fixedOccurrence]
  exact SafeRealizationOccurrence.after_eq_actionWrite

theorem quadraticCofaceSettlement_target_nondegenerate :
    quadraticCofaceSettlement.target.Nondegenerate := by
  rw [quadraticCofaceSettlement_target_eq_fixedOccurrence]
  exact
    fixedP506L0CartanECConstraintCauchySafeRootRealization_after_nondegenerate

theorem quadraticCofaceSettlement_target_smooth :
    quadraticCofaceSettlement.target.Smooth := by
  rw [quadraticCofaceSettlement_target_eq_fixedOccurrence]
  exact fixedP506L0CartanECConstraintCauchySafeRootRealization_after_smooth

theorem quadraticCofaceSettlement_target_noncharacteristic
    (point : BasePoint) :
    coframeTemporalPrincipalScalar
        (quadraticCofaceSettlement.target.coframe point) ≠ 0 := by
  rw [quadraticCofaceSettlement_target_eq_fixedOccurrence]
  exact
    fixedP506L0CartanECConstraintCauchySafeRootRealization_after_noncharacteristic
      point

private inductive RootCurrentState
  | quadraticBoundary
  | quadraticCoface
  | gravity
      (settlement : QuadraticCofaceSettlement)
      (configuration : StageNineHolonomicConfiguration)
  | assembly
      (settlement : QuadraticCofaceSettlement)
      (configuration : StageNineHolonomicConfiguration)

/-- A physical root current is produced by this module's fixed source history.
The private constructor and sealed native-action token keep every
gravity/assembly configuration inside that generated history. -/
structure RootCurrent where
  private mk ::
  state : RootCurrentState

def RootCurrent.configuration :
    RootCurrent → StageNineHolonomicConfiguration
  | ⟨.quadraticBoundary⟩ => InitialConfiguration
  | ⟨.quadraticCoface⟩ => quadraticCofaceSettlement.target
  | ⟨.gravity _ configuration⟩ => configuration
  | ⟨.assembly _ configuration⟩ => configuration

inductive RootLawSurfaceExtensionAt : RootCurrent → Type
  | quadraticCoframe : RootLawSurfaceExtensionAt ⟨.quadraticBoundary⟩

def rootLawSurfaceExtensionTarget :
    {current : RootCurrent} → RootLawSurfaceExtensionAt current → RootCurrent
  | _, .quadraticCoframe => ⟨.quadraticCoface⟩

/-- A nonempty, definitionally connected sequence of native configuration
writes.  Every later source is the preceding material stage's target, so the
final configuration is computed from the trace rather than supplied beside
it. -/
inductive GeneratedConfigurationTraceAt :
    StageNineHolonomicConfiguration → Type
  | final {source : StageNineHolonomicConfiguration}
      (target : StageNineHolonomicConfiguration) :
      GeneratedConfigurationTraceAt source
  | step {source : StageNineHolonomicConfiguration}
      (middle : StageNineHolonomicConfiguration)
      (tail : GeneratedConfigurationTraceAt middle) :
      GeneratedConfigurationTraceAt source

namespace GeneratedConfigurationTraceAt

def finalConfiguration :
    {source : StageNineHolonomicConfiguration} →
      GeneratedConfigurationTraceAt source →
        StageNineHolonomicConfiguration
  | _, .final target => target
  | _, .step _ tail => tail.finalConfiguration

def edges :
    {source : StageNineHolonomicConfiguration} →
      GeneratedConfigurationTraceAt source →
        List (StageNineHolonomicConfiguration ×
          StageNineHolonomicConfiguration)
  | source, .final target => [(source, target)]
  | source, .step middle tail =>
      (source, middle) :: tail.edges

end GeneratedConfigurationTraceAt

/-- Private canonical P286 material stage executed inside every sealed
gravity action.  It accepts only the exact indexed current configuration and
the fixed root source; no constructor or branch is exposed to callers. -/
private def rootP286YangMillsStep
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  p286JointYangMillsEulerStep Source configuration

/-- Private post-gravity constitutive refresh.  The gravity material changes
the coframe while preserving the P286 connection; this final same-action
stage recomputes the auxiliary from that generated coframe and curvature.
It is an internal material edge, not another root visit. -/
private def rootPostGravityP286ConstitutiveRefresh
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  formNativeP286GaugeConstitutiveReadout Source configuration

private abbrev SafeFinalP286 : StageNineHolonomicConfiguration :=
  rootP286YangMillsStep SafeFinal

private theorem safeFinalP286_smooth : SafeFinalP286.Smooth :=
  p286JointYangMillsEulerStep_smooth Source SafeFinal
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_smooth
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_nondegenerate

private theorem safeFinalP286_nondegenerate : SafeFinalP286.Nondegenerate :=
  p286JointYangMillsEulerStep_nondegenerate Source SafeFinal
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_nondegenerate

/-- The P286 A/F/B stage changes neither the coframe nor the coframe first
jet used by the synchronized gravity base.  The proof follows the exact field
inventory: the EC contact preserves the primitive connection value, and the
Cartan torsion depends only on coframe, primal matter and conjugate matter. -/
private theorem gravityBase_coframe_p286Step
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (cartanECSynchronizedGravityTailBase source
        (p286JointYangMillsEulerStep source current)).coframe =
      (cartanECSynchronizedGravityTailBase source current).coframe := by
  unfold cartanECSynchronizedGravityTailBase
  change
    cartanECSynchronizedCenteredAffineCoframeField 0
        (diracDualFormNativeCartanECSynchronizedCoframeFirstJet source
          (p286JointYangMillsEulerStep source current) 0) =
      cartanECSynchronizedCenteredAffineCoframeField 0
        (diracDualFormNativeCartanECSynchronizedCoframeFirstJet source
          current 0)
  apply congrArg (cartanECSynchronizedCenteredAffineCoframeField 0)
  apply coframeJet_eq_of_fields_eq
  · exact congrFun (p286JointYangMillsEulerStep_coframe source current) 0
  · funext derivativeDirection internal coordinate
    unfold diracDualFormNativeCartanECSynchronizedCoframeFirstJet
    dsimp only
    rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact,
      sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact]
    rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe,
      sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe]
    rw [p286JointYangMillsEulerStep_coframe]
    have gravityConnectionEq :
        (p286JointYangMillsEulerStep source current).gravityConnection =
          current.gravityConnection :=
      rfl
    rw [gravityConnectionEq]
    have spinEq :
        diracDualFormNativeActionSpinResponseAt source
            (diracDualFormNativeCartanECSynchronizedECActual source
              (p286JointYangMillsEulerStep source current) 0) 0 =
          diracDualFormNativeActionSpinResponseAt source
            (diracDualFormNativeCartanECSynchronizedECActual source current 0)
            0 := by
      apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      · rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe,
          sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe]
        exact congrFun (p286JointYangMillsEulerStep_coframe source current) 0
      · rfl
      · rfl
    unfold diracDualFormNativeActionCartanTorsionAt
    rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe,
      sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe,
      p286JointYangMillsEulerStep_coframe, spinEq]

private abbrev SafeFinalP286GravityBase : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase Source SafeFinalP286

private theorem safeFinalP286GravityBase_smooth :
    SafeFinalP286GravityBase.Smooth :=
  cartanECSynchronizedGravityTailBase_smooth_of_currentSmooth Source
    SafeFinalP286 safeFinalP286_smooth

private theorem safeFinalP286GravityBase_coframe_origin :
    SafeFinalP286GravityBase.coframe 0 = SafeFinalP286.coframe 0 :=
  sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contact
    Source SafeFinalP286 0

private theorem safeFinalP286GravityBase_coframe_eq_one :
    SafeFinalP286GravityBase.coframe =
      fun _ => (1 : LorentzianCoframe) := by
  change
    (cartanECSynchronizedGravityTailBase Source
      (p286JointYangMillsEulerStep Source SafeFinal)).coframe = _
  rw [gravityBase_coframe_p286Step]
  exact
    fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_coframe_eq_one

private theorem safeFinalP286GravityBase_nondegenerate :
    SafeFinalP286GravityBase.Nondegenerate := by
  intro point
  rw [safeFinalP286GravityBase_coframe_eq_one]
  norm_num

private theorem safeFinalP286GravityBase_nondegenerate_origin :
    Matrix.det (SafeFinalP286GravityBase.coframe 0) ≠ 0 := by
  exact safeFinalP286GravityBase_nondegenerate 0

private abbrev SafeFinalP286GravityGL : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailGLPathOperator
    Source SafeFinalP286

private theorem safeFinalP286GravityGL_nondegenerate :
    SafeFinalP286GravityGL.Nondegenerate := by
  apply
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailGLPathOperator_nondegenerate
  exact safeFinalP286GravityBase_nondegenerate_origin

private theorem safeFinalP286GravityGL_smooth :
    SafeFinalP286GravityGL.Smooth :=
  sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailGLPathOperator_smooth
    Source SafeFinalP286 safeFinalP286GravityBase_smooth
      safeFinalP286GravityBase_nondegenerate

/-- The native action token can only be generated after its root current is
already available.  Its private constructor prevents a dependent action
index from being repackaged as a fresh arbitrary `RootCurrent`. -/
structure ActionAt (current : RootCurrent) : Type where
  private mk ::

/-- Dependent readout of the private P286 material stage carried by a sealed
action.  Non-gravity actions read their indexed source unchanged; callers
receive no constructor for either the stage or a new root current. -/
def ActionAt.p286Stage {current : RootCurrent}
    (_action : ActionAt current) : StageNineHolonomicConfiguration :=
  match current with
  | ⟨.gravity _ configuration⟩ => rootP286YangMillsStep configuration
  | _ => current.configuration

/-- The sealed action generates its connected material trace from the exact
indexed current.  No trace, endpoint, or completed equality is submitted by a
caller. -/
def ActionAt.generatedTrace {current : RootCurrent}
    (_action : ActionAt current) :
    GeneratedConfigurationTraceAt current.configuration :=
  match current with
  | ⟨.quadraticBoundary⟩ =>
      .final SafeRealizationOccurrence.after
  | ⟨.quadraticCoface⟩ =>
      .step SafeBase
        (.step (SafeJointOccurrence.after .temporal)
          (.step (SafeJointOccurrence.after .constitutive)
            (.step (SafeJointOccurrence.after .p286)
              (.step (SafeJointOccurrence.after .ecPath)
                (.step (SafeJointOccurrence.after .matterDual)
                  (.final (SafeJointOccurrence.after .reaction)))))))
  | ⟨.gravity _ _configuration⟩ =>
      let p286Next := _action.p286Stage
      let occurrence :=
        sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
          Source p286Next
      .step p286Next
        (.step (occurrence.after .cartanECSynchronized)
          (.step (occurrence.after .jointPrimitivePath)
            (.step (occurrence.after .liveReaction)
              (.final
                (rootPostGravityP286ConstitutiveRefresh
                  occurrence.finalActual)))))
  | ⟨.assembly _ configuration⟩ =>
      .final
        (sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
          Source configuration)

def rootActionAt (current : RootCurrent) : ActionAt current :=
  ⟨⟩

/-- The phase tag is determined by the indexed current, while every phase
which carries a configuration takes it only from the generated trace's final
material stage. -/
def actionTarget : {current : RootCurrent} → ActionAt current → RootCurrent
  | ⟨.quadraticBoundary⟩, _action => ⟨.quadraticCoface⟩
  | ⟨.quadraticCoface⟩, action =>
      ⟨.gravity quadraticCofaceSettlement
        action.generatedTrace.finalConfiguration⟩
  | ⟨.gravity settlement _⟩, action =>
      ⟨.assembly settlement action.generatedTrace.finalConfiguration⟩
  | ⟨.assembly settlement _⟩, action =>
      ⟨.gravity settlement action.generatedTrace.finalConfiguration⟩

/-- The root successor has no configuration-producing mouth independent of
the sealed native action and its connected material trace. -/
def Next (current : RootCurrent) : RootCurrent :=
  actionTarget (rootActionAt current)

/-- Eliminating a sealed action recovers the commuting law definitionally:
the trace's final material stage is the target current's configuration. -/
@[simp] theorem actionGeneratedTrace_finalConfiguration_eq_targetConfiguration
    {current : RootCurrent} (action : ActionAt current) :
    action.generatedTrace.finalConfiguration =
      (actionTarget action).configuration := by
  rcases current with ⟨state⟩
  cases state <;> rfl

def Initial : RootCurrent := ⟨.quadraticBoundary⟩

def quadraticCofaceCurrent : RootCurrent := ⟨.quadraticCoface⟩

def firstGravityCurrent : RootCurrent :=
  ⟨.gravity quadraticCofaceSettlement SafeFinal⟩

def firstAssemblyCurrent : RootCurrent :=
  Next firstGravityCurrent

def firstPostAssemblyGravityCurrent : RootCurrent :=
  Next firstAssemblyCurrent

@[simp] theorem next_initial_eq_quadraticCofaceCurrent :
    Next Initial = quadraticCofaceCurrent :=
  rfl

@[simp] theorem next_quadraticCoface_eq_firstGravityCurrent :
    Next quadraticCofaceCurrent = firstGravityCurrent :=
  rfl

@[simp] theorem next_firstGravityCurrent_eq_firstAssemblyCurrent :
    Next firstGravityCurrent = firstAssemblyCurrent :=
  rfl

@[simp] theorem next_firstAssemblyCurrent_eq_firstPostAssemblyGravityCurrent :
    Next firstAssemblyCurrent = firstPostAssemblyGravityCurrent :=
  rfl

/-- The native trace is the exact write list carried by each root action.  The
boundary phase performs the same-Hessian Cauchy-safe realization; the coface
phase continues through the qualified Cartan restart and joint post-EC
endpoint.  Later gravity occurrences retain their three-leg chronology. -/
def actionPathTraceAt (current : RootCurrent) :
    List (StageNineHolonomicConfiguration × StageNineHolonomicConfiguration) :=
  (rootActionAt current).generatedTrace.edges

@[simp] theorem actionPathTrace_quadraticBoundary :
    actionPathTraceAt Initial =
      [(SafeRealizationOccurrence.before,
        SafeRealizationOccurrence.after)] :=
  rfl

@[simp] theorem actionPathTrace_quadraticCoface :
    actionPathTraceAt quadraticCofaceCurrent =
      [ (SafeOccurrence.before .cartanRestart,
          SafeOccurrence.after .cartanRestart),
        (SafeJointOccurrence.before .temporal,
          SafeJointOccurrence.after .temporal),
        (SafeJointOccurrence.before .constitutive,
          SafeJointOccurrence.after .constitutive),
        (SafeJointOccurrence.before .p286,
          SafeJointOccurrence.after .p286),
        (SafeJointOccurrence.before .ecPath,
          SafeJointOccurrence.after .ecPath),
        (SafeJointOccurrence.before .matterDual,
          SafeJointOccurrence.after .matterDual),
        (SafeJointOccurrence.before .reaction,
          SafeJointOccurrence.after .reaction) ] :=
  rfl

/-- The coface native action computes the complete Cauchy-safe occurrence,
including its matter-dual and live-reaction writes.  The first gravity current
has no independent configuration input. -/
@[simp] theorem actionGeneratedTrace_quadraticCoface_finalConfiguration :
    (rootActionAt quadraticCofaceCurrent).generatedTrace.finalConfiguration =
      SafeFinal :=
  rfl

theorem actionLeg_is_sourceGenerated
    (current : StageNineHolonomicConfiguration)
    (leg : CartanECSynchronizedGravityTailGLWriteLeg) :
    (sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
      Source current).after leg =
      cartanECSynchronizedGravityTailGLActionWrite
        Source current leg
        ((sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
          Source current).before leg) :=
  (sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
    Source current).after_eq_actionWrite leg

@[simp] theorem actionPathTrace_cartan_joint_handoff
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
      Source current).after .cartanECSynchronized =
      (sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
        Source current).before .jointPrimitivePath :=
  (sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
    Source current).cartanECSynchronized_to_jointPrimitivePath_handoff

@[simp] theorem actionPathTrace_joint_reaction_handoff
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
      Source current).after .jointPrimitivePath =
      (sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
        Source current).before .liveReaction :=
  (sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
    Source current).jointPrimitivePath_to_liveReaction_handoff

@[simp] theorem actionPathTrace_source
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
      Source current).before .cartanECSynchronized = current :=
  rfl

@[simp] theorem actionPathTrace_writeBack
    (settlement : QuadraticCofaceSettlement)
    (current : StageNineHolonomicConfiguration) :
    rootPostGravityP286ConstitutiveRefresh
        (sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
          Source (rootP286YangMillsStep current)).finalActual =
      (Next ⟨.gravity settlement current⟩).configuration :=
  rfl

/-- The actual action occurrence is also the source-owned transfer receipt
for the singleton current-state responsibility. -/
inductive RootDispositionAt
    (support : RootCurrent) :
    WorldDispositionKind → Type
  | transfer (action : ActionAt support) :
      RootDispositionAt support .transfer
  | extensionTransfer (extension : RootLawSurfaceExtensionAt support) :
      RootDispositionAt support .transfer
  | lawSurfaceExtension (extension : RootLawSurfaceExtensionAt support) :
      RootDispositionAt support .lawSurfaceExtension

/-! ## Phase-exhaustive whole residual account -/

inductive RootCoframeBoundaryAccount
  | oldFailure
  | revised
  | settled
  deriving DecidableEq

instance : Zero RootCoframeBoundaryAccount := ⟨.settled⟩

/-- Complete first-jet exactification residual generated by one gravity
occurrence.  The two finite indices are the coframe row and coordinate; the
continuous-linear map retains every derivative direction. -/
abbrev GravityCoframeFirstJetResidual :=
  LorentzianIndex → LorentzianIndex → BasePoint →L[ℝ] ℝ

@[ext] structure RootResidualPayload where
  coframeBoundary : RootCoframeBoundaryAccount
  classicalJoint : BasePoint → DiracDualFormNativePointwiseJointResidualCarrier
  gravity : BasePoint → GravityTailActionJetSeam
  gravityCoframeFirstJet : BasePoint → GravityCoframeFirstJetResidual
  assembly : BasePoint → CompleteJointActionJetAssemblySeam

instance : Zero RootResidualPayload := ⟨⟨0, 0, 0, 0, 0⟩⟩

def rootResidualAt
    (support : RootCurrent) : RootResidualPayload :=
  match support with
  | ⟨.quadraticBoundary⟩ =>
      { coframeBoundary := .oldFailure
        classicalJoint :=
          diracDualFormNativeJointResidualSection Source support.configuration
        gravity := 0
        gravityCoframeFirstJet := 0
        assembly := 0 }
  | ⟨.quadraticCoface⟩ =>
      { coframeBoundary := .revised
        classicalJoint :=
          diracDualFormNativeJointResidualSection Source support.configuration
        gravity := 0
        gravityCoframeFirstJet := 0
        assembly := 0 }
  | ⟨.gravity _ configuration⟩ =>
      { coframeBoundary := .settled
        classicalJoint :=
          diracDualFormNativeJointResidualSection Source support.configuration
        gravity := fun point =>
          gravityTailActionJetSeam
            (generatedDiracDualFormNativePointwiseActionJet
              Source
              (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailGLPathOperator
                Source (rootP286YangMillsStep configuration)) point)
            (generatedDiracDualFormNativePointwiseActionJet
              Source
              (cartanECSynchronizedGravityTailProfileContact
                Source (rootP286YangMillsStep configuration) point) 0)
        gravityCoframeFirstJet := fun point internal coordinate =>
          cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
            Source (rootP286YangMillsStep configuration) point internal
              coordinate
        assembly := 0 }
  | ⟨.assembly _ configuration⟩ =>
      { coframeBoundary := .settled
        classicalJoint :=
          diracDualFormNativeJointResidualSection Source support.configuration
        gravity := 0
        gravityCoframeFirstJet := 0
        assembly := fun point =>
          candidateAssemblySeam Source configuration point }

/-- Exact whole residual responsibility at one world support. -/
structure RootOpenAt
    (support : RootCurrent)
    (responsibility : RootResidualPayload) : Type where
  responsibility_eq : responsibility = rootResidualAt support

/-- Nonzero whole-action seam is an exact obstruction read from the action
target; it is never an input to the action producer. -/
inductive RootResidualCoordinate
  | coframeBoundary
  | classicalJoint
  | gravity
  | gravityCoframeFirstJet
  | assembly

def RootResidualPayload.coordinateAt
    (payload : RootResidualPayload)
    (coordinate : RootResidualCoordinate) (point : BasePoint) : Type :=
  match coordinate with
  | .coframeBoundary =>
      PLift
        (payload.coframeBoundary = .oldFailure ∧
          point =
            fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint)
  | .classicalJoint => PLift (payload.classicalJoint point ≠ 0)
  | .gravity => PLift (payload.gravity point ≠ 0)
  | .gravityCoframeFirstJet =>
      PLift (payload.gravityCoframeFirstJet point ≠ 0)
  | .assembly => PLift (payload.assembly point ≠ 0)

private structure RootResidualObstructionPayloadAt
    (support : RootCurrent) : Type where
  coordinate : RootResidualCoordinate
  point : BasePoint
  evidence : (rootResidualAt support).coordinateAt coordinate point

/-- Root-owned obstruction vocabulary.  Its private constructor makes every
public obstruction a readout generated by this fixed source law. -/
structure RootResidualObstructionAt
    (support : RootCurrent) : Type where
  private mk ::
  payload : RootResidualObstructionPayloadAt support

namespace RootResidualObstructionAt

def point {support : RootCurrent} :
    RootResidualObstructionAt support → BasePoint
  | ⟨payload⟩ => payload.point

private def residual
    {support : RootCurrent}
    (coordinate : RootResidualCoordinate) (point : BasePoint)
    (nonzero : (rootResidualAt support).coordinateAt coordinate point) :
    RootResidualObstructionAt support :=
  ⟨⟨coordinate, point, nonzero⟩⟩

end RootResidualObstructionAt

/-- The sole public residual-obstruction constructor is a dependent read of
one coordinate of the exact root residual.  Choosing a presentation
coordinate cannot choose a branch, source, ledger row, or successor. -/
def rootResidualObstructionAt
    {support : RootCurrent}
    (coordinate : RootResidualCoordinate)
    (point : BasePoint)
    (evidence :
      (rootResidualAt support).coordinateAt coordinate point) :
    RootResidualObstructionAt support :=
  RootResidualObstructionAt.residual coordinate point evidence

/-- Semantic identity of the carried physical account or one exact rooted
obstruction.  The live account remains stable while its ledger payload
evolves; obstruction claims retain support, coordinate, point, and evidence. -/
inductive RootResidualClaim : Type
  | liveAccount
  | obstruction (rooted : Sigma RootResidualObstructionAt)

/-- The live-account standing is global to this fixed source history.  An
obstruction claim holds only at the exact support retained in its payload. -/
def RootResidualClaim.HoldsAt
    (support : RootCurrent) : RootResidualClaim → Type
  | .liveAccount => PUnit
  | .obstruction rooted => PLift (rooted.1 = support)

def rootNetwork : WorldRelationNetwork where
  Support := RootCurrent
  Anchor := SmoothUnifiedSource
  Incidence := RootCurrent
  Lineage := SmoothUnifiedSource
  Responsibility := RootResidualPayload
  Claim := RootResidualClaim
  anchorAt := fun _ => Source
  incidenceAt := id
  lineageAt := fun _ => Source
  OpenAt := RootOpenAt
  openClaimAt := fun _ => .liveAccount
  HoldsAt := RootResidualClaim.HoldsAt
  ObstructionAt := RootResidualObstructionAt
  obstructionClaim := fun {support} obstruction =>
    .obstruction ⟨support, obstruction⟩
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := RootDispositionAt

abbrev N := rootNetwork

/-- At fixed support the semantic claim retains the complete rooted
obstruction.  Equality cannot silently replace its coordinate, point, or
evidence with those of a sibling obstruction. -/
theorem rootObstructionClaim_injective
    (support : N.Support) :
    Function.Injective
      (fun obstruction : N.ObstructionAt support =>
        N.obstructionClaim obstruction) := by
  intro first second claimEq
  change RootResidualClaim.obstruction ⟨support, first⟩ =
    RootResidualClaim.obstruction ⟨support, second⟩ at claimEq
  injection claimEq with rootedEq
  cases rootedEq
  rfl

def rootLedgerEntry (current : RootCurrent) :
    OpenResponsibilityAt N current :=
  ⟨rootResidualAt current, ⟨rfl⟩⟩

theorem rootLedgerEntry_unique
    (current : RootCurrent)
    (entry : OpenResponsibilityAt N current) :
    entry = rootLedgerEntry current := by
  rcases entry with ⟨responsibility, openAt⟩
  rcases openAt with ⟨responsibility_eq⟩
  cases responsibility_eq
  rfl

def rootLedgerInventoryPresentation
    (current : RootCurrent) :
    ConstructivePresentation PUnit (OpenResponsibilityAt N current) where
  forward := fun _ => rootLedgerEntry current
  backward := fun _ => PUnit.unit
  backward_forward := fun _ => rfl
  forward_backward := fun entry => (rootLedgerEntry_unique current entry).symm

def rootVocabulary : ConstructiveRoot.Vocabulary where
  Current := RootCurrent
  Anchor := SmoothUnifiedSource
  Incidence := RootCurrent
  Lineage := SmoothUnifiedSource
  anchorAt := fun _ => Source
  incidenceAt := id
  lineageAt := fun _ => Source
  NativeWriteAt := ActionAt
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := actionTarget
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev V := rootVocabulary

/-- Support is already part of the primitive event identity. -/
structure RootNativeEventAt
    (current support : RootCurrent) : Type where
  support_eq : support = current

def rootEventAlgebra : SourceNativeEventAlgebra N V where
  EventAt := RootNativeEventAt
  compile := fun {current} {_support} _event =>
    .nativeWrite (rootActionAt current)
  AffectedInventoryAt := fun _ => PUnit
  affectedInventoryPresentation := by
    intro current support event
    cases event.support_eq
    exact rootLedgerInventoryPresentation current
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by
    intro current support event
    cases event.support_eq
    rfl
  incidence_commutes := by
    intro current support event
    cases event.support_eq
    rfl
  lineage_commutes := by
    intro current support event
    cases event.support_eq
    rfl

def rootSource : SourceNativeSource N V where
  initial := Initial
  law := rootEventAlgebra

def rootEmitted (current : RootCurrent) :
    rootSource.toRootSource.actual.OccurrenceAt current :=
  ⟨current, ⟨rfl⟩⟩

structure RootLedgerExactTransitionAt
    (current targetSupport : RootCurrent) : Type where
  targetSupport_eq : targetSupport = Next current

def rootLedgerWriteRowSource :
    LedgerWriteRowSourceAt rootSource (by
      intro current _occurrence targetSupport _sourceEntry _targetEntry
      exact RootLedgerExactTransitionAt current targetSupport) where
  IncidenceOccurrenceAt := by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact RootLedgerExactTransitionAt current targetSupport
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    change RootNativeEventAt current support at sourceEvent
    cases sourceEvent.support_eq
    cases event.targetSupport_eq
    cases rootLedgerEntry_unique current sourceEntry
    cases rootLedgerEntry_unique (Next current) targetEntry
    rcases current with ⟨state⟩
    cases state with
    | quadraticBoundary =>
        exact .transferred (.extensionTransfer .quadraticCoframe)
          rfl rfl (Nat.le_refl _)
    | quadraticCoface =>
        exact .transferred (.transfer (rootActionAt ⟨.quadraticCoface⟩))
          rfl rfl (Nat.le_refl _)
    | gravity settlement configuration =>
        exact .transferred
          (.transfer (rootActionAt ⟨.gravity settlement configuration⟩))
          rfl rfl (Nat.le_refl _)
    | assembly settlement configuration =>
        exact .transferred
          (.transfer (rootActionAt ⟨.assembly settlement configuration⟩))
          rfl rfl (Nat.le_refl _)
  compileExact := fun event => event

def rootLedgerTerminalRowSource : LedgerTerminalRowSourceAt rootSource :=
  LedgerTerminalRowSourceAt.empty _

def rootOccurrenceLedgerEntry
    {current : RootCurrent}
    (occurrence : rootSource.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt N occurrence.1 :=
  rootSource.law.affectedInventoryPresentation occurrence.2 |>.forward PUnit.unit

def rootLedgerGeneratedRowsAtOccurrence
    {current : RootCurrent}
    (occurrence : rootSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt rootLedgerWriteRowSource occurrence
      (⟨Next current⟩ : CompleteLiveLedgerAt N) where
  size := 1
  sourceEntryAt := fun _ => rootOccurrenceLedgerEntry occurrence
  targetEntryAt := fun _ => rootLedgerEntry (Next current)
  rowAt := fun _ => rootLedgerWriteRowSource.generate ⟨rfl⟩

def rootLedgerGeneratedCoverageAtOccurrence
    {current : RootCurrent}
    (occurrence : rootSource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt
      (rootLedgerGeneratedRowsAtOccurrence occurrence) where
  destinationIndex := fun _ => ⟨0, by simp [rootLedgerGeneratedRowsAtOccurrence]⟩
  originIndex := fun _ => ⟨0, by simp [rootLedgerGeneratedRowsAtOccurrence]⟩
  destination_sound := fun entry => by
    change rootOccurrenceLedgerEntry occurrence = entry
    exact
      (rootSource.law.affectedInventoryPresentation occurrence.2
        ).forward_backward entry
  origin_sound := fun entry =>
    (rootLedgerEntry_unique (Next current) entry).symm

def rootLedgerGeneratedPatchAtOccurrence
    {current : RootCurrent}
    (occurrence : rootSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt rootLedgerWriteRowSource occurrence
      (⟨Next current⟩ : CompleteLiveLedgerAt N) :=
  .complete (rootLedgerGeneratedRowsAtOccurrence occurrence)
    (rootLedgerGeneratedCoverageAtOccurrence occurrence)

def rootGeneratedLedgerEvolution
    {current : RootCurrent}
    (occurrence : rootSource.toRootSource.actual.OccurrenceAt current) :
  SourceNativeLedgerEvolutionAt rootSource occurrence := by
  rcases occurrence with ⟨support, event⟩
  change RootNativeEventAt current support at event
  cases event.support_eq
  rcases current with ⟨state⟩
  cases state with
  | quadraticBoundary =>
      exact .nativeWrite (rootActionAt ⟨.quadraticBoundary⟩) rfl
        (rootEmitted (Next ⟨.quadraticBoundary⟩))
        ((rootLedgerGeneratedPatchAtOccurrence
          ⟨⟨.quadraticBoundary⟩, event⟩).toLedgerWriteEvolution)
  | quadraticCoface =>
      exact .nativeWrite (rootActionAt ⟨.quadraticCoface⟩) rfl
        (rootEmitted (Next ⟨.quadraticCoface⟩))
        ((rootLedgerGeneratedPatchAtOccurrence
          ⟨⟨.quadraticCoface⟩, event⟩).toLedgerWriteEvolution)
  | gravity settlement configuration =>
      exact .nativeWrite (rootActionAt ⟨.gravity settlement configuration⟩) rfl
        (rootEmitted (Next ⟨.gravity settlement configuration⟩))
        ((rootLedgerGeneratedPatchAtOccurrence
          ⟨⟨.gravity settlement configuration⟩, event⟩).toLedgerWriteEvolution)
  | assembly settlement configuration =>
      exact .nativeWrite (rootActionAt ⟨.assembly settlement configuration⟩) rfl
        (rootEmitted (Next ⟨.assembly settlement configuration⟩))
        ((rootLedgerGeneratedPatchAtOccurrence
          ⟨⟨.assembly settlement configuration⟩, event⟩).toLedgerWriteEvolution)

def rootLedgerCompiler : SourceNativeLedgerCompiler rootSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact RootLedgerExactTransitionAt current targetSupport
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := rootLedgerWriteRowSource
  terminalRowSource := rootLedgerTerminalRowSource
  compile := rootGeneratedLedgerEvolution
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    change RootNativeEventAt current support at event
    cases event.support_eq
    rcases current with ⟨state⟩
    cases state with
    | quadraticBoundary =>
        exact
          ⟨rootLedgerGeneratedPatchAtOccurrence
            ⟨⟨.quadraticBoundary⟩, event⟩, rfl⟩
    | quadraticCoface =>
        exact
          ⟨rootLedgerGeneratedPatchAtOccurrence
            ⟨⟨.quadraticCoface⟩, event⟩, rfl⟩
    | gravity settlement configuration =>
        exact
          ⟨rootLedgerGeneratedPatchAtOccurrence
            ⟨⟨.gravity settlement configuration⟩, event⟩, rfl⟩
    | assembly settlement configuration =>
        exact
          ⟨rootLedgerGeneratedPatchAtOccurrence
            ⟨⟨.assembly settlement configuration⟩, event⟩, rfl⟩

def rootLedgerSource : SourceNativeLedgerSource N V where
  source := rootSource
  ledgerCompiler := rootLedgerCompiler

def sourceNativeRoot : SourceNativeLedgerRootClosure N V where
  source := rootLedgerSource
  emitted := rootEmitted
  compiler_commutes := by
    intro current
    rcases current with ⟨state⟩
    cases state <;> rfl

abbrev root : RootClosure N V := sourceNativeRoot.toRoot

/-- Every registered physical current is compiled by its own sealed native
action token.  The compiler has no occurrence-local premise beyond that
current and the fixed source law. -/
@[simp] theorem root_evolution_eq_nativeAction
    (current : RootCurrent) :
    root.evolutionAt current =
      EvolutionAt.nativeWrite (rootActionAt current) := by
  rcases current with ⟨state⟩
  cases state <;> rfl

/-- The same fixed compiler determines the next current at every history
position. -/
@[simp] theorem root_next_eq
    (current : RootCurrent) :
    (root.evolutionAt current).nextCurrent? = some (Next current) := by
  rw [root_evolution_eq_nativeAction]
  rfl

def initialVisit : RootVisit root := root.initialVisit

def initialTemporalVisit : SourceNativeTemporalVisitAt sourceNativeRoot :=
  .finite initialVisit

def initialTemporalEvent : ExactTemporalCausalRootEventAt
    sourceNativeRoot initialTemporalVisit :=
  sourceNativeRoot.exactTemporalCausalEventAt initialTemporalVisit

@[simp] theorem root_initial_evolution_eq_action :
    root.evolutionAt Initial =
      EvolutionAt.nativeWrite (rootActionAt Initial) :=
  rfl

@[simp] theorem root_initial_next_eq_quadraticCoface :
    (root.evolutionAt Initial).nextCurrent? =
      some quadraticCofaceCurrent :=
  rfl

@[simp] theorem root_quadraticCoface_evolution_eq_action :
    root.evolutionAt quadraticCofaceCurrent =
      EvolutionAt.nativeWrite (rootActionAt quadraticCofaceCurrent) :=
  rfl

@[simp] theorem root_quadraticCoface_next_eq_firstGravity :
    (root.evolutionAt quadraticCofaceCurrent).nextCurrent? =
      some firstGravityCurrent :=
  rfl

@[simp] theorem root_firstGravity_evolution_eq_action :
    root.evolutionAt firstGravityCurrent =
      EvolutionAt.nativeWrite (rootActionAt firstGravityCurrent) :=
  rfl

@[simp] theorem root_firstGravity_next_eq_firstAssembly :
    (root.evolutionAt firstGravityCurrent).nextCurrent? =
      some firstAssemblyCurrent :=
  rfl

@[simp] theorem root_initial_ledger_eq_current :
    (root.ledgerAt Initial).support = Initial :=
  rfl

@[simp] theorem root_initial_coframeBoundary_eq_oldFailure :
    (rootLedgerEntry Initial).1.coframeBoundary = .oldFailure :=
  rfl

@[simp] theorem root_initial_gravity_payload_eq_zero :
    (rootLedgerEntry Initial).1.gravity = 0 :=
  rfl

@[simp] theorem root_initial_assembly_payload_eq_zero :
    (rootLedgerEntry Initial).1.assembly = 0 :=
  rfl

@[simp] theorem root_quadraticCoface_coframeBoundary_eq_revised :
    (rootLedgerEntry quadraticCofaceCurrent).1.coframeBoundary = .revised :=
  rfl

@[simp] theorem root_firstGravity_coframeBoundary_eq_settled :
    (rootLedgerEntry firstGravityCurrent).1.coframeBoundary = .settled :=
  rfl

@[simp] theorem root_firstGravity_residual_payload_eq :
    (rootLedgerEntry firstGravityCurrent).1.gravity =
      fun point =>
        gravityTailActionJetSeam
          (generatedDiracDualFormNativePointwiseActionJet
            Source SafeFinalP286GravityGL point)
          (generatedDiracDualFormNativePointwiseActionJet Source
            (cartanECSynchronizedGravityTailProfileContact
              Source SafeFinalP286 point) 0) := by
  funext point
  rfl

/-- The complete repaired-action residual is a literal coordinate of the
same first-gravity whole-ledger row.  Its already generated origin zero is a
dependent readout, not a settlement field supplied to the root writer. -/
@[simp] theorem root_firstGravity_classicalJoint_origin_eq_zero :
    (rootResidualAt firstGravityCurrent).classicalJoint 0 = 0 := by
  change
    diracDualFormNativePointwiseJointResidual Source SafeFinal 0 = 0
  exact
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_residual_origin_zero

/-- The current S9-C repaired zero-fibre obligation is exactly settlement of
the newly installed whole-row coordinate. -/
theorem root_firstGravity_classicalJoint_eq_zero_iff :
    (rootResidualAt firstGravityCurrent).classicalJoint = 0 ↔
      DiracDualFormNativeJointZeroFiber Source SafeFinal :=
  Iff.rfl

/-- Pointwise readback of the same classical residual coordinate. -/
@[simp] theorem fixed_firstGravityClassicalJoint_is_root_residual_readout
    (point : BasePoint) :
    (rootResidualAt firstGravityCurrent).classicalJoint point =
      diracDualFormNativePointwiseJointResidual Source SafeFinal point :=
  rfl

@[simp] theorem root_firstGravity_assembly_payload_eq_zero :
    (rootLedgerEntry firstGravityCurrent).1.assembly = 0 :=
  rfl

@[simp] theorem root_firstAssembly_coframeBoundary_eq_settled :
    (rootLedgerEntry firstAssemblyCurrent).1.coframeBoundary = .settled :=
  rfl

/-- The compiler-generated assembly current is the post-gravity GL material
with its P286 auxiliary recomputed from that exact generated coframe and
curvature. -/
@[simp] theorem root_firstAssembly_configuration_eq_postGravityP286Refresh :
    firstAssemblyCurrent.configuration =
      formNativeP286GaugeConstitutiveReadout Source
        (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailGLPathOperator
          Source (rootActionAt firstGravityCurrent).p286Stage) :=
  rfl

/-- Smoothness is generated by the same material chain: the fixed P286 stage
preserves the identity gravity base, the C-infinity jet laws drive the GL
gravity operator, and the final constitutive refresh preserves smoothness. -/
theorem root_firstAssembly_smooth :
    firstAssemblyCurrent.configuration.Smooth := by
  rw [root_firstAssembly_configuration_eq_postGravityP286Refresh]
  exact formNativeP286GaugeConstitutiveReadout_smooth Source
    SafeFinalP286GravityGL safeFinalP286GravityGL_smooth
      safeFinalP286GravityGL_nondegenerate

/-- The GL gravity stage makes nondegeneracy a generated invariant of the
actual first assembly current; the constitutive refresh preserves it. -/
theorem root_firstAssembly_nondegenerate :
    firstAssemblyCurrent.configuration.Nondegenerate := by
  rw [root_firstAssembly_configuration_eq_postGravityP286Refresh]
  exact formNativeP286GaugeConstitutiveReadout_nondegenerate Source _
    safeFinalP286GravityGL_nondegenerate

/-- The post-gravity constitutive write settles the P286 auxiliary
coordinate at every point of the exact first-assembly whole-ledger row. -/
@[simp] theorem root_firstAssembly_p286GaugeAuxiliaryResidual_eq_zero
    (point : BasePoint) :
    ((rootResidualAt firstAssemblyCurrent).classicalJoint point
      ).p286GaugeAuxiliary = 0 := by
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
      (sourceGeneratedUnifiedCouplings Source)
      (toContinuumPointField firstAssemblyCurrent.configuration point) = 0
  rw [root_firstAssembly_configuration_eq_postGravityP286Refresh]
  rw [formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff]
  exact
    formNativeP286GaugeConstitutiveReadout_auxiliaryPointwiseEquation
      Source SafeFinalP286GravityGL safeFinalP286GravityGL_nondegenerate point

/-- Whole-section form of the same generated settlement. -/
theorem root_firstAssembly_p286GaugeAuxiliaryResidualSection_eq_zero :
    (fun point =>
      ((rootResidualAt firstAssemblyCurrent).classicalJoint point
        ).p286GaugeAuxiliary) = 0 := by
  funext point
  exact root_firstAssembly_p286GaugeAuxiliaryResidual_eq_zero point

/-- The GL gravity occurrence installs `II+(e)` before the final reaction;
the subsequent P286 constitutive refresh preserves those gravity fields. -/
@[simp] theorem root_firstAssembly_gravityMultiplierResidual_eq_zero
    (point : BasePoint) :
    ((rootResidualAt firstAssemblyCurrent).classicalJoint point
      ).gravityMultiplier = 0 := by
  change
    formNativeGravityMultiplierEulerResidual
      (toContinuumPointField firstAssemblyCurrent.configuration point) = 0
  rw [formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity]
  rw [root_firstAssembly_configuration_eq_postGravityP286Refresh]
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailGLPathOperator_simplicity
      Source SafeFinalP286 point

/-- The same GL occurrence recomputes the live gravity reaction, and the
post-gravity P286 refresh does not modify its multiplier or BF inputs. -/
@[simp] theorem root_firstAssembly_gravityAuxiliaryResidual_eq_zero
    (point : BasePoint) :
    ((rootResidualAt firstAssemblyCurrent).classicalJoint point
      ).gravityAuxiliary = 0 := by
  change
    formNativeGravityAuxiliaryEulerResidual
      (toContinuumPointField firstAssemblyCurrent.configuration point) = 0
  rw [root_firstAssembly_configuration_eq_postGravityP286Refresh]
  rw [show (rootActionAt firstGravityCurrent).p286Stage = SafeFinalP286 by rfl]
  rw [formNativeGravityAuxiliaryEulerResidual_formNativeP286GaugeConstitutiveReadout]
  exact congrFun
    (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailGLPathOperator_auxiliaryEquation
      Source SafeFinalP286) point

theorem root_firstAssembly_gravityMultiplierResidualSection_eq_zero :
    (fun point =>
      ((rootResidualAt firstAssemblyCurrent).classicalJoint point
        ).gravityMultiplier) = 0 := by
  funext point
  exact root_firstAssembly_gravityMultiplierResidual_eq_zero point

theorem root_firstAssembly_gravityAuxiliaryResidualSection_eq_zero :
    (fun point =>
      ((rootResidualAt firstAssemblyCurrent).classicalJoint point
        ).gravityAuxiliary) = 0 := by
  funext point
  exact root_firstAssembly_gravityAuxiliaryResidual_eq_zero point

/-- Exact algebraic three-coordinate settlement generated by one assembly
occurrence. -/
theorem root_firstAssembly_algebraicThreeCoordinateSections_eq_zero :
    (fun point =>
      ((rootResidualAt firstAssemblyCurrent).classicalJoint point
        ).gravityMultiplier) = 0 ∧
    (fun point =>
      ((rootResidualAt firstAssemblyCurrent).classicalJoint point
        ).gravityAuxiliary) = 0 ∧
    (fun point =>
      ((rootResidualAt firstAssemblyCurrent).classicalJoint point
        ).p286GaugeAuxiliary) = 0 :=
  ⟨root_firstAssembly_gravityMultiplierResidualSection_eq_zero,
    root_firstAssembly_gravityAuxiliaryResidualSection_eq_zero,
    root_firstAssembly_p286GaugeAuxiliaryResidualSection_eq_zero⟩

@[simp] theorem root_firstAssembly_residual_payload_eq :
    (rootLedgerEntry firstAssemblyCurrent).1.assembly =
      candidateAssemblySeam Source firstAssemblyCurrent.configuration :=
  rfl

/-- The post-YM assembly row is retained at its exact generic strength.  The
old identity-first-jet and origin divergence zeros belonged to the pre-YM
SafeFinal calibration and are not replayed onto this new actual. -/
theorem root_firstAssembly_residual_eq_zero_iff_openCoordinates_eq_zero
    (point : BasePoint) :
    (rootResidualAt firstAssemblyCurrent).assembly point = 0 ↔
      ((rootResidualAt firstAssemblyCurrent).assembly point
        ).gravityCurvature = 0 ∧
      ((rootResidualAt firstAssemblyCurrent).assembly point
        ).gravityAuxiliaryExteriorCovariantDerivative = 0 ∧
      ((rootResidualAt firstAssemblyCurrent).assembly point
        ).scalarDifferentialMomentumDivergence = 0 ∧
      ((rootResidualAt firstAssemblyCurrent).assembly point
        ).matterDifferentialMomentumDivergence = 0 :=
  candidateAssemblySeam_eq_zero_iff_openCoordinates_eq_zero Source
    firstAssemblyCurrent.configuration point

/-- Origin specialization of the same actual four-coordinate normal form.
No legacy identity jet is used to erase a newly computed coordinate. -/
theorem
    root_firstAssembly_origin_residual_eq_zero_iff_openCoordinates_eq_zero :
    (rootResidualAt firstAssemblyCurrent).assembly 0 = 0 ↔
      ((rootResidualAt firstAssemblyCurrent).assembly 0
        ).gravityCurvature = 0 ∧
      ((rootResidualAt firstAssemblyCurrent).assembly 0
        ).gravityAuxiliaryExteriorCovariantDerivative = 0 ∧
      ((rootResidualAt firstAssemblyCurrent).assembly 0
        ).scalarDifferentialMomentumDivergence = 0 ∧
      ((rootResidualAt firstAssemblyCurrent).assembly 0
        ).matterDifferentialMomentumDivergence = 0 :=
  root_firstAssembly_residual_eq_zero_iff_openCoordinates_eq_zero 0
@[simp] theorem root_firstAssembly_gravity_payload_eq_zero :
    (rootLedgerEntry firstAssemblyCurrent).1.gravity = 0 :=
  rfl

@[simp] theorem root_firstAssembly_evolution_is_wholeAssembly :
    root.evolutionAt firstAssemblyCurrent =
      EvolutionAt.nativeWrite (rootActionAt firstAssemblyCurrent) :=
  rfl

@[simp] theorem root_firstAssembly_next_eq_firstPostAssemblyGravity :
    (root.evolutionAt firstAssemblyCurrent).nextCurrent? =
      some firstPostAssemblyGravityCurrent :=
  rfl

/-- The second root write consumes the exact assembly residual carried by its
source current.  The target action jet is the existing same-action naturality
write-back, not a sibling fixed configuration or a separately supplied seam. -/
theorem root_firstPostAssembly_actionJet_eq_residualWriteBack
    (point : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet
        Source firstPostAssemblyGravityCurrent.configuration point =
      pointwiseActionJetWithCompleteJointAssemblySeam
        (contactActionJet Source firstAssemblyCurrent.configuration point)
        ((rootResidualAt firstAssemblyCurrent).assembly point) := by
  exact candidate_actionJet_naturality
    Source firstAssemblyCurrent.configuration point

@[simp] theorem root_initial_whole_writeBack_eq :
    HEq initialTemporalEvent.wholeLedgerWriteBack
      (sourceNativeRoot.generatedLedgerAt Initial) :=
  HEq.rfl

/-- The omitted coframe first-jet inventory is now an exact dependent
coordinate of the same first-gravity root occurrence. -/
@[simp] theorem fixed_firstGravityCoframeFirstJet_is_root_residual_readout
    (point : BasePoint) :
    (rootResidualAt firstGravityCurrent).gravityCoframeFirstJet point =
      fun internal coordinate =>
        cartanECSynchronizedGravityTailCoframeRadialFirstJetDefectCoordinate
          Source SafeFinalP286 point internal coordinate :=
  rfl

def fixedRootObstructionAt
    (point : BasePoint)
    (nonzero :
      (rootResidualAt firstGravityCurrent).gravity point ≠ 0) :
    N.ObstructionAt firstGravityCurrent :=
  rootResidualObstructionAt .gravity point <| by
      change PLift ((rootLedgerEntry firstGravityCurrent).1.gravity point ≠ 0)
      exact PLift.up nonzero

/-- Any nonzero repaired-action residual at the exact current is registered
inside the same root obstruction vocabulary and therefore uses the existing
same-row U7 answer-and-next path. -/
def rootClassicalJointObstructionAt
    {support : RootCurrent}
    (point : BasePoint)
    (nonzero :
      (rootResidualAt support).classicalJoint point ≠ 0) :
    N.ObstructionAt support :=
  rootResidualObstructionAt .classicalJoint point <| PLift.up nonzero

/-- SafeFinal specialization of the repaired-action obstruction mouth. -/
def fixedRootClassicalJointObstructionAt
    (point : BasePoint)
    (nonzero :
      (rootResidualAt firstGravityCurrent).classicalJoint point ≠ 0) :
    N.ObstructionAt firstGravityCurrent :=
  rootClassicalJointObstructionAt point nonzero

/-- Any exact root current carrying a nonzero first-jet family enters the
same obstruction vocabulary.  Non-gravity rows define this family as zero,
so they cannot inhabit this mouth. -/
def rootCoframeFirstJetObstructionAt
    {support : RootCurrent}
    (point : BasePoint)
    (nonzero :
      (rootResidualAt support).gravityCoframeFirstJet point ≠ 0) :
    N.ObstructionAt support :=
  rootResidualObstructionAt .gravityCoframeFirstJet point <|
    PLift.up nonzero

/-- First-gravity specialization retained for the named Stage-Ten prefix. -/
def fixedRootCoframeFirstJetObstructionAt
    (point : BasePoint)
    (nonzero :
      (rootResidualAt firstGravityCurrent).gravityCoframeFirstJet point ≠ 0) :
    N.ObstructionAt firstGravityCurrent :=
  rootCoframeFirstJetObstructionAt point nonzero

/-- A nonzero assembly seam is registered against the exact assembly current
that emitted it.  This constructor is the only public route from the
whole-spacetime readout into the root obstruction vocabulary. -/
def fixedRootAssemblyObstructionAt
    (point : BasePoint)
    (nonzero :
      (rootResidualAt firstAssemblyCurrent).assembly point ≠ 0) :
    N.ObstructionAt firstAssemblyCurrent :=
  rootResidualObstructionAt .assembly point <| PLift.up nonzero

/-- A nonzero gravity seam after the assembly write remains attached to that
exact emitted gravity current. -/
def fixedRootPostAssemblyGravityObstructionAt
    (point : BasePoint)
    (nonzero :
      (rootResidualAt firstPostAssemblyGravityCurrent).gravity point ≠ 0) :
    N.ObstructionAt firstPostAssemblyGravityCurrent :=
  rootResidualObstructionAt .gravity point <| PLift.up nonzero

/-- At the distinguished occurrence every nonzero assembly responsibility is
exactly the remaining gravity-curvature integrability seam. -/
def fixedRootAssemblyOriginGravityCurvatureObstructionAt
    (nonzero :
      ((rootResidualAt firstAssemblyCurrent).assembly 0
        ).gravityCurvature ≠ 0) :
    N.ObstructionAt firstAssemblyCurrent :=
  fixedRootAssemblyObstructionAt 0 <| by
    intro seamZero
    apply nonzero
    exact congrArg
      (fun seam : CompleteJointActionJetAssemblySeam => seam.gravityCurvature)
      seamZero

/-- The initial root occurrence carries the exact old-carrier determinant
failure.  This is the failure payload carried by the root boundary write,
not a free obstruction premise. -/
theorem fixedRootQuadraticCoframeBoundary_determinant_zero :
    Matrix.det
        (Initial.configuration.coframe
          fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint) =
      0 := by
  change
    Matrix.det
        (fixedP506L0CartanECConstraintPreparedActual.coframe
          fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint) =
      0
  exact fixedP506L0CartanECConstraintPreparedActual_determinant_zero

/-- The exact quadratic coframe failure registered at the initial root
current. -/
def fixedRootQuadraticCoframeBoundaryObstruction :
    N.ObstructionAt Initial :=
  rootResidualObstructionAt .coframeBoundary
    fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint
    (PLift.up ⟨rfl, rfl⟩)

@[simp] theorem fixedRootQuadraticCoframeBoundaryObstruction_point :
    fixedRootQuadraticCoframeBoundaryObstruction.point =
      fixedP506L0ConstraintCauchyDirectPrefixQuadraticCoframeSingularPoint :=
  rfl

/-- The generated quadratic-boundary obstruction is not the canonical origin.
The proof uses the source determinant failure itself, not a coordinate-level
choice hidden in the obstruction constructor. -/
theorem fixedRootQuadraticCoframeBoundaryObstruction_point_ne_origin :
    fixedRootQuadraticCoframeBoundaryObstruction.point ≠ 0 := by
  intro point_eq
  have determinant_zero :=
    fixedRootQuadraticCoframeBoundary_determinant_zero
  rw [← fixedRootQuadraticCoframeBoundaryObstruction_point, point_eq]
    at determinant_zero
  change Matrix.det (SafeRealizationOccurrence.before.coframe 0) = 0
    at determinant_zero
  rw [fixedP506L0CartanECConstraintCauchySafeRootRealization_before_eq_quadraticPrepared,
    fixedP506L0CartanECConstraintPreparedActual_coframe_origin]
    at determinant_zero
  simp at determinant_zero

end
end StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
end PhysicsCore
end SaturationMonoid
