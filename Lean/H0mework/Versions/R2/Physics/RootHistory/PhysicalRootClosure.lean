import H0mework.Versions.R2.Physics.GravityTail.FixedRootU7AnswerNext

/-!
# Stage Ten fixed physical root closure

The fixed closed physical source generates one temporal root history.  Its
gravity and whole-spacetime assembly occurrences are retained here together
with the exact Stage-Nine action payloads that they realize.  Per-action
recognition is dependent data of this single closure.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.PhysicsCore
namespace StageTenPhysicalRoot

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathGLCoframe
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailAllPointResidualNormalForm
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailLivingRoot
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootU7AnswerNext
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyWholeSpacetimeAssembly
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineFormNativeP286GaugeYangMillsReadout

noncomputable section

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource
private abbrev InitialCurrent : RootCurrent := Initial
private abbrev CofaceCurrent : RootCurrent := quadraticCofaceCurrent
private abbrev GravityCurrent : RootCurrent := firstGravityCurrent
private abbrev AssemblyCurrent : RootCurrent := firstAssemblyCurrent
private abbrev PostAssemblyCurrent : RootCurrent := firstPostAssemblyGravityCurrent
private abbrev GravityP286 : StageNineHolonomicConfiguration :=
  (rootActionAt GravityCurrent).p286Stage

private abbrev GravityDomainAction :=
  CartanECSynchronizedGravityTailGLOccurrence Source
    GravityP286

/-- The single public Stage-Ten formal credential.  Its private constructor
retains both domain payloads as dependent fields of the fixed compiler image. -/
structure StageTenPhysicalRootClosure : Type 2 where
  private mk ::
  initialEvent : ExactTemporalCausalRootEventAt
    sourceNativeRoot initialTemporalVisit
  initialEvent_eq : initialEvent =
    sourceNativeRoot.generatedAtTemporalVisit initialTemporalVisit
  cofaceEvent : ExactTemporalCausalRootEventAt
    sourceNativeRoot nextTemporalVisit
  cofaceEvent_eq : cofaceEvent =
    sourceNativeRoot.generatedAtTemporalVisit nextTemporalVisit
  gravityEvent : ExactTemporalCausalRootEventAt
    sourceNativeRoot afterCofaceTemporalVisit
  gravityEvent_eq : gravityEvent =
    sourceNativeRoot.generatedAtTemporalVisit afterCofaceTemporalVisit
  gravityAction : GravityDomainAction
  gravityAction_eq : gravityAction =
    sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
      Source GravityP286
  assemblyEvent : ExactTemporalCausalRootEventAt
    sourceNativeRoot afterGravityTemporalVisit
  assemblyEvent_eq : assemblyEvent =
    sourceNativeRoot.generatedAtTemporalVisit afterGravityTemporalVisit
  postAssemblyEvent : ExactTemporalCausalRootEventAt
    sourceNativeRoot afterAssemblyTemporalVisit
  postAssemblyEvent_eq : postAssemblyEvent =
    sourceNativeRoot.generatedAtTemporalVisit afterAssemblyTemporalVisit
  wholeSpacetimeWriter : StageNineHolonomicConfiguration
  wholeSpacetimeWriter_eq : wholeSpacetimeWriter =
    sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
      Source AssemblyCurrent.configuration

/-- The fixed closed source generates every field of the physical root closure. -/
def stageTenPhysicalRootClosure : StageTenPhysicalRootClosure where
  initialEvent :=
    sourceNativeRoot.generatedAtTemporalVisit initialTemporalVisit
  initialEvent_eq := rfl
  cofaceEvent :=
    sourceNativeRoot.generatedAtTemporalVisit nextTemporalVisit
  cofaceEvent_eq := rfl
  gravityEvent :=
    sourceNativeRoot.generatedAtTemporalVisit afterCofaceTemporalVisit
  gravityEvent_eq := rfl
  gravityAction :=
    sourceActionGeneratedCartanECSynchronizedGravityTailGLOccurrence
      Source GravityP286
  gravityAction_eq := rfl
  assemblyEvent :=
    sourceNativeRoot.generatedAtTemporalVisit afterGravityTemporalVisit
  assemblyEvent_eq := rfl
  postAssemblyEvent :=
    sourceNativeRoot.generatedAtTemporalVisit afterAssemblyTemporalVisit
  postAssemblyEvent_eq := rfl
  wholeSpacetimeWriter :=
    sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
      Source AssemblyCurrent.configuration
  wholeSpacetimeWriter_eq := rfl

/-- Every closure is the fixed compiler image at all five history positions. -/
theorem StageTenPhysicalRootClosure.eq_generated
    (candidate : StageTenPhysicalRootClosure) :
    candidate = stageTenPhysicalRootClosure := by
  rcases candidate with
    ⟨initialEvent, initialEvent_eq, cofaceEvent, cofaceEvent_eq,
      gravityEvent, gravityEvent_eq, gravityAction, gravityAction_eq,
      assemblyEvent, assemblyEvent_eq, postAssemblyEvent,
      postAssemblyEvent_eq, wholeSpacetimeWriter,
      wholeSpacetimeWriter_eq⟩
  cases initialEvent_eq
  cases cofaceEvent_eq
  cases gravityEvent_eq
  cases gravityAction_eq
  cases assemblyEvent_eq
  cases postAssemblyEvent_eq
  cases wholeSpacetimeWriter_eq
  rfl

/-- The installed physical history has five registered positions.  Adding an
authority-bearing stage extends the fixed root history and recompiles this
closure. -/
inductive PhysicalHistoryPosition
  | boundary
  | coface
  | gravity
  | assembly
  | postAssembly

def PhysicalHistoryPosition.visitAt :
    PhysicalHistoryPosition → SourceNativeTemporalVisitAt sourceNativeRoot
  | .boundary => initialTemporalVisit
  | .coface => nextTemporalVisit
  | .gravity => afterCofaceTemporalVisit
  | .assembly => afterGravityTemporalVisit
  | .postAssembly => afterAssemblyTemporalVisit

def PhysicalHistoryPosition.currentAt : PhysicalHistoryPosition → RootCurrent
  | .boundary => InitialCurrent
  | .coface => CofaceCurrent
  | .gravity => GravityCurrent
  | .assembly => AssemblyCurrent
  | .postAssembly => PostAssemblyCurrent

@[simp] theorem PhysicalHistoryPosition.visitAt_current
    (position : PhysicalHistoryPosition) :
    position.visitAt.current = position.currentAt := by
  cases position <;> rfl

/-- Exact compiler occurrence at one installed physical history position. -/
def StageTenPhysicalRootClosure.eventAt
    (closure : StageTenPhysicalRootClosure)
    (position : PhysicalHistoryPosition) :
    ExactTemporalCausalRootEventAt sourceNativeRoot position.visitAt :=
  match position with
  | .boundary => closure.initialEvent
  | .coface => closure.cofaceEvent
  | .gravity => closure.gravityEvent
  | .assembly => closure.assemblyEvent
  | .postAssembly => closure.postAssemblyEvent

@[simp] theorem StageTenPhysicalRootClosure.eventAt_eq_generated
    (closure : StageTenPhysicalRootClosure)
    (position : PhysicalHistoryPosition) :
    closure.eventAt position =
      sourceNativeRoot.generatedAtTemporalVisit position.visitAt := by
  cases position with
  | boundary => exact closure.initialEvent_eq
  | coface => exact closure.cofaceEvent_eq
  | gravity => exact closure.gravityEvent_eq
  | assembly => exact closure.assemblyEvent_eq
  | postAssembly => exact closure.postAssemblyEvent_eq

/-- Every admitted Physics authority coordinate is read directly from one
exact closure occurrence; domain theorems consume it as a dependent readout. -/
def StageTenPhysicalRootClosure.authorityOutcomeAt
    (closure : StageTenPhysicalRootClosure)
    (position : PhysicalHistoryPosition)
    (projection : RootProjectionCoordinate) :=
  SourceNativeTemporalVisitGeneratedEvolutionAt.projectionOutcome
    (world := authoritativeRoot) (closure.eventAt position) projection

theorem StageTenPhysicalRootClosure.authorityOutcome_factorizes
    (closure : StageTenPhysicalRootClosure)
    (position : PhysicalHistoryPosition)
    (projection : RootProjectionCoordinate) :
    HEq (closure.authorityOutcomeAt position projection)
      (authoritativeRoot.projectionOutcomeAt projection position.currentAt) := by
  cases position with
  | boundary =>
      exact SourceNativeTemporalVisitGeneratedEvolutionAt.projectionOutcome_heq_sourceOutcome
        (world := authoritativeRoot) closure.initialEvent projection
  | coface =>
      exact SourceNativeTemporalVisitGeneratedEvolutionAt.projectionOutcome_heq_sourceOutcome
        (world := authoritativeRoot) closure.cofaceEvent projection
  | gravity =>
      exact SourceNativeTemporalVisitGeneratedEvolutionAt.projectionOutcome_heq_sourceOutcome
        (world := authoritativeRoot) closure.gravityEvent projection
  | assembly =>
      exact SourceNativeTemporalVisitGeneratedEvolutionAt.projectionOutcome_heq_sourceOutcome
        (world := authoritativeRoot) closure.assemblyEvent projection
  | postAssembly =>
      exact SourceNativeTemporalVisitGeneratedEvolutionAt.projectionOutcome_heq_sourceOutcome
        (world := authoritativeRoot) closure.postAssemblyEvent projection

/-- The exact occurrence anchor supplies the full proof-free source and its
continuous-contact residual. -/
@[simp] theorem StageTenPhysicalRootClosure.sourceOutcome_eq
    (closure : StageTenPhysicalRootClosure)
    (position : PhysicalHistoryPosition) :
    closure.authorityOutcomeAt position .source =
      .inl ⟨PUnit.unit, N.anchorAt position.currentAt⟩ := by
  cases position <;> rfl

/-- The complete physical carrier at every installed history position is
read from that position's exact root occurrence. -/
@[simp] theorem StageTenPhysicalRootClosure.configurationOutcome_eq
    (closure : StageTenPhysicalRootClosure)
    (position : PhysicalHistoryPosition) :
    closure.authorityOutcomeAt position .configuration =
      .inl ⟨PUnit.unit, position.currentAt.configuration⟩ := by
  cases position <;> rfl

/-- Final formal authority receipt for the physical root inventory.  Every
projection at every source-native temporal visit is the dependent image of the
fixed compiler; the private constructor seals this complete inventory. -/
structure ZeroUnregisteredPhysicalAuthorityReceipt : Prop where
  private mk ::
  evolutionFactorizes : ∀
      (visit : SourceNativeTemporalVisitAt sourceNativeRoot),
    root.evolutionAt visit.current =
      EvolutionAt.nativeWrite (rootActionAt visit.current)
  nextFactorizes : ∀
      (visit : SourceNativeTemporalVisitAt sourceNativeRoot),
    (root.evolutionAt visit.current).nextCurrent? =
      some (Next visit.current)
  factorizes : ∀
      (visit : SourceNativeTemporalVisitAt sourceNativeRoot)
      (projection : RootProjectionCoordinate),
    HEq
      (SourceNativeTemporalVisitGeneratedEvolutionAt.projectionOutcome
        (world := authoritativeRoot)
        (sourceNativeRoot.generatedAtTemporalVisit visit) projection)
      (authoritativeRoot.projectionOutcomeAt projection visit.current)
  /-- The lifecycle adapter's `PUnit` residual is only a seal.  The actual
  responsibility content in every registered row is the complete physical
  residual generated at that exact current. -/
  responsibilityFactorizes : ∀
      (visit : SourceNativeTemporalVisitAt sourceNativeRoot),
    (rootOccurrenceLedgerEntry
      (sourceNativeRoot.generatedAtTemporalVisit visit).occurrence).1 =
        rootResidualAt visit.current
  /-- Every actual coordinate of every reachable residual row has one common
  positive route into same-row U7 and the compiler-owned successor. -/
  obstructionFactorizes : ∀
      (visit : SourceNativeTemporalVisitAt sourceNativeRoot)
      (coordinate : RootResidualCoordinate)
      (point : BasePoint)
      (evidence :
        (rootResidualAt visit.current).coordinateAt coordinate point),
    (rootResidualDemandAt coordinate point evidence).entry =
        rootOccurrenceLedgerEntry
          (sourceNativeRoot.generatedAtTemporalVisit visit).occurrence ∧
      Nonempty
        (SourceNativeRootResidualAnswerAndNextAt visit
          (rootResidualObstructionAt coordinate point evidence)
          (rootCausalEntryAuthorityAt visit))

theorem zeroUnregisteredPhysicalAuthorityReceipt :
    ZeroUnregisteredPhysicalAuthorityReceipt where
  evolutionFactorizes := fun visit =>
    root_evolution_eq_nativeAction visit.current
  nextFactorizes := fun visit =>
    root_next_eq visit.current
  factorizes := fun visit projection =>
    SourceNativeTemporalVisitGeneratedEvolutionAt.projectionOutcome_heq_sourceOutcome
      (world := authoritativeRoot)
      (sourceNativeRoot.generatedAtTemporalVisit visit) projection
  responsibilityFactorizes := by
    intro visit
    rcases visit with ⟨current, history⟩
    rcases current with ⟨state⟩
    cases state <;> rfl
  obstructionFactorizes :=
    fun visit coordinate point evidence =>
      ⟨rfl,
        ⟨sourceGeneratedRootResidualAnswerAndNextAt
          visit coordinate point evidence⟩⟩

theorem ZeroUnregisteredPhysicalAuthorityReceipt.eq_generated
    (candidate : ZeroUnregisteredPhysicalAuthorityReceipt) :
    candidate = zeroUnregisteredPhysicalAuthorityReceipt :=
  Subsingleton.elim _ _

/-! ## Fixed-source temporal history -/

@[simp] theorem StageTenPhysicalRootClosure.initial_evolution_eq
    (_closure : StageTenPhysicalRootClosure) :
    root.evolutionAt InitialCurrent =
      EvolutionAt.nativeWrite (rootActionAt InitialCurrent) :=
  root_initial_evolution_eq_action

@[simp] theorem StageTenPhysicalRootClosure.initial_next_eq
    (_closure : StageTenPhysicalRootClosure) :
    (root.evolutionAt InitialCurrent).nextCurrent? = some CofaceCurrent :=
  root_initial_next_eq_quadraticCoface

theorem StageTenPhysicalRootClosure.initial_wholeLedgerWriteBack_eq
    (closure : StageTenPhysicalRootClosure) :
    HEq closure.initialEvent.wholeLedgerWriteBack
      (rootLedgerCompiler.compile (rootEmitted InitialCurrent)) := by
  rw [closure.initialEvent_eq]
  exact HEq.rfl

@[simp] theorem StageTenPhysicalRootClosure.initial_sourceEntry_eq
    (closure : StageTenPhysicalRootClosure) :
    rootOccurrenceLedgerEntry closure.initialEvent.occurrence =
      rootLedgerEntry InitialCurrent := by
  rw [closure.initialEvent_eq]
  rfl

@[simp] theorem StageTenPhysicalRootClosure.coface_evolution_eq
    (_closure : StageTenPhysicalRootClosure) :
    root.evolutionAt CofaceCurrent =
      EvolutionAt.nativeWrite (rootActionAt CofaceCurrent) :=
  root_quadraticCoface_evolution_eq_action

@[simp] theorem StageTenPhysicalRootClosure.coface_next_eq
    (_closure : StageTenPhysicalRootClosure) :
    (root.evolutionAt CofaceCurrent).nextCurrent? = some GravityCurrent :=
  root_quadraticCoface_next_eq_firstGravity

theorem StageTenPhysicalRootClosure.coface_wholeLedgerWriteBack_eq
    (closure : StageTenPhysicalRootClosure) :
    HEq closure.cofaceEvent.wholeLedgerWriteBack
      (rootLedgerCompiler.compile (rootEmitted CofaceCurrent)) := by
  rw [closure.cofaceEvent_eq]
  exact HEq.rfl

@[simp] theorem StageTenPhysicalRootClosure.coface_sourceEntry_eq
    (closure : StageTenPhysicalRootClosure) :
    rootOccurrenceLedgerEntry closure.cofaceEvent.occurrence =
      rootLedgerEntry CofaceCurrent := by
  rw [closure.cofaceEvent_eq]
  rfl

/-! ## Internal gravity recognition readouts -/

@[simp] theorem StageTenPhysicalRootClosure.gravity_anchor_eq
    (_closure : StageTenPhysicalRootClosure) :
    N.anchorAt GravityCurrent = Source :=
  rfl

@[simp] theorem StageTenPhysicalRootClosure.gravity_incidence_eq
    (_closure : StageTenPhysicalRootClosure) :
    N.incidenceAt GravityCurrent = GravityCurrent :=
  rfl

@[simp] theorem StageTenPhysicalRootClosure.gravity_lineage_eq
    (_closure : StageTenPhysicalRootClosure) :
    N.lineageAt GravityCurrent = Source :=
  rfl

@[simp] theorem StageTenPhysicalRootClosure.lawSurface_eq
    (_closure : StageTenPhysicalRootClosure) :
    authoritativeRoot.source.lawSurface = .rootSemantic N :=
  rfl

@[simp] theorem StageTenPhysicalRootClosure.gravity_evolution_eq
    (_closure : StageTenPhysicalRootClosure) :
    root.evolutionAt GravityCurrent =
      EvolutionAt.nativeWrite (rootActionAt GravityCurrent) := by
  exact root_firstGravity_evolution_eq_action

@[simp] theorem StageTenPhysicalRootClosure.gravity_source_eq
    (closure : StageTenPhysicalRootClosure) :
    closure.gravityAction.before .cartanECSynchronized =
      GravityP286 := by
  rw [closure.gravityAction_eq]
  rfl

@[simp] theorem StageTenPhysicalRootClosure.gravity_cartan_handoff
    (closure : StageTenPhysicalRootClosure) :
    closure.gravityAction.after .cartanECSynchronized =
      closure.gravityAction.before .jointPrimitivePath := by
  rw [closure.gravityAction_eq]
  rfl

@[simp] theorem StageTenPhysicalRootClosure.gravity_joint_handoff
    (closure : StageTenPhysicalRootClosure) :
    closure.gravityAction.after .jointPrimitivePath =
      closure.gravityAction.before .liveReaction := by
  rw [closure.gravityAction_eq]
  rfl

@[simp] theorem StageTenPhysicalRootClosure.gravity_target_eq
    (closure : StageTenPhysicalRootClosure) :
    formNativeP286GaugeConstitutiveReadout Source
        (closure.gravityAction.after .liveReaction) =
      AssemblyCurrent.configuration := by
  rw [closure.gravityAction_eq]
  rfl

@[simp] theorem StageTenPhysicalRootClosure.gravity_pathTrace_eq
    (closure : StageTenPhysicalRootClosure) :
    actionPathTraceAt GravityCurrent =
      [ (GravityCurrent.configuration, GravityP286),
        (closure.gravityAction.before .cartanECSynchronized,
          closure.gravityAction.after .cartanECSynchronized),
        (closure.gravityAction.before .jointPrimitivePath,
          closure.gravityAction.after .jointPrimitivePath),
        (closure.gravityAction.before .liveReaction,
          closure.gravityAction.after .liveReaction),
        (closure.gravityAction.after .liveReaction,
          AssemblyCurrent.configuration) ] := by
  rw [closure.gravityAction_eq]
  rfl

@[simp] theorem StageTenPhysicalRootClosure.gravity_next_eq
    (_closure : StageTenPhysicalRootClosure) :
    (root.evolutionAt GravityCurrent).nextCurrent? = some AssemblyCurrent :=
  rfl

theorem StageTenPhysicalRootClosure.gravity_wholeLedgerWriteBack_eq
    (closure : StageTenPhysicalRootClosure) :
    HEq closure.gravityEvent.wholeLedgerWriteBack
      (rootLedgerCompiler.compile (rootEmitted GravityCurrent)) := by
  rw [closure.gravityEvent_eq]
  exact HEq.rfl

@[simp] theorem StageTenPhysicalRootClosure.gravity_sourceEntry_eq
    (closure : StageTenPhysicalRootClosure) :
    rootOccurrenceLedgerEntry closure.gravityEvent.occurrence =
      rootLedgerEntry GravityCurrent := by
  rw [closure.gravityEvent_eq]
  rfl

/-- The repaired Dirac joint residual is installed in the exact SafeFinal
whole-ledger row, not kept as an adjacent analytic diagnostic. -/
theorem StageTenPhysicalRootClosure.gravity_classicalJointRow_eq
    (closure : StageTenPhysicalRootClosure) :
    (rootOccurrenceLedgerEntry
      closure.gravityEvent.occurrence).1.classicalJoint =
      diracDualFormNativeJointResidualSection
        Source GravityCurrent.configuration := by
  rw [closure.gravity_sourceEntry_eq]
  rfl

/-- The source-generated SafeFinal origin is already on the repaired-action
zero fibre inside that same row. -/
@[simp] theorem StageTenPhysicalRootClosure.gravity_classicalJoint_origin_eq_zero
    (_closure : StageTenPhysicalRootClosure) :
    (rootResidualAt GravityCurrent).classicalJoint 0 = 0 :=
  root_firstGravity_classicalJoint_origin_eq_zero

@[simp] theorem StageTenPhysicalRootClosure.gravity_targetEntry_eq
    (_closure : StageTenPhysicalRootClosure) :
    rootOccurrenceLedgerEntry (rootEmitted AssemblyCurrent) =
      rootLedgerEntry AssemblyCurrent :=
  rfl

/-- The exact gravity occurrence's generated target action jet is unchanged
exactly when that point of the same live gravity residual is settled.  Both
the target and its native contact are read through the closure's dependent
gravity action; neither is supplied by the caller. -/
theorem StageTenPhysicalRootClosure.gravity_registeredActionJet_eq_contact_iff
    (closure : StageTenPhysicalRootClosure)
    (point : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet
        Source (closure.gravityAction.after .liveReaction) point =
      generatedDiracDualFormNativePointwiseActionJet Source
        (cartanECSynchronizedGravityTailProfileContact Source
          (closure.gravityAction.before .cartanECSynchronized) point) 0 ↔
      (rootResidualAt GravityCurrent).gravity point = 0 := by
  rw [closure.gravityAction_eq]
  let outputJet :=
    generatedDiracDualFormNativePointwiseActionJet Source
      (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailGLPathOperator
        Source GravityP286) point
  let contactJet :=
    generatedDiracDualFormNativePointwiseActionJet Source
      (cartanECSynchronizedGravityTailProfileContact Source
        GravityP286 point) 0
  have naturality :
      outputJet = pointwiseActionJetWithGravityTailSeam contactJet
        (gravityTailActionJetSeam outputJet contactJet) := by
    exact sourceActionGeneratedGravityTailGL_actionJet_naturality
      Source GravityP286 point
  change outputJet = contactJet ↔
    gravityTailActionJetSeam outputJet contactJet = 0
  constructor
  · intro actionJetEq
    unfold gravityTailActionJetSeam
    rw [actionJetEq]
    apply GravityTailActionJetSeam.ext <;> simp
  · intro seamZero
    rw [naturality, seamZero, pointwiseActionJetWithGravityTailSeam_zero]

/-- Whole-field gravity write faithfulness at the registered occurrence. -/
theorem StageTenPhysicalRootClosure.gravity_registeredActionField_eq_contact_iff
    (closure : StageTenPhysicalRootClosure) :
    (fun point =>
      generatedDiracDualFormNativePointwiseActionJet
        Source (closure.gravityAction.after .liveReaction) point) =
      (fun point =>
        generatedDiracDualFormNativePointwiseActionJet Source
          (cartanECSynchronizedGravityTailProfileContact Source
            (closure.gravityAction.before .cartanECSynchronized) point) 0) ↔
      (rootResidualAt GravityCurrent).gravity = 0 := by
  constructor
  · intro fieldEq
    funext point
    exact (closure.gravity_registeredActionJet_eq_contact_iff point).mp
      (congrFun fieldEq point)
  · intro residualEq
    funext point
    exact (closure.gravity_registeredActionJet_eq_contact_iff point).mpr
      (by simpa using congrFun residualEq point)

/-- The exact gravity visit supplies its live responsibility authority. -/
def StageTenPhysicalRootClosure.gravityLiveAuthority
    (_closure : StageTenPhysicalRootClosure) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot
      afterCofaceTemporalVisit (rootLedgerEntry GravityCurrent) :=
  afterCofaceCausalEntryAuthority

/-- Canonical typed answer-and-next for the complete physical responsibility
carried by the exact gravity occurrence.  The caller supplies neither a
residual value, settlement proof, target current, nor branch selector. -/
def stageTenPhysicalRootGravityAnswerAndNext :
    SourceNativeLivingCausalEntryAnswerAndNextAt livingRoot
      afterCofaceTemporalVisit (rootLedgerEntry GravityCurrent)
      stageTenPhysicalRootClosure.gravityLiveAuthority :=
  livingRoot.generatedCausalEntryAnswerAndNextAt afterCofaceTemporalVisit
    (rootLedgerEntry GravityCurrent)
    stageTenPhysicalRootClosure.gravityLiveAuthority

/-- The gravity answer payload is the exact next-row ledger readout generated
by the same living root. -/
@[simp] theorem stageTenPhysicalRootGravityAnswer_payload_eq_assembly :
    stageTenPhysicalRootGravityAnswerAndNext.answer =
      afterGravityCausalEntryAuthority.toLedgerReadout := by
  rfl

/-- The current carried by the canonical gravity answer is the registered
assembly current, not a caller-selected target. -/
@[simp] theorem stageTenPhysicalRootGravityAnswer_nextCurrent_eq_assembly :
    stageTenPhysicalRootGravityAnswerAndNext.nextCurrent.visit.current =
      AssemblyCurrent := by
  rfl

/-- Every obstruction-indexed gravity U7 return shares the unconditional
canonical answer of this exact living-root occurrence. -/
theorem stageTenPhysicalRootGravityU7Answer_eq_canonical
    (point : BasePoint)
    (nonzero :
      (rootResidualAt GravityCurrent).gravity point ≠ 0) :
    (fixedRootResidualAnswerAndNext point nonzero).answerAndNext =
      stageTenPhysicalRootGravityAnswerAndNext :=
  SourceNativeLivingCausalEntryAnswerAndNextAt.eq _ _

/-- A nonzero repaired-action residual uses the same canonical gravity
answer and therefore cannot fork a second S9-C successor. -/
theorem stageTenPhysicalRootGravityClassicalJointU7Answer_eq_canonical
    (point : BasePoint)
    (nonzero :
      (rootResidualAt GravityCurrent).classicalJoint point ≠ 0) :
    (fixedRootClassicalJointAnswerAndNextAt point nonzero).answerAndNext =
      stageTenPhysicalRootGravityAnswerAndNext :=
  SourceNativeLivingCausalEntryAnswerAndNextAt.eq _ _

/-- The source-generated first-jet obstruction returns through the same
canonical gravity answer; adding the missing coordinate cannot fork next. -/
theorem stageTenPhysicalRootGravityCoframeFirstJetU7Answer_eq_canonical
    (point : BasePoint)
    (nonzero :
      (rootResidualAt GravityCurrent).gravityCoframeFirstJet point ≠ 0) :
    (fixedRootCoframeFirstJetAnswerAndNextAt point nonzero).answerAndNext =
      stageTenPhysicalRootGravityAnswerAndNext :=
  SourceNativeLivingCausalEntryAnswerAndNextAt.eq _ _

/-- The canonical answer exposes both actual stages without conflating them:
its next current is the constitutive refresh of the GL gravity final, while
the gravity seam is the exact pre-refresh GL action-jet readout. -/
theorem
    canonicalGravityAnswerNext_refresh_and_gravityStage_factorize :
    stageTenPhysicalRootGravityAnswerAndNext.nextCurrent.visit.current.configuration =
        formNativeP286GaugeConstitutiveReadout Source
          (stageTenPhysicalRootClosure.gravityAction.after .liveReaction) ∧
      ((fun point =>
        generatedDiracDualFormNativePointwiseActionJet Source
          (stageTenPhysicalRootClosure.gravityAction.after .liveReaction)
          point) =
        (fun point =>
          generatedDiracDualFormNativePointwiseActionJet Source
            (cartanECSynchronizedGravityTailProfileContact Source
              (stageTenPhysicalRootClosure.gravityAction.before
                .cartanECSynchronized) point) 0) ↔
        (rootResidualAt GravityCurrent).gravity = 0) := by
  constructor
  · rw [stageTenPhysicalRootGravityAnswer_nextCurrent_eq_assembly]
    exact stageTenPhysicalRootClosure.gravity_target_eq.symm
  · exact
      stageTenPhysicalRootClosure.gravity_registeredActionField_eq_contact_iff

/-! ## Internal whole-spacetime assembly recognition readouts -/

@[simp] theorem StageTenPhysicalRootClosure.assembly_evolution_eq
    (_closure : StageTenPhysicalRootClosure) :
    root.evolutionAt AssemblyCurrent =
      EvolutionAt.nativeWrite (rootActionAt AssemblyCurrent) :=
  root_firstAssembly_evolution_is_wholeAssembly

@[simp] theorem StageTenPhysicalRootClosure.assembly_source_eq
    (_closure : StageTenPhysicalRootClosure) :
    (actionPathTraceAt AssemblyCurrent).head? =
      some (AssemblyCurrent.configuration,
        sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
          Source AssemblyCurrent.configuration) :=
  rfl

@[simp] theorem StageTenPhysicalRootClosure.assembly_writer_eq_target
    (closure : StageTenPhysicalRootClosure) :
    closure.wholeSpacetimeWriter = PostAssemblyCurrent.configuration := by
  rw [closure.wholeSpacetimeWriter_eq]
  rfl

@[simp] theorem StageTenPhysicalRootClosure.assembly_pathTrace_eq
    (closure : StageTenPhysicalRootClosure) :
    actionPathTraceAt AssemblyCurrent =
      [(AssemblyCurrent.configuration, closure.wholeSpacetimeWriter)] := by
  rw [closure.wholeSpacetimeWriter_eq]
  rfl

@[simp] theorem StageTenPhysicalRootClosure.assembly_next_eq
    (_closure : StageTenPhysicalRootClosure) :
    (root.evolutionAt AssemblyCurrent).nextCurrent? =
      some PostAssemblyCurrent :=
  rfl

theorem StageTenPhysicalRootClosure.assembly_wholeLedgerWriteBack_eq
    (closure : StageTenPhysicalRootClosure) :
    HEq closure.assemblyEvent.wholeLedgerWriteBack
      (rootLedgerCompiler.compile (rootEmitted AssemblyCurrent)) := by
  rw [closure.assemblyEvent_eq]
  exact HEq.rfl

/-- The whole-spacetime writer's exact action jet is the registered
post-assembly current obtained by writing back the complete assembly residual
carried by the source occurrence. -/
theorem StageTenPhysicalRootClosure.assembly_writer_actionJet_eq_residualWriteBack
    (closure : StageTenPhysicalRootClosure)
    (point : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet
        Source closure.wholeSpacetimeWriter point =
      pointwiseActionJetWithCompleteJointAssemblySeam
        (contactActionJet Source AssemblyCurrent.configuration point)
        ((rootResidualAt AssemblyCurrent).assembly point) := by
  rw [closure.assembly_writer_eq_target]
  exact root_firstPostAssembly_actionJet_eq_residualWriteBack point

/-- The registered post-assembly action jet is unchanged exactly when the
source occurrence's complete assembly residual is zero.  This is the exact
zero/effect disposition of the fixed root write. -/
theorem StageTenPhysicalRootClosure.assembly_registeredActionJet_eq_contact_iff
    (closure : StageTenPhysicalRootClosure)
    (point : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet
        Source PostAssemblyCurrent.configuration point =
        contactActionJet Source AssemblyCurrent.configuration point ↔
      (rootResidualAt AssemblyCurrent).assembly point = 0 := by
  calc
    generatedDiracDualFormNativePointwiseActionJet
          Source PostAssemblyCurrent.configuration point =
        contactActionJet Source AssemblyCurrent.configuration point ↔
      generatedDiracDualFormNativePointwiseActionJet
          Source closure.wholeSpacetimeWriter point =
        contactActionJet Source AssemblyCurrent.configuration point := by
          rw [closure.assembly_writer_eq_target]
    _ ↔ pointwiseActionJetWithCompleteJointAssemblySeam
          (contactActionJet Source AssemblyCurrent.configuration point)
          ((rootResidualAt AssemblyCurrent).assembly point) =
        contactActionJet Source AssemblyCurrent.configuration point := by
          rw [closure.assembly_writer_actionJet_eq_residualWriteBack]
    _ ↔ (rootResidualAt AssemblyCurrent).assembly point = 0 :=
      pointwiseActionJetWithCompleteJointAssemblySeam_eq_contact_iff
        (contactActionJet Source AssemblyCurrent.configuration point)
        ((rootResidualAt AssemblyCurrent).assembly point)

/-- At one exact post-YM assembly occurrence, write-back leaves the registered
action jet unchanged exactly when its four actual open coordinates vanish. -/
theorem
    StageTenPhysicalRootClosure.assembly_registeredActionJet_eq_contact_iff_openCoordinates
    (closure : StageTenPhysicalRootClosure)
    (point : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet
        Source PostAssemblyCurrent.configuration point =
        contactActionJet Source AssemblyCurrent.configuration point ↔
      ((rootResidualAt AssemblyCurrent).assembly point).gravityCurvature = 0 ∧
      ((rootResidualAt AssemblyCurrent).assembly point
        ).gravityAuxiliaryExteriorCovariantDerivative = 0 ∧
      ((rootResidualAt AssemblyCurrent).assembly point
        ).scalarDifferentialMomentumDivergence = 0 ∧
      ((rootResidualAt AssemblyCurrent).assembly point
        ).matterDifferentialMomentumDivergence = 0 := by
  rw [closure.assembly_registeredActionJet_eq_contact_iff]
  exact root_firstAssembly_residual_eq_zero_iff_openCoordinates_eq_zero point

/-- At the activation origin the post-YM writer retains the same actual
four-coordinate normal form; no pre-YM identity-jet calibration is replayed.
-/
theorem
    StageTenPhysicalRootClosure.assembly_registeredActionJet_origin_eq_contact_iff_openCoordinates
    (closure : StageTenPhysicalRootClosure) :
    generatedDiracDualFormNativePointwiseActionJet
        Source PostAssemblyCurrent.configuration 0 =
        contactActionJet Source AssemblyCurrent.configuration 0 ↔
      ((rootResidualAt AssemblyCurrent).assembly 0).gravityCurvature = 0 ∧
      ((rootResidualAt AssemblyCurrent).assembly 0
        ).gravityAuxiliaryExteriorCovariantDerivative = 0 ∧
      ((rootResidualAt AssemblyCurrent).assembly 0
        ).scalarDifferentialMomentumDivergence = 0 ∧
      ((rootResidualAt AssemblyCurrent).assembly 0
        ).matterDifferentialMomentumDivergence = 0 := by
  rw [closure.assembly_registeredActionJet_eq_contact_iff]
  exact
    root_firstAssembly_origin_residual_eq_zero_iff_openCoordinates_eq_zero

/-- The complete registered action field is unchanged exactly when the whole
assembly residual field vanishes. -/
theorem StageTenPhysicalRootClosure.assembly_registeredActionField_eq_contact_iff
    (closure : StageTenPhysicalRootClosure) :
    (fun point =>
      generatedDiracDualFormNativePointwiseActionJet
        Source PostAssemblyCurrent.configuration point) =
        (fun point =>
          contactActionJet Source AssemblyCurrent.configuration point) ↔
      (rootResidualAt AssemblyCurrent).assembly = 0 := by
  constructor
  · intro fieldEq
    funext point
    exact (closure.assembly_registeredActionJet_eq_contact_iff point).mp
      (congrFun fieldEq point)
  · intro residualEq
    funext point
    apply (closure.assembly_registeredActionJet_eq_contact_iff point).mpr
    simpa using congrFun residualEq point

/-- Whole-field faithfulness exposes the same four actual coordinates at every
point of the exact post-YM assembly occurrence. -/
theorem
    StageTenPhysicalRootClosure.assembly_registeredActionField_eq_contact_iff_openCoordinates
    (closure : StageTenPhysicalRootClosure) :
    (fun point =>
      generatedDiracDualFormNativePointwiseActionJet
        Source PostAssemblyCurrent.configuration point) =
        (fun point =>
          contactActionJet Source AssemblyCurrent.configuration point) ↔
      ∀ point,
        ((rootResidualAt AssemblyCurrent).assembly point).gravityCurvature = 0 ∧
        ((rootResidualAt AssemblyCurrent).assembly point
          ).gravityAuxiliaryExteriorCovariantDerivative = 0 ∧
        ((rootResidualAt AssemblyCurrent).assembly point
          ).scalarDifferentialMomentumDivergence = 0 ∧
        ((rootResidualAt AssemblyCurrent).assembly point
          ).matterDifferentialMomentumDivergence = 0 := by
  constructor
  · intro fieldEq point
    exact
      (closure.assembly_registeredActionJet_eq_contact_iff_openCoordinates
        point).mp (congrFun fieldEq point)
  · intro equations
    funext point
    exact
      (closure.assembly_registeredActionJet_eq_contact_iff_openCoordinates
        point).mpr (equations point)

/-- Faithfulness of the complete write-back makes every nonzero assembly
residual observable as an actual change of the registered target action jet. -/
theorem
    StageTenPhysicalRootClosure.assemblyResidual_nonzero_changes_registeredActionJet
    (closure : StageTenPhysicalRootClosure)
    (point : BasePoint)
    (nonzero : (rootResidualAt AssemblyCurrent).assembly point ≠ 0) :
    generatedDiracDualFormNativePointwiseActionJet
        Source PostAssemblyCurrent.configuration point ≠
      contactActionJet Source AssemblyCurrent.configuration point := by
  intro unchanged
  exact nonzero
    ((closure.assembly_registeredActionJet_eq_contact_iff point).mp unchanged)

/-- A nonzero whole-spacetime assembly residual generates the U7 demand on
this exact occurrence's ledger row, and the same compiler writes it into the
registered post-assembly current. -/
theorem
    StageTenPhysicalRootClosure.assemblyResidual_generates_registeredAnswerAndNext
    (closure : StageTenPhysicalRootClosure)
    (point : BasePoint)
    (nonzero : (rootResidualAt AssemblyCurrent).assembly point ≠ 0) :
    (fixedRootAssemblyDemandAt point nonzero).entry =
        rootOccurrenceLedgerEntry closure.assemblyEvent.occurrence ∧
      Nonempty
        (SourceNativeRootResidualAnswerAndNextAt afterGravityTemporalVisit
          (fixedRootAssemblyObstructionAt point nonzero)
          afterGravityCausalEntryAuthority) ∧
      (root.evolutionAt AssemblyCurrent).nextCurrent? =
        some PostAssemblyCurrent ∧
      generatedDiracDualFormNativePointwiseActionJet
          Source PostAssemblyCurrent.configuration point =
        pointwiseActionJetWithCompleteJointAssemblySeam
          (contactActionJet Source AssemblyCurrent.configuration point)
          ((rootResidualAt AssemblyCurrent).assembly point) ∧
      generatedDiracDualFormNativePointwiseActionJet
          Source PostAssemblyCurrent.configuration point ≠
        contactActionJet Source AssemblyCurrent.configuration point := by
  refine ⟨?_, ⟨fixedRootAssemblyAnswerAndNextAt point nonzero⟩, ?_, ?_, ?_⟩
  · rw [closure.assemblyEvent_eq]
    rfl
  · exact closure.assembly_next_eq
  · rw [← closure.assembly_writer_eq_target]
    exact closure.assembly_writer_actionJet_eq_residualWriteBack point
  · exact closure.assemblyResidual_nonzero_changes_registeredActionJet
      point nonzero

@[simp] theorem StageTenPhysicalRootClosure.assembly_sourceEntry_eq
    (closure : StageTenPhysicalRootClosure) :
    rootOccurrenceLedgerEntry closure.assemblyEvent.occurrence =
      rootLedgerEntry AssemblyCurrent := by
  rw [closure.assemblyEvent_eq]
  rfl

/-- Installed dependent face of the exact assembly occurrence: the final
post-gravity constitutive material edge settles the P286 auxiliary coordinate
of the occurrence's whole-ledger classical row at every spacetime point. -/
theorem
    StageTenPhysicalRootClosure.assembly_p286GaugeAuxiliaryResidualSection_eq_zero
    (closure : StageTenPhysicalRootClosure) :
    (fun point =>
      ((rootOccurrenceLedgerEntry closure.assemblyEvent.occurrence
        ).1.classicalJoint point).p286GaugeAuxiliary) = 0 := by
  rw [closure.assembly_sourceEntry_eq]
  exact root_firstAssembly_p286GaugeAuxiliaryResidualSection_eq_zero

/-- The same exact assembly occurrence settles both algebraic gravity rows
and the refreshed P286 auxiliary row.  All three coordinates are read from
the occurrence's whole-ledger entry; none is supplied to the closure. -/
theorem
    StageTenPhysicalRootClosure.assembly_algebraicThreeCoordinateSections_eq_zero
    (closure : StageTenPhysicalRootClosure) :
    (fun point =>
      ((rootOccurrenceLedgerEntry closure.assemblyEvent.occurrence
        ).1.classicalJoint point).gravityMultiplier) = 0 ∧
    (fun point =>
      ((rootOccurrenceLedgerEntry closure.assemblyEvent.occurrence
        ).1.classicalJoint point).gravityAuxiliary) = 0 ∧
    (fun point =>
      ((rootOccurrenceLedgerEntry closure.assemblyEvent.occurrence
        ).1.classicalJoint point).p286GaugeAuxiliary) = 0 := by
  rw [closure.assembly_sourceEntry_eq]
  exact root_firstAssembly_algebraicThreeCoordinateSections_eq_zero

theorem StageTenPhysicalRootClosure.assembly_configuration_smooth
    (_closure : StageTenPhysicalRootClosure) :
    AssemblyCurrent.configuration.Smooth :=
  root_firstAssembly_smooth

theorem StageTenPhysicalRootClosure.assembly_configuration_nondegenerate
    (_closure : StageTenPhysicalRootClosure) :
    AssemblyCurrent.configuration.Nondegenerate :=
  root_firstAssembly_nondegenerate

/-- The exact assembly occurrence installs the complete generated
qualification of its refreshed material state.  Smoothness, nondegeneracy and
the exact three-coordinate algebraic settlement are consequences of the one
sealed trace, not fields submitted to the closure. -/
theorem StageTenPhysicalRootClosure.assembly_materialQualification_factorizes
    (closure : StageTenPhysicalRootClosure) :
    closure.authorityOutcomeAt .assembly .configuration =
        .inl ⟨PUnit.unit, AssemblyCurrent.configuration⟩ ∧
      AssemblyCurrent.configuration.Smooth ∧
      AssemblyCurrent.configuration.Nondegenerate ∧
      (fun point =>
        ((rootOccurrenceLedgerEntry closure.assemblyEvent.occurrence
          ).1.classicalJoint point).gravityMultiplier) = 0 ∧
      (fun point =>
        ((rootOccurrenceLedgerEntry closure.assemblyEvent.occurrence
          ).1.classicalJoint point).gravityAuxiliary) = 0 ∧
      (fun point =>
        ((rootOccurrenceLedgerEntry closure.assemblyEvent.occurrence
          ).1.classicalJoint point).p286GaugeAuxiliary) = 0 := by
  exact ⟨closure.configurationOutcome_eq .assembly,
    closure.assembly_configuration_smooth,
    closure.assembly_configuration_nondegenerate,
    closure.assembly_algebraicThreeCoordinateSections_eq_zero⟩

@[simp] theorem StageTenPhysicalRootClosure.assembly_targetEntry_eq
    (_closure : StageTenPhysicalRootClosure) :
    rootOccurrenceLedgerEntry (rootEmitted PostAssemblyCurrent) =
      rootLedgerEntry PostAssemblyCurrent :=
  rfl

/-- The assembly occurrence carries the existing live ledger into its
source-native next current. -/
def StageTenPhysicalRootClosure.assemblyLiveAuthority
    (_closure : StageTenPhysicalRootClosure) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot
      afterGravityTemporalVisit (rootLedgerEntry AssemblyCurrent) :=
  afterGravityCausalEntryAuthority

/-! ## Registered post-assembly continuation -/

@[simp] theorem StageTenPhysicalRootClosure.postAssembly_sourceEntry_eq
    (closure : StageTenPhysicalRootClosure) :
    rootOccurrenceLedgerEntry closure.postAssemblyEvent.occurrence =
      rootLedgerEntry PostAssemblyCurrent := by
  rw [closure.postAssemblyEvent_eq]
  rfl

theorem StageTenPhysicalRootClosure.postAssembly_wholeLedgerWriteBack_eq
    (closure : StageTenPhysicalRootClosure) :
    HEq closure.postAssemblyEvent.wholeLedgerWriteBack
      (rootLedgerCompiler.compile (rootEmitted PostAssemblyCurrent)) := by
  rw [closure.postAssemblyEvent_eq]
  exact HEq.rfl

/-- The target of the assembly write remains in the same live responsibility
history. -/
def StageTenPhysicalRootClosure.postAssemblyLiveAuthority
    (_closure : StageTenPhysicalRootClosure) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt livingRoot
      afterAssemblyTemporalVisit (rootLedgerEntry PostAssemblyCurrent) :=
  afterAssemblyCausalEntryAuthority

/-- Canonical typed answer-and-next for the complete physical responsibility
carried by the fixed assembly occurrence.  Its source entry is the actual
assembly ledger row; no residual value, settlement proof, target current, or
branch selector is supplied by the caller. -/
def stageTenPhysicalRootAssemblyAnswerAndNext :
    SourceNativeLivingCausalEntryAnswerAndNextAt livingRoot
      afterGravityTemporalVisit (rootLedgerEntry AssemblyCurrent)
      stageTenPhysicalRootClosure.assemblyLiveAuthority :=
  livingRoot.generatedCausalEntryAnswerAndNextAt afterGravityTemporalVisit
    (rootLedgerEntry AssemblyCurrent)
    stageTenPhysicalRootClosure.assemblyLiveAuthority

/-- The typed answer payload is the exact post-assembly ledger readout
generated by the same living root. -/
@[simp] theorem stageTenPhysicalRootAssemblyAnswer_payload_eq_postAssembly :
    stageTenPhysicalRootAssemblyAnswerAndNext.answer =
      stageTenPhysicalRootClosure.postAssemblyLiveAuthority.toLedgerReadout := by
  rfl

/-- The current carried by the canonical answer-and-next is the registered
post-assembly physical current, not a caller-supplied target. -/
@[simp] theorem stageTenPhysicalRootAssemblyAnswer_nextCurrent_eq_postAssembly :
    stageTenPhysicalRootAssemblyAnswerAndNext.nextCurrent.visit.current =
      PostAssemblyCurrent := by
  rfl

/-- The obstruction-indexed U7 branch and the unconditional typed assembly
answer share the unique canonical living-root answer. -/
theorem stageTenPhysicalRootAssemblyU7Answer_eq_canonical
    (point : BasePoint)
    (nonzero : (rootResidualAt AssemblyCurrent).assembly point ≠ 0) :
    (fixedRootAssemblyAnswerAndNextAt point nonzero).answerAndNext =
      stageTenPhysicalRootAssemblyAnswerAndNext :=
  SourceNativeLivingCausalEntryAnswerAndNextAt.eq _ _

/-- Canonical typed answer-and-next for the exact post-assembly gravity row.
The fifth registered occurrence, its answer, and its generated successor all
remain in the same living-root history. -/
def stageTenPhysicalRootPostAssemblyAnswerAndNext :
    SourceNativeLivingCausalEntryAnswerAndNextAt livingRoot
      afterAssemblyTemporalVisit (rootLedgerEntry PostAssemblyCurrent)
      stageTenPhysicalRootClosure.postAssemblyLiveAuthority :=
  livingRoot.generatedCausalEntryAnswerAndNextAt afterAssemblyTemporalVisit
    (rootLedgerEntry PostAssemblyCurrent)
    stageTenPhysicalRootClosure.postAssemblyLiveAuthority

@[simp] theorem stageTenPhysicalRootPostAssemblyAnswer_nextCurrent_eq :
    stageTenPhysicalRootPostAssemblyAnswerAndNext.nextCurrent.visit.current =
      Next PostAssemblyCurrent := by
  rfl

/-- Every obstruction-indexed U7 answer on the fifth row is the same
unconditional canonical answer generated for that row. -/
theorem stageTenPhysicalRootPostAssemblyU7Answer_eq_canonical
    (point : BasePoint)
    (nonzero :
      (rootResidualAt PostAssemblyCurrent).gravity point ≠ 0) :
    (fixedRootPostAssemblyGravityAnswerAndNextAt point nonzero).answerAndNext =
      stageTenPhysicalRootPostAssemblyAnswerAndNext :=
  SourceNativeLivingCausalEntryAnswerAndNextAt.eq _ _

/-- Reverse faithfulness: the whole-spacetime writer recovered from the root
closure is definitionally the Stage-Nine source-generated global operator. -/
theorem StageTenPhysicalRootClosure.recovers_wholeSpacetimeWriter
    (closure : StageTenPhysicalRootClosure) :
    closure.wholeSpacetimeWriter =
      sourceActionGeneratedCartanECConstraintCauchyFullOccurrenceGlobalOperator
        Source AssemblyCurrent.configuration :=
  closure.wholeSpacetimeWriter_eq

end
end StageTenPhysicalRoot
end SaturationMonoid.PhysicsCore
