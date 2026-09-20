import H0mework.Foundation.Runtime.Activation
import H0mework.Foundation.Arithmetic.UnfoldingFace
import H0mework.Realization.Operations.BinaryInputs

/-!
# Canonical unit arithmetic living root

One source-owned unit history is the current of this arithmetic root.  Its
unique native event appends one actual unit occurrence.  The same emitted
occurrence owns the arithmetic material face, sibling/dependent restriction
faces, whole-ledger write-back, and generated next current.

This file contains no prime, zeta, Goldbach, or Riemann object.  Those are
downstream restrictions of this fixed source and law epoch.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticRoot

open ArithmeticGeneration
open RootArithmeticIncidence
open RootArithmeticUnfoldingFace

/-- The source begins with one actual unit occurrence, not a numeric index. -/
def unitHistory : UnitHistory := .next .empty

abbrev Current := UnitHistory

/-- The only native update appends one sibling unit occurrence. -/
def next (current : Current) : Current :=
  current.parallel unitHistory

@[simp] theorem next_eq_next (current : Current) :
    next current = .next current :=
  rfl

def initialCurrent : Current := unitHistory

abbrev WriteBack := UnitHistory

abbrev NativeOperationProof (current target : Current) : Type :=
  SourceOperationDerivations.Derivation
    (SourceNativeBinary.environment (X := Current) (Y := Current) (Z := Current))
    (SourceNativeBinary.expression UnitHistory.parallel current unitHistory)
    (.const (Finsupp.single target 1))

noncomputable def nativeOperationProof (current : Current) :
    NativeOperationProof current (next current) :=
  SourceNativeBinary.normalization UnitHistory.parallel current unitHistory

/-- Eliminate the generated operation receipt while the native target continues
to be computed by the original unit-history recursion. -/
theorem nativeOperation_target {current target : Current}
    (proof : NativeOperationProof current target) : target = next current := by
  have same : Finsupp.single (next current) (1 : ℤ) = Finsupp.single target 1 :=
    (SourceNativeBinary.expression_eval UnitHistory.parallel current unitHistory).symm.trans proof.sound
  exact (Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0) same).symm

/-- One exact source write.  Its target and write-back are calculated from
the current unit history. -/
structure NativeWriteAt (current : Current) where
  private mk ::
  target : Current
  target_eq : target = next current
  target_ne_source : target ≠ current
  wholeWriteBack : WriteBack
  wholeWriteBack_eq : wholeWriteBack = current

def nativeWriteAt (current : Current) : NativeWriteAt current where
  target := next current
  target_eq := nativeOperation_target (nativeOperationProof current)
  target_ne_source := by
    intro equality
    have shadowEquality := congrArg UnitHistory.cardinalShadow equality
    change Nat.succ current.cardinalShadow = current.cardinalShadow at shadowEquality
    exact Nat.succ_ne_self current.cardinalShadow shadowEquality
  wholeWriteBack := current
  wholeWriteBack_eq := rfl

@[simp] theorem nativeWriteAt_target (current : Current) :
    (nativeWriteAt current).target = next current :=
  rfl

@[simp] theorem nativeWriteAt_wholeWriteBack (current : Current) :
    (nativeWriteAt current).wholeWriteBack = current :=
  rfl

/-- The unique open arithmetic responsibility is transferred by the native
unit write. -/
inductive RootDispositionAt (support : Current) :
    WorldDispositionKind → Type
  | transfer (write : NativeWriteAt support) :
      RootDispositionAt support .transfer

def rootResponsibilityAt (support : Current) : WriteBack := support

structure RootOpenAt
    (support : Current) (responsibility : WriteBack) : Type where
  responsibility_eq : responsibility = rootResponsibilityAt support

def network : WorldRelationNetwork where
  Support := Current
  Anchor := PUnit
  Incidence := Current
  Lineage := PUnit
  Responsibility := WriteBack
  Claim := PUnit
  anchorAt := fun _ => PUnit.unit
  incidenceAt := id
  lineageAt := fun _ => PUnit.unit
  OpenAt := RootOpenAt
  openClaimAt := fun _ => PUnit.unit
  HoldsAt := fun _ claim => PLift (claim = PUnit.unit)
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := PEmpty.elim
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := RootDispositionAt

abbrev N := network

/-- The v0 arithmetic root has an empty obstruction surface.  This is a
representation-audit fact, not evidence that no real representation failure
exists: if the coordinate-free common carrier later exceeds this law surface,
the single authorized U8 must revise this root rather than cite `PEmpty` as a
global no-go. -/
theorem rootObstructionAt_isEmpty (current : Current) :
    IsEmpty (N.ObstructionAt current) :=
  ⟨fun obstruction => nomatch obstruction⟩

def rootLedgerEntry (current : Current) : OpenResponsibilityAt N current :=
  ⟨rootResponsibilityAt current, ⟨rfl⟩⟩

theorem rootLedgerEntry_unique
    (current : Current) (entry : OpenResponsibilityAt N current) :
    entry = rootLedgerEntry current := by
  rcases entry with ⟨responsibility, openAt⟩
  rcases openAt with ⟨responsibility_eq⟩
  cases responsibility_eq
  rfl

def rootLedgerInventoryPresentation (current : Current) :
    ConstructivePresentation PUnit (OpenResponsibilityAt N current) where
  forward := fun _ => rootLedgerEntry current
  backward := fun _ => PUnit.unit
  backward_forward := fun _ => rfl
  forward_backward := fun entry => (rootLedgerEntry_unique current entry).symm

def vocabulary : Vocabulary where
  Current := Current
  Anchor := PUnit
  Incidence := Current
  Lineage := PUnit
  anchorAt := fun _ => PUnit.unit
  incidenceAt := id
  lineageAt := fun _ => PUnit.unit
  NativeWriteAt := NativeWriteAt
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := NativeWriteAt.target
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev V := vocabulary

structure RootNativeEventAt (current support : Current) : Type where
  support_eq : support = current

def eventAlgebra : SourceNativeEventAlgebra N V where
  EventAt := RootNativeEventAt
  compile := fun {current} {_support} _event =>
    .nativeWrite (nativeWriteAt current)
  AffectedInventoryAt := fun _ => PUnit
  affectedInventoryPresentation := by
    intro current support event
    cases event.support_eq
    exact rootLedgerInventoryPresentation current
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by
    intro _ _ event
    cases event.support_eq
    rfl
  incidence_commutes := by
    intro _ _ event
    cases event.support_eq
    rfl
  lineage_commutes := by
    intro _ _ event
    cases event.support_eq
    rfl

def source : SourceNativeSource N V where
  initial := initialCurrent
  law := eventAlgebra

def emitted (current : Current) :
    source.toRootSource.actual.OccurrenceAt current :=
  ⟨current, ⟨rfl⟩⟩

structure RootLedgerExactTransitionAt
    (current targetSupport : Current) : Type where
  targetSupport_eq : targetSupport = next current

def ledgerWriteRowSource :
    LedgerWriteRowSourceAt source (by
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
    cases rootLedgerEntry_unique (next current) targetEntry
    exact .transferred (.transfer (nativeWriteAt current))
      rfl rfl (Nat.le_refl _)
  compileExact := fun event => event

def ledgerTerminalRowSource : LedgerTerminalRowSourceAt source :=
  LedgerTerminalRowSourceAt.empty _

def occurrenceLedgerEntry
    {current : Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt N occurrence.1 :=
  source.law.affectedInventoryPresentation occurrence.2 |>.forward PUnit.unit

def generatedRowsAtOccurrence
    {current : Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt ledgerWriteRowSource occurrence
      (⟨next current⟩ : CompleteLiveLedgerAt N) where
  size := 1
  sourceEntryAt := fun _ => occurrenceLedgerEntry occurrence
  targetEntryAt := fun _ => rootLedgerEntry (next current)
  rowAt := fun _ => ledgerWriteRowSource.generate ⟨rfl⟩

def generatedCoverageAtOccurrence
    {current : Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (generatedRowsAtOccurrence occurrence) where
  destinationIndex := fun _ =>
    ⟨0, by simp [generatedRowsAtOccurrence]⟩
  originIndex := fun _ =>
    ⟨0, by simp [generatedRowsAtOccurrence]⟩
  destination_sound := fun entry => by
    change occurrenceLedgerEntry occurrence = entry
    exact (source.law.affectedInventoryPresentation occurrence.2).forward_backward entry
  origin_sound := fun entry =>
    (rootLedgerEntry_unique (next current) entry).symm

def generatedPatchAtOccurrence
    {current : Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt ledgerWriteRowSource occurrence
      (⟨next current⟩ : CompleteLiveLedgerAt N) :=
  .complete (generatedRowsAtOccurrence occurrence)
    (generatedCoverageAtOccurrence occurrence)

def generatedLedgerEvolution
    {current : Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt source occurrence := by
  rcases occurrence with ⟨support, event⟩
  change RootNativeEventAt current support at event
  cases event.support_eq
  exact .nativeWrite (nativeWriteAt current) rfl
    (emitted (next current))
    ((generatedPatchAtOccurrence ⟨current, event⟩).toLedgerWriteEvolution)

def ledgerCompiler : SourceNativeLedgerCompiler source where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := by
    intro current _occurrence targetSupport _sourceEntry _targetEntry
    exact RootLedgerExactTransitionAt current targetSupport
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := ledgerWriteRowSource
  terminalRowSource := ledgerTerminalRowSource
  compile := generatedLedgerEvolution
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    change RootNativeEventAt current support at event
    cases event.support_eq
    exact ⟨generatedPatchAtOccurrence ⟨current, event⟩, rfl⟩

def ledgerSource : SourceNativeLedgerSource N V where
  source := source
  ledgerCompiler := ledgerCompiler

def ledgerRoot : SourceNativeLedgerRootClosure N V where
  source := ledgerSource
  emitted := emitted
  compiler_commutes := by
    intro current
    rfl

abbrev root : RootClosure N V := ledgerRoot.toRoot

theorem rootEntry_subsingleton (support : N.Support) :
    Subsingleton (OpenResponsibilityAt N support) :=
  ⟨fun left right =>
    (rootLedgerEntry_unique support left).trans
      (rootLedgerEntry_unique support right).symm⟩

private def restructuringLaw : SourceNativeLedgerRestructuringLaw source :=
  identityOnlyWorldLedgerRestructuringLaw source PUnit.unit <| by
    intro support responsibility
    constructor
    intro left right
    rcases left with ⟨leftProof⟩
    rcases right with ⟨rightProof⟩
    have proof_eq : leftProof = rightProof := Subsingleton.elim _ _
    cases proof_eq
    rfl

def restructuringCertification
    {current : V.Current} (occurrence : source.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt restructuringLaw
      (ledgerCompiler.compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  change RootNativeEventAt current support at event
  cases event.support_eq
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (rootEntry_subsingleton _).elim left right)
    (fun left right _ => (rootEntry_subsingleton _).elim left right)

private def restructuringCompiler : SourceNativeRestructuringLedgerCompiler source where
  ledgerCompiler := ledgerCompiler
  restructuringLaw := restructuringLaw
  certifyRestructuring := restructuringCertification

private def restructuringSource : SourceNativeRestructuringLedgerSource N V where
  source := source
  compiler := restructuringCompiler

/-- Raw sibling and dependent arithmetic restrictions installed before the
root emitter. -/
inductive RestrictionKind
  | sibling
  | dependent
  deriving DecidableEq

def materialLaw : SourceNativeRootArithmeticMaterialLaw ledgerSource :=
  .create fun {current} _occurrence =>
    { whole := next current
      left := current
      right := unitHistory }

private def restrictionLaw : SourceNativeProjectionLaw ledgerSource where
  Projection := RestrictionKind
  ActiveAt := fun _ {_current} _occurrence => PUnit
  InactiveAt := fun _ {_current} _occurrence => PEmpty
  classify := fun _ {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _ {_current} _occurrence _active => UnitHistory
  project := fun restriction {current} _occurrence _active =>
    match restriction with
    | .sibling => current.parallel unitHistory
    | .dependent => current.joint unitHistory

private def projectionLaw : SourceNativeProjectionLaw ledgerSource where
  Projection := Sum materialLaw.toProjectionLaw.Projection restrictionLaw.Projection
  ActiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl material => materialLaw.toProjectionLaw.ActiveAt material occurrence
    | .inr restriction => restrictionLaw.ActiveAt restriction occurrence
  InactiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl material => materialLaw.toProjectionLaw.InactiveAt material occurrence
    | .inr restriction => restrictionLaw.InactiveAt restriction occurrence
  classify := fun projection {_current} occurrence =>
    match projection with
    | .inl material => materialLaw.toProjectionLaw.classify material occurrence
    | .inr restriction => restrictionLaw.classify restriction occurrence
  PayloadAt := fun projection {_current} occurrence active =>
    match projection with
    | .inl material => materialLaw.toProjectionLaw.PayloadAt material occurrence active
    | .inr restriction => restrictionLaw.PayloadAt restriction occurrence active
  project := fun projection {_current} occurrence active =>
    match projection with
    | .inl material => materialLaw.toProjectionLaw.project material occurrence active
    | .inr restriction => restrictionLaw.project restriction occurrence active

def materialInstallation : SourceNativeProjectionLaw.InstallationAt
    materialLaw.toProjectionLaw projectionLaw where
  embed := Sum.inl
  embed_injective := by
    intro left right equality
    cases equality
    rfl
  outcome_heq := by intros; rfl

def restrictionInstallation : SourceNativeProjectionLaw.InstallationAt
    restrictionLaw projectionLaw where
  embed := Sum.inr
  embed_injective := by
    intro left right equality
    cases equality
    rfl
  outcome_heq := by intros; rfl

private def authoritySource : SourceNativeAuthoritySource N V where
  restructuringSource := restructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal restructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic N
  projectionLaw := projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure N V where
  source := authoritySource
  emitted := emitted
  compiler_commutes := by
    intro current
    rfl

def livingRoot : SourceNativeLivingRootClosure N V :=
  authoritativeRoot.toLivingWithoutFaithfulTerminal <| fun _ =>
    ⟨fun terminal => nomatch terminal⟩

def recognition : SourceNativeRootArithmeticIncidenceRecognitionAt livingRoot where
  materialLaw := materialLaw
  installation := materialInstallation

def initialVisit : SourceNativeTemporalVisitAt ledgerRoot :=
  .finite root.initialVisit

def initialStep : RootArithmeticIncidenceStepAt recognition initialVisit :=
  recognition.generateStepAt initialVisit

@[simp] theorem initialStep_material_whole :
    initialStep.material.whole = next initialCurrent :=
  rfl

@[simp] theorem initialStep_material_left :
    initialStep.material.left = initialCurrent :=
  rfl

@[simp] theorem initialStep_material_right :
    initialStep.material.right = unitHistory :=
  rfl

theorem initial_parallel_fold_is_actual :
    initialStep.material.whole = parallelFold initialStep := by
  rfl

/-- The first domain point is structurally indexed by the compiler-owned
occurrence. -/
def initialDomainPoint : RootArithmeticDomainPointAt initialStep PUnit :=
  RootArithmeticDomainPointAt.generate initialStep PUnit.unit

def initialDomainOccurrence :
    RootedAccountedUnfolding (RootArithmeticDomainPointAt initialStep PUnit) :=
  RootedAccountedUnfolding.zero initialDomainPoint

def initialDomainAdmission : RootArithmeticUnfoldingAdmissionAt initialStep
    initialDomainOccurrence [PUnit.unit] rfl :=
  RootArithmeticUnfoldingAdmissionAt.generate

theorem initialDomain_reuses_whole_ledger_and_next :
    HEq initialDomainAdmission.wholeLedgerWriteBack
        initialStep.wholeLedgerWriteBack ∧
      initialDomainAdmission.nextCurrent =
        livingRoot.generatedNextCurrentAt initialVisit :=
  ⟨HEq.rfl, rfl⟩

/-! ## Canonical runtime and named raw arithmetic facade -/

def finiteVisit : Nat → RootVisit root
  | 0 => root.initialVisit
  | depth + 1 => (finiteVisit depth).next rfl

def temporalVisit (depth : Nat) : SourceNativeTemporalVisitAt ledgerRoot :=
  .finite (finiteVisit depth)

def temporalDepth?
    (current : SourceNativeLivingRootCurrentAt N) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

theorem temporalVisit_depth (depth : Nat) :
    temporalDepth? ⟨V, livingRoot, temporalVisit depth⟩ = some depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change
        some (ProductiveFiniteRootHistoryAt.causalDepth
          (finiteVisit depth).history + 1) = some (depth + 1)
      have priorDepth :
          ProductiveFiniteRootHistoryAt.causalDepth
              (finiteVisit depth).history = depth := by
        change some (ProductiveFiniteRootHistoryAt.causalDepth
          (finiteVisit depth).history) = some depth at inductionHypothesis
        exact Option.some.inj inductionHypothesis
      rw [priorDepth]

def process : SourceNativeLivingRootProcess N where
  State := Nat
  stateAt := fun depth => ⟨V, livingRoot, temporalVisit depth⟩
  stateAt_injective := by
    intro left right equality
    have depthEquality := congrArg temporalDepth? equality
    rw [temporalVisit_depth left, temporalVisit_depth right] at depthEquality
    exact Option.some.inj depthEquality
  initial := 0
  successorAt := fun depth => ⟨depth + 1, rfl, by rfl⟩

inductive FacadeFace
  | material
  | additiveRestriction
  | multiplicativeRestriction
  deriving DecidableEq

def runtimeFacade : SourceNativeLivingRuntimeFacade N where
  process := process
  FaceAt := fun _runtime => FacadeFace
  componentAt := fun _runtime face =>
    match face with
    | .material => materialLaw.toProjectionLaw
    | .additiveRestriction => restrictionLaw
    | .multiplicativeRestriction => restrictionLaw
  installationAt := fun _runtime face =>
    match face with
    | .material => materialInstallation
    | .additiveRestriction => restrictionInstallation
    | .multiplicativeRestriction => restrictionInstallation
  projectionAt := fun _runtime face =>
    match face with
    | .material => PUnit.unit
    | .additiveRestriction => .sibling
    | .multiplicativeRestriction => .dependent

def runtimeSeed : LivingRuntimeState runtimeFacade.process :=
  runtimeFacade.seed

theorem coversAt_factorizes
    (runtime : LivingRuntimeState runtimeFacade.process)
    (face : runtimeFacade.FaceAt runtime) :
    runtimeFacade.process.toAnswerNextCausalWorld.emitted
          (ULift.up runtime.state) = ULift.up runtime.tick.generated ∧
      runtime.tick.generated.occurrence =
        runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          runtime.current.visit.current ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          runtime.current.visit.current) ∧
      HEq (runtimeFacade.readoutAt runtime face)
        (runtime.tick.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime face).embed
            (runtimeFacade.projectionAt runtime face))) ∧
      runtime.tick.nextCurrent =
        runtimeFacade.process.stateAt
          (runtimeFacade.process.successor runtime.state) :=
  runtimeFacade.readoutAt_factorizes runtime face

theorem seed_material_additive_multiplicative_share_occurrence :
    runtimeSeed.emittedOccurrence = initialStep.generated.occurrence ∧
      runtimeSeed.tick.generated.occurrence =
        runtimeSeed.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          runtimeSeed.current.visit.current ∧
      runtimeSeed.tick.generated.occurrence =
        runtimeSeed.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          runtimeSeed.current.visit.current ∧
      runtimeSeed.tick.generated.occurrence =
        runtimeSeed.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          runtimeSeed.current.visit.current := by
  exact ⟨rfl,
    (coversAt_factorizes runtimeSeed .material).2.1,
    (coversAt_factorizes runtimeSeed .additiveRestriction).2.1,
    (coversAt_factorizes runtimeSeed .multiplicativeRestriction).2.1⟩

end CanonicalUnitArithmeticRoot
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
