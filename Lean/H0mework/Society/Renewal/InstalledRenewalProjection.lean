import H0mework.Society.Renewal.RootInstalledRenewalProjection
import H0mework.Foundation.Authority.Representation

/-!
# Source-installed renewal projection

An operational social renewal is not obtained by choosing a local seed after
the root has emitted an occurrence.  A `SourceNativeRenewalProjectionLaw` is
part of the complete authority source before emission.  At every source
occurrence its active payload contains, in one dependent package:

* the exact local `ProcessGame.SourceSeed`;
* the local responsibility consumer and disposition indexed by that seed;
* an exact row of the occurrence's canonical finite ledger patch; and
* a continuing successor of the same occurrence's whole-ledger compiler.

Consequently the temporal root row, operational standing, local face and
living next are restrictions of one compiler image.  The law is polymorphic
over the source, occurrence and temporal visit; concrete fixtures are only
consumers of this interface.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Renewal

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u

variable {N : WorldRelationNetwork.{u}}
variable {V : ConstructiveRoot.Vocabulary.{u}}
variable {LocalSource LocalState Seed Standing : Type u}
variable {Lineage : LocalSource → Type u}
variable {occurrenceOf : LocalSource → RootedAccountedUnfolding LocalState}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {SeedAt : LocalSource → LocalState → Seed → Prop}
variable {ConsumerAt DispositionAt :
  SourceSeed occurrenceOf Seed SeedAt game.source → Type u}

/-- One source-owned renewal payload at one exact root occurrence.

The ledger row and successor are indexed by the same occurrence as the local
seed payload.  The constructor is private so a caller cannot replace those
indices after the source classifier has run. -/
structure RootRestrictedRenewalPayloadAt
    (source : SourceNativeLedgerSource N V)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current)
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type u)
    (SeedAt : LocalSource → LocalState → Seed → Prop)
    (ConsumerAt DispositionAt :
      SourceSeed occurrenceOf Seed SeedAt game.source → Type u) : Type u where
  private mk ::
  sourceSeed : SourceSeed occurrenceOf Seed SeedAt game.source
  consumer : ConsumerAt sourceSeed
  disposition : DispositionAt sourceSeed
  sourceEntry : OpenResponsibilityAt N
    (source.source.toRootSource.account.supportOf occurrence)
  selectedRow : SourceNativeFiniteLedgerPatchGeneratedEntryAt source.source
    source.ledgerCompiler.ExactTransitionAt
    source.ledgerCompiler.writeRowSource
    source.ledgerCompiler.terminalRowSource
    (source.ledgerCompiler.compile occurrence)
    (source.ledgerCompiler.compilePatch occurrence)
    sourceEntry
  successor : SourceNativeLedgerGeneratedSuccessorAt occurrence
    (source.ledgerCompiler.compile occurrence)

namespace RootRestrictedRenewalPayloadAt

/-- Source-side constructor.  All six outputs are fixed before a later root
emitter or temporal visit can reveal a branch. -/
def generate
    {source : SourceNativeLedgerSource N V}
    {current : V.Current}
    {occurrence : source.source.toRootSource.actual.OccurrenceAt current}
    (sourceSeed : SourceSeed occurrenceOf Seed SeedAt game.source)
    (consumer : ConsumerAt sourceSeed)
    (disposition : DispositionAt sourceSeed)
    (sourceEntry : OpenResponsibilityAt N
      (source.source.toRootSource.account.supportOf occurrence))
    (selectedRow : SourceNativeFiniteLedgerPatchGeneratedEntryAt source.source
      source.ledgerCompiler.ExactTransitionAt
      source.ledgerCompiler.writeRowSource
      source.ledgerCompiler.terminalRowSource
      (source.ledgerCompiler.compile occurrence)
      (source.ledgerCompiler.compilePatch occurrence)
      sourceEntry)
    (successor : SourceNativeLedgerGeneratedSuccessorAt occurrence
      (source.ledgerCompiler.compile occurrence)) :
    RootRestrictedRenewalPayloadAt source occurrence game Seed SeedAt
      ConsumerAt DispositionAt :=
  ⟨sourceSeed, consumer, disposition, sourceEntry, selectedRow, successor⟩

end RootRestrictedRenewalPayloadAt

/-- A complete source-first renewal classifier and compiler.

It quantifies over every occurrence of the underlying root source.  Inactive
occurrences carry an explicit source receipt; active occurrences compile the
whole dependent renewal payload above. -/
structure SourceNativeRenewalProjectionLaw
    (source : SourceNativeLedgerSource N V)
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type u)
    (SeedAt : LocalSource → LocalState → Seed → Prop)
    (ConsumerAt DispositionAt :
      SourceSeed occurrenceOf Seed SeedAt game.source → Type u) : Type (u + 1) where
  ActiveAt : {current : V.Current} →
    source.source.toRootSource.actual.OccurrenceAt current → Type u
  InactiveAt : {current : V.Current} →
    source.source.toRootSource.actual.OccurrenceAt current → Type u
  classify : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
      ActiveAt occurrence ⊕ InactiveAt occurrence
  compile : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
    ActiveAt occurrence →
      RootRestrictedRenewalPayloadAt source occurrence game Seed SeedAt
        ConsumerAt DispositionAt
  /-- The local source seed cannot collapse two distinct active root
  occurrences.  Recurrent temporal visits to the *same* occurrence remain
  distinct through their temporal row indices. -/
  sourceSeed_reflects_rootOccurrence :
    {leftCurrent rightCurrent : V.Current} →
    (leftOccurrence :
      source.source.toRootSource.actual.OccurrenceAt leftCurrent) →
    (rightOccurrence :
      source.source.toRootSource.actual.OccurrenceAt rightCurrent) →
    (leftActive : ActiveAt leftOccurrence) →
    (rightActive : ActiveAt rightOccurrence) →
    (compile leftOccurrence leftActive).sourceSeed =
      (compile rightOccurrence rightActive).sourceSeed →
    (⟨leftCurrent, leftOccurrence⟩ :
      Sigma source.source.toRootSource.actual.OccurrenceAt) =
      ⟨rightCurrent, rightOccurrence⟩

/-- Root-owned inputs needed to assemble a renewal projection law whose local
seed, consumer, and disposition are already fixed by a source producer.

This is a shell over the existing ledger compiler, not another ledger.  It
can supply only that compiler's occurrence-indexed entry, exact patch row, and
generated successor. -/
structure SourceNativeRenewalRootShellAt
    (source : SourceNativeLedgerSource N V) where
  ActiveAt : {current : V.Current} →
    source.source.toRootSource.actual.OccurrenceAt current → Type u
  InactiveAt : {current : V.Current} →
    source.source.toRootSource.actual.OccurrenceAt current → Type u
  classify : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
      ActiveAt occurrence ⊕ InactiveAt occurrence
  sourceEntry : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
    ActiveAt occurrence →
      OpenResponsibilityAt N
        (source.source.toRootSource.account.supportOf occurrence)
  selectedRow : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
    (active : ActiveAt occurrence) →
      SourceNativeFiniteLedgerPatchGeneratedEntryAt source.source
        source.ledgerCompiler.ExactTransitionAt
        source.ledgerCompiler.writeRowSource
        source.ledgerCompiler.terminalRowSource
        (source.ledgerCompiler.compile occurrence)
        (source.ledgerCompiler.compilePatch occurrence)
        (sourceEntry occurrence active)
  successor : {current : V.Current} →
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) →
    ActiveAt occurrence →
      SourceNativeLedgerGeneratedSuccessorAt occurrence
        (source.ledgerCompiler.compile occurrence)
  activeOccurrences_eq :
    {leftCurrent rightCurrent : V.Current} →
    (leftOccurrence :
      source.source.toRootSource.actual.OccurrenceAt leftCurrent) →
    (rightOccurrence :
      source.source.toRootSource.actual.OccurrenceAt rightCurrent) →
    ActiveAt leftOccurrence → ActiveAt rightOccurrence →
      (⟨leftCurrent, leftOccurrence⟩ :
        Sigma source.source.toRootSource.actual.OccurrenceAt) =
      ⟨rightCurrent, rightOccurrence⟩

namespace SourceNativeRenewalProjectionLaw

/-- Assemble a renewal law from one source-generated local payload and the
existing root compiler shell.  No caller can replace the local payload after
the shell has selected an occurrence row. -/
def ofRootShell
    {source : SourceNativeLedgerSource N V}
    (shell : SourceNativeRenewalRootShellAt source)
    (sourceSeed : SourceSeed occurrenceOf Seed SeedAt game.source)
    (consumer : ConsumerAt sourceSeed)
    (disposition : DispositionAt sourceSeed) :
    SourceNativeRenewalProjectionLaw source game Seed SeedAt
      ConsumerAt DispositionAt where
  ActiveAt := shell.ActiveAt
  InactiveAt := shell.InactiveAt
  classify := shell.classify
  compile := by
    intro current occurrence active
    exact RootRestrictedRenewalPayloadAt.generate sourceSeed consumer
      disposition (shell.sourceEntry occurrence active)
      (shell.selectedRow occurrence active)
      (shell.successor occurrence active)
  sourceSeed_reflects_rootOccurrence := by
    intro leftCurrent rightCurrent leftOccurrence rightOccurrence
      leftActive rightActive _seedEq
    exact shell.activeOccurrences_eq leftOccurrence rightOccurrence
      leftActive rightActive

/-- Non-vacuous constant-projector rejection: any two distinct active root
occurrences, including occurrences at different currents, must generate
different local source seeds. -/
theorem distinctRootOccurrences_generate_distinctSourceSeeds
    {source : SourceNativeLedgerSource N V}
    (law : SourceNativeRenewalProjectionLaw source game Seed SeedAt
      ConsumerAt DispositionAt)
    {leftCurrent rightCurrent : V.Current}
    (leftOccurrence :
      source.source.toRootSource.actual.OccurrenceAt leftCurrent)
    (rightOccurrence :
      source.source.toRootSource.actual.OccurrenceAt rightCurrent)
    (leftActive : law.ActiveAt leftOccurrence)
    (rightActive : law.ActiveAt rightOccurrence)
    (distinct :
      (⟨leftCurrent, leftOccurrence⟩ :
        Sigma source.source.toRootSource.actual.OccurrenceAt) ≠
        ⟨rightCurrent, rightOccurrence⟩) :
    (law.compile leftOccurrence leftActive).sourceSeed ≠
      (law.compile rightOccurrence rightActive).sourceSeed := by
  intro seed_eq
  exact distinct (law.sourceSeed_reflects_rootOccurrence
    leftOccurrence rightOccurrence leftActive rightActive seed_eq)

/-- The renewal compiler as one source-native projection coordinate. -/
def toProjectionLaw
    {source : SourceNativeLedgerSource N V}
    (law : SourceNativeRenewalProjectionLaw source game Seed SeedAt
      ConsumerAt DispositionAt) :
    SourceNativeProjectionLaw source where
  Projection := PUnit
  ActiveAt := fun _ {_current} occurrence => law.ActiveAt occurrence
  InactiveAt := fun _ {_current} occurrence => law.InactiveAt occurrence
  classify := fun _ {_current} occurrence => law.classify occurrence
  PayloadAt := fun _ {_current} occurrence _active =>
    RootRestrictedRenewalPayloadAt source occurrence game Seed SeedAt
      ConsumerAt DispositionAt
  project := fun _ {_current} occurrence active => law.compile occurrence active

end SourceNativeRenewalProjectionLaw

/-- Canonical projection-inventory uplift.  This is an authority-source
constructor, not a function on an already emitted root. -/
inductive SourceNativeRenewalProjection (Base : Type u) : Type u
  | renewal
  | inherited (projection : Base)

/-- Install a renewal law in the complete authority source before emission,
while preserving every existing coordinate definitionally. -/
def withRenewalProjection
    (base : SourceNativeAuthoritySource N V)
    (law : SourceNativeRenewalProjectionLaw
      base.restructuringSource.toLedgerSource game Seed SeedAt
      ConsumerAt DispositionAt) :
    SourceNativeAuthoritySource N V where
  restructuringSource := base.restructuringSource
  eventInventoryAdmission := base.eventInventoryAdmission
  lawSurface := base.lawSurface
  projectionLaw :=
    { Projection := SourceNativeRenewalProjection
        base.projectionLaw.Projection
      ActiveAt := fun projection {_current} occurrence =>
        match projection with
        | .renewal => law.ActiveAt occurrence
        | .inherited inherited =>
            base.projectionLaw.ActiveAt inherited occurrence
      InactiveAt := fun projection {_current} occurrence =>
        match projection with
        | .renewal => law.InactiveAt occurrence
        | .inherited inherited =>
            base.projectionLaw.InactiveAt inherited occurrence
      classify := by
        intro projection current occurrence
        cases projection with
        | renewal => exact law.classify occurrence
        | inherited inherited =>
            exact base.projectionLaw.classify inherited occurrence
      PayloadAt := fun projection {_current} occurrence active =>
        match projection with
        | .renewal =>
            RootRestrictedRenewalPayloadAt
              base.restructuringSource.toLedgerSource occurrence game Seed SeedAt
              ConsumerAt DispositionAt
        | .inherited inherited =>
            base.projectionLaw.PayloadAt inherited occurrence active
      project := by
        intro projection current occurrence active
        cases projection with
        | renewal => exact law.compile occurrence active
        | inherited inherited =>
            exact base.projectionLaw.project inherited occurrence active }

/-- Existing authority coordinates survive the renewal visibility uplift. -/
def inheritedByRenewal
    (base : SourceNativeAuthoritySource N V)
    (law : SourceNativeRenewalProjectionLaw
      base.restructuringSource.toLedgerSource game Seed SeedAt
      ConsumerAt DispositionAt) :
    SourceNativeProjectionLaw.InstallationAt base.projectionLaw
      (withRenewalProjection base law).projectionLaw where
  embed := SourceNativeRenewalProjection.inherited
  embed_injective := by
    intro left right equality
    injection equality
  outcome_heq := by
    intro current occurrence projection
    dsimp only [SourceNativeProjectionLaw.outcomeAt,
      withRenewalProjection]
    cases base.projectionLaw.classify projection occurrence <;> rfl

/-- The renewal component is a faithful coordinate of the complete uplifted
source inventory. -/
def renewalComponent
    (base : SourceNativeAuthoritySource N V)
    (law : SourceNativeRenewalProjectionLaw
      base.restructuringSource.toLedgerSource game Seed SeedAt
      ConsumerAt DispositionAt) :
    SourceNativeProjectionLaw.InstallationAt law.toProjectionLaw
      (withRenewalProjection base law).projectionLaw where
  embed := fun _ => SourceNativeRenewalProjection.renewal
  embed_injective := by
    intro left right _
    cases left
    cases right
    rfl
  outcome_heq := by
    intro current occurrence projection
    cases projection
    dsimp only [SourceNativeProjectionLaw.outcomeAt,
      withRenewalProjection,
      SourceNativeRenewalProjectionLaw.toProjectionLaw]
    cases law.classify occurrence <;> rfl

/-- Recognition that a fixed living root was born with this renewal law in
its pre-emitter projection inventory.  It cannot install a post-hoc local
projector. -/
structure SourceNativeRenewalRecognitionAt
    (root : SourceNativeLivingRootClosure N V)
    (game : SaturationMonoid.ProcessGame occurrenceOf)
    (Seed : Type u)
    (SeedAt : LocalSource → LocalState → Seed → Prop)
    (ConsumerAt DispositionAt :
      SourceSeed occurrenceOf Seed SeedAt game.source → Type u) : Type (u + 2) where
  law : SourceNativeRenewalProjectionLaw
    root.toAuthoritativeRoot.toLedgerRoot.source game Seed SeedAt
      ConsumerAt DispositionAt
  installation : SourceNativeProjectionLaw.InstallationAt law.toProjectionLaw
    root.toAuthoritativeRoot.source.projectionLaw

namespace SourceNativeRenewalRecognitionAt

variable {root : SourceNativeLivingRootClosure N V}
variable (recognition : SourceNativeRenewalRecognitionAt root game Seed SeedAt
  ConsumerAt DispositionAt)

/-- Exact coordinate occupied by the renewal law in the fixed root. -/
def rootProjection :
    root.toAuthoritativeRoot.source.projectionLaw.Projection :=
  recognition.installation.embed PUnit.unit

/-- The installed component outcome is the source compiler outcome at the
same root occurrence. -/
theorem componentOutcome_heq_rootOutcome
    {current : V.Current}
    (occurrence : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      current) :
    HEq
      (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        recognition.rootProjection occurrence)
      (recognition.law.toProjectionLaw.outcomeAt PUnit.unit occurrence) :=
  recognition.installation.outcome_heq occurrence PUnit.unit

end SourceNativeRenewalRecognitionAt

/-- Active source-installed renewal at one arbitrary registered temporal
visit.  No row, successor, local seed, consumer or disposition is accepted at
this mouth: they are all read from the fixed source law. -/
structure SourceInstalledRenewalAt
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeRenewalRecognitionAt root game Seed SeedAt
      ConsumerAt DispositionAt)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) : Type (u + 2) where
  private mk ::
  active : recognition.law.ActiveAt (root.emitted visit.current)
  classified : recognition.law.classify (root.emitted visit.current) =
    .inl active

namespace SourceInstalledRenewalAt

variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : SourceNativeRenewalRecognitionAt root game Seed SeedAt
  ConsumerAt DispositionAt}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

/-- Generate the installed renewal only from the active branch selected by
the fixed source classifier. -/
def generate
    (active : recognition.law.ActiveAt (root.emitted visit.current))
    (classified : recognition.law.classify (root.emitted visit.current) =
      .inl active) :
    SourceInstalledRenewalAt recognition visit :=
  ⟨active, classified⟩

variable (installed : SourceInstalledRenewalAt recognition visit)

/-- Exact source payload at this root occurrence. -/
def payload : RootRestrictedRenewalPayloadAt
    root.toAuthoritativeRoot.toLedgerRoot.source
    (root.emitted visit.current) game Seed SeedAt ConsumerAt DispositionAt :=
  recognition.law.compile (root.emitted visit.current) installed.active

/-- Exact temporal row obtained by querying the canonical current patch with
the source payload's own row. -/
def temporalSelectedRow :
    (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit)
      |>.GeneratedEntryRowAt installed.payload.sourceEntry :=
  let generated :=
    root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit
  (generated.canonicalGeneratedEntryRow? installed.payload.sourceEntry).get
    (generated.canonicalGeneratedEntryRow?_isSome
      installed.payload.sourceEntry installed.payload.selectedRow)

/-- Operational renewal generated from the same payload's selected row and
whole-ledger successor. -/
def operationalAuthority :
    RootInstalledRenewalAt
      (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit)
      installed.payload.sourceEntry :=
  RootInstalledRenewalAt.install installed.temporalSelectedRow
    installed.payload.successor

/-- Independent root responsibility consumer generated by the installed
operational renewal. -/
def rootResponsibilityConsumer :
    RenewalResponsibilityConsumerAt installed.operationalAuthority :=
  installed.operationalAuthority.responsibilityConsumer

/-- Local face read from the same source payload. -/
def localFace
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source)
    (standingOf : SourceSeed occurrenceOf Seed SeedAt game.source → Standing) :
    SourceGeneratedRenewalFace game Seed SeedAt
      Lineage lineageOf Standing standingOf
      ConsumerAt DispositionAt :=
  SourceGeneratedRenewalFace.generate installed.payload.sourceSeed
    installed.payload.consumer installed.payload.disposition

@[simp] theorem localFace_sourceSeed
    (lineageOf : ∀ source,
      SourceSeed occurrenceOf Seed SeedAt source → Lineage source)
    (standingOf : SourceSeed occurrenceOf Seed SeedAt game.source → Standing) :
    (installed.localFace lineageOf standingOf).sourceSeed =
      installed.payload.sourceSeed :=
  rfl

/-- The source classifier outcome is exactly the active dependent payload. -/
theorem componentOutcome_eq_activePayload :
    recognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (root.emitted visit.current) =
      (.inl ⟨installed.active, installed.payload⟩ :
        SourceNativeProjectionFiberAt recognition.law.toProjectionLaw
          PUnit.unit (root.emitted visit.current)) := by
  simp only [SourceNativeProjectionLaw.outcomeAt,
    SourceNativeRenewalProjectionLaw.toProjectionLaw,
    installed.classified]
  rfl

/-- Proposition carried by every strong same-event installation: exact
temporal occurrence, installed renewal coordinate, and generated living next
are one root answer-and-next compiler image. -/
def RootAnswerAndNextFactorizes
    (_installed : SourceInstalledRenewalAt recognition visit) : Prop :=
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (evolution.generated.projectionOutcome
          recognition.rootProjection)
        (recognition.law.toProjectionLaw.outcomeAt PUnit.unit
          (root.emitted visit.current)) ∧
      evolution.nextCurrent = root.generatedNextCurrentAt visit

/-- Every installed source renewal satisfies the factorization proposition. -/
theorem rootAnswerAndNext_factorizes
    (installed : SourceInstalledRenewalAt recognition visit) :
    installed.RootAnswerAndNextFactorizes := by
  unfold RootAnswerAndNextFactorizes
  dsimp only
  exact
    (root.canonicalCausalAnswerAndNext
      (ULift.up visit)).installedSubsystemAuthority_factorizes
        recognition.installation PUnit.unit

/-- The local seed, local consumer and local disposition cannot outlive the
root occurrence: removing the fixed source-active branch removes the whole
installed face. -/
theorem inactive_noInstalledRenewal
    (installed : SourceInstalledRenewalAt recognition visit)
    (inactive : recognition.law.InactiveAt (root.emitted visit.current))
    (classifiedInactive :
      recognition.law.classify (root.emitted visit.current) = .inr inactive) :
    False := by
  rw [installed.classified] at classifiedInactive
  cases classifiedInactive

end SourceInstalledRenewalAt

/-- Without a source-installed component there is no strong renewal face,
even if a caller can separately exhibit a local seed or a ledger row. -/
theorem noInstalledComponent_noSourceInstalledRenewal
    {root : SourceNativeLivingRootClosure N V}
    (noInstallation : ∀ law : SourceNativeRenewalProjectionLaw
        root.toAuthoritativeRoot.toLedgerRoot.source game Seed SeedAt
          ConsumerAt DispositionAt,
      SourceNativeProjectionLaw.InstallationAt law.toProjectionLaw
        root.toAuthoritativeRoot.source.projectionLaw → False) :
    (Sigma fun recognition : SourceNativeRenewalRecognitionAt root game Seed SeedAt
        ConsumerAt DispositionAt =>
      Sigma fun visit : SourceNativeTemporalVisitAt
        root.toAuthoritativeRoot.toLedgerRoot =>
      SourceInstalledRenewalAt recognition visit) → False := by
  rintro ⟨recognition, _visit, _installed⟩
  exact noInstallation recognition.law recognition.installation

end Renewal
end Society
end ProcessGame
end SaturationMonoid
