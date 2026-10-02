import H0mework.Versions.R2.Foundation.Runtime.EffectDynamics

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- Source-owned data needed while one installed effect is inactive.

The inactive occurrence still names the exact live responsibility row.  A
later active occurrence may only be reached through `ReactivationReceiptAt`,
whose indices retain the source occurrence, the canonical successor, and the
target active witness. -/
structure SourceNativeEffectDormantVocabulary
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {eventVocabulary : SourceNativeEffectEventVocabulary source}
    (D : SourceNativeEffectDynamicalVocabulary eventVocabulary) : Type (u + 1) where
  inactiveEntryAt : {current : V.Current} →
    (occurrence : SourceNativeEffectOccurrenceAt eventVocabulary current) →
    D.InactiveAt occurrence → OpenResponsibilityAt N
      (source.source.toRootSource.account.supportOf occurrence.lower)
  ReactivationReceiptAt : {current : V.Current} →
    (occurrence : SourceNativeEffectOccurrenceAt eventVocabulary current) →
    (inactive : D.InactiveAt occurrence) →
    {generated : SourceNativeLedgerEvolutionAt source.source occurrence.lower} →
    (successor : SourceNativeEffectGeneratedSuccessorAt occurrence.lower generated) →
    (targetActive : D.ActiveAt
      (eventVocabulary.emit successor.targetOccurrence)) → Type u

/-- The dormant row is transported to the exact dormant target row by the
same whole-ledger evolution. -/
structure SourceNativeWholeDormantEffectLedgerTransportAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {eventVocabulary : SourceNativeEffectEventVocabulary source}
    (D : SourceNativeEffectDynamicalVocabulary eventVocabulary)
    (I : SourceNativeEffectDormantVocabulary D)
    {current : V.Current}
    {occurrence : SourceNativeEffectOccurrenceAt eventVocabulary current}
    {inactive : D.InactiveAt occurrence}
    {generated : SourceNativeLedgerEvolutionAt source.source occurrence.lower}
    (successor : SourceNativeEffectGeneratedSuccessorAt occurrence.lower generated)
    (targetInactive : D.InactiveAt
      (eventVocabulary.emit successor.targetOccurrence)) : Type u where
  targetEntry_eq :
    (successor.ledgerEvolution.destination
      (I.inactiveEntryAt occurrence inactive)).1 =
      I.inactiveEntryAt (eventVocabulary.emit successor.targetOccurrence)
        targetInactive

/-- Reactivation is a causal return of the same dormant row, not an
independent active classification at a later visit. -/
structure SourceNativeWholeEffectReactivationLedgerTransportAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {eventVocabulary : SourceNativeEffectEventVocabulary source}
    (D : SourceNativeEffectDynamicalVocabulary eventVocabulary)
    (I : SourceNativeEffectDormantVocabulary D)
    {current : V.Current}
    {occurrence : SourceNativeEffectOccurrenceAt eventVocabulary current}
    {inactive : D.InactiveAt occurrence}
    {generated : SourceNativeLedgerEvolutionAt source.source occurrence.lower}
    (successor : SourceNativeEffectGeneratedSuccessorAt occurrence.lower generated)
    (targetActive : D.ActiveAt
      (eventVocabulary.emit successor.targetOccurrence)) : Type u where
  targetEntry_eq :
    (successor.ledgerEvolution.destination
      (I.inactiveEntryAt occurrence inactive)).1 =
      D.effectEntryAt (eventVocabulary.emit successor.targetOccurrence)
        targetActive

/-- The inactive cut and U7 compiler expose the same exact row disposition. -/
def SourceNativeDormantEffectU7CutCommutesAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {eventVocabulary : SourceNativeEffectEventVocabulary source}
    (D : SourceNativeEffectDynamicalVocabulary eventVocabulary)
    (I : SourceNativeEffectDormantVocabulary D)
    {U7 : U7ProducerCalculus N}
    (calculus : U7ObstructionEvolutionCalculus N U7)
    {current : V.Current}
    {occurrence : SourceNativeEffectOccurrenceAt eventVocabulary current}
    {inactive : D.InactiveAt occurrence}
    {generated : SourceNativeLedgerEvolutionAt source.source occurrence.lower}
    (successor : SourceNativeEffectGeneratedSuccessorAt occurrence.lower generated)
    (obstruction : N.ObstructionAt
      (source.source.toRootSource.account.supportOf occurrence.lower)) : Prop :=
  HEq
    (LedgerEntryDispositionAt.evolved
      (successor.ledgerEvolution.destination
        (I.inactiveEntryAt occurrence inactive)).2)
    (calculus.generated obstruction).2.entryDisposition

/-- Exhaustive source-generated disposition of one inactive effect row.

There is no bare `inactive → active` constructor.  A return to the active
fibre carries the exact whole-ledger transport and one source-native
reactivation receipt. -/
inductive SourceNativeDormantEffectDispositionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {eventVocabulary : SourceNativeEffectEventVocabulary source}
    (D : SourceNativeEffectDynamicalVocabulary eventVocabulary)
    (I : SourceNativeEffectDormantVocabulary D)
    {U7 : U7ProducerCalculus N}
    (calculus : U7ObstructionEvolutionCalculus N U7)
    {current : V.Current}
    (occurrence : SourceNativeEffectOccurrenceAt eventVocabulary current)
    (inactive : D.InactiveAt occurrence)
    (generated : SourceNativeLedgerEvolutionAt source.source occurrence.lower) : Type u
  | settled
      (terminal : SourceNativeEffectTerminalAt generated
        (I.inactiveEntryAt occurrence inactive))
  | dormantNext
      (row : SourceNativeEffectGeneratedEntryAt
        (occurrence := occurrence.lower)
        (I.inactiveEntryAt occurrence inactive))
      (successor : SourceNativeEffectGeneratedSuccessorAt occurrence.lower generated)
      (targetInactive : D.InactiveAt
        (eventVocabulary.emit successor.targetOccurrence))
      (target_classify_eq :
        D.classify (eventVocabulary.emit successor.targetOccurrence) =
          .inr targetInactive)
      (ledgerTransport : SourceNativeWholeDormantEffectLedgerTransportAt
        (inactive := inactive) D I successor targetInactive)
  | reactivated
      (row : SourceNativeEffectGeneratedEntryAt
        (occurrence := occurrence.lower)
        (I.inactiveEntryAt occurrence inactive))
      (successor : SourceNativeEffectGeneratedSuccessorAt occurrence.lower generated)
      (targetActive : D.ActiveAt
        (eventVocabulary.emit successor.targetOccurrence))
      (target_classify_eq :
        D.classify (eventVocabulary.emit successor.targetOccurrence) =
          .inl targetActive)
      (ledgerTransport : SourceNativeWholeEffectReactivationLedgerTransportAt
        (inactive := inactive) D I successor targetActive)
      (receipt : I.ReactivationReceiptAt occurrence inactive successor targetActive)
  | cut
      (row : SourceNativeEffectGeneratedEntryAt
        (occurrence := occurrence.lower)
        (I.inactiveEntryAt occurrence inactive))
      (successor : SourceNativeEffectGeneratedSuccessorAt occurrence.lower generated)
      (obstruction : N.ObstructionAt
        (source.source.toRootSource.account.supportOf occurrence.lower))
      (demandEntry_eq :
        U7ActualSuccessorSource.demandEntry
            (calculus.generated obstruction).1 =
          I.inactiveEntryAt occurrence inactive)
      (disposition_commutes : SourceNativeDormantEffectU7CutCommutesAt
        (inactive := inactive) D I calculus successor obstruction)

/-- Source-sealed completion of an effect law across its inactive fibre. -/
structure SourceNativeEffectReactivationClosureLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V) : Type (u + 1) where
  private mk ::
  effectLaw : SourceNativeEffectDynamicalClosureLaw source
  dormantVocabulary : SourceNativeEffectDormantVocabulary effectLaw.vocabulary
  private generateInactive : {current : V.Current} →
    (occurrence : SourceNativeEffectOccurrenceAt
      effectLaw.eventVocabulary current) →
    (inactive : effectLaw.vocabulary.InactiveAt occurrence) →
      SourceNativeDormantEffectDispositionAt effectLaw.vocabulary
        dormantVocabulary effectLaw.calculus occurrence inactive
        (source.ledgerCompiler.compile occurrence.lower)

def SourceNativeEffectReactivationClosureLaw.create
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    (effectLaw : SourceNativeEffectDynamicalClosureLaw source)
    (dormantVocabulary : SourceNativeEffectDormantVocabulary effectLaw.vocabulary)
    (generateInactive : {current : V.Current} →
      (occurrence : SourceNativeEffectOccurrenceAt
        effectLaw.eventVocabulary current) →
      (inactive : effectLaw.vocabulary.InactiveAt occurrence) →
        SourceNativeDormantEffectDispositionAt effectLaw.vocabulary
          dormantVocabulary effectLaw.calculus occurrence inactive
          (source.ledgerCompiler.compile occurrence.lower)) :
    SourceNativeEffectReactivationClosureLaw source :=
  ⟨effectLaw, dormantVocabulary, generateInactive⟩

/-- Total active/dormant status generated by the original effect classifier. -/
abbrev SourceNativeEffectLifecycleStatusAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    (law : SourceNativeEffectReactivationClosureLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) : Type u :=
  law.effectLaw.vocabulary.ActiveAt
      (law.effectLaw.eventVocabulary.emit occurrence) ⊕
    law.effectLaw.vocabulary.InactiveAt
      (law.effectLaw.eventVocabulary.emit occurrence)

/-- Complete lifecycle payload at one exact source occurrence. -/
def SourceNativeGeneratedEffectLifecycleClosureAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    (law : SourceNativeEffectReactivationClosureLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current)
    (status : SourceNativeEffectLifecycleStatusAt law occurrence) : Type u :=
  match status with
  | .inl active =>
      SourceNativeGeneratedEffectDynamicalClosureAt law.effectLaw occurrence active
  | .inr inactive =>
      SourceNativeDormantEffectDispositionAt law.effectLaw.vocabulary
        law.dormantVocabulary law.effectLaw.calculus
        (law.effectLaw.eventVocabulary.emit occurrence) inactive
        (source.ledgerCompiler.compile occurrence)

/-- Total lifecycle face.  It is active at every exact source occurrence;
the payload itself is the source classifier's active or dormant branch. -/
def SourceNativeEffectReactivationClosureLaw.toProjectionLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    (law : SourceNativeEffectReactivationClosureLaw source) :
    SourceNativeProjectionLaw source where
  Projection := PUnit
  ActiveAt := fun _ {_current} occurrence =>
    SourceNativeEffectLifecycleStatusAt law occurrence
  InactiveAt := fun _ {_current} _occurrence => PEmpty
  classify := fun _ {_current} occurrence =>
    .inl (law.effectLaw.vocabulary.classify
      (law.effectLaw.eventVocabulary.emit occurrence))
  PayloadAt := fun _ {_current} occurrence status =>
    SourceNativeGeneratedEffectLifecycleClosureAt law occurrence status
  project := by
    intro _ current occurrence status
    cases status with
    | inl active =>
        change SourceNativeGeneratedEffectDynamicalClosureAt
          law.effectLaw occurrence active
        exact law.effectLaw.toProjectionLaw.project PUnit.unit occurrence active
    | inr inactive =>
        change SourceNativeDormantEffectDispositionAt
          law.effectLaw.vocabulary law.dormantVocabulary
          law.effectLaw.calculus
          (law.effectLaw.eventVocabulary.emit occurrence) inactive
          (source.ledgerCompiler.compile occurrence)
        exact law.generateInactive
          (law.effectLaw.eventVocabulary.emit occurrence) inactive

/-- Visibility uplift installing the total effect lifecycle before emission. -/
inductive SourceNativeEffectReactivationProjection (Base : Type u) : Type u
  | lifecycle
  | inherited (projection : Base)

def SourceNativeEffectReactivationClosureLaw.toAuthoritySource
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (base : SourceNativeAuthoritySource N V)
    (law : SourceNativeEffectReactivationClosureLaw
      base.restructuringSource.toLedgerSource) :
    SourceNativeAuthoritySource N V where
  restructuringSource := base.restructuringSource
  observationAt := base.observationAt
  eventInventoryAdmission := base.eventInventoryAdmission
  lawSurface := base.lawSurface
  projectionLaw :=
    { Projection := SourceNativeEffectReactivationProjection
        base.projectionLaw.Projection
      ActiveAt := fun projection {_current} occurrence =>
        match projection with
        | .lifecycle => SourceNativeEffectLifecycleStatusAt law occurrence
        | .inherited inherited =>
            base.projectionLaw.ActiveAt inherited occurrence
      InactiveAt := fun projection {_current} occurrence =>
        match projection with
        | .lifecycle => PEmpty
        | .inherited inherited =>
            base.projectionLaw.InactiveAt inherited occurrence
      classify := by
        intro projection current occurrence
        cases projection with
        | lifecycle =>
            exact .inl (law.effectLaw.vocabulary.classify
              (law.effectLaw.eventVocabulary.emit occurrence))
        | inherited inherited =>
            exact base.projectionLaw.classify inherited occurrence
      PayloadAt := fun projection {_current} occurrence active =>
        match projection with
        | .lifecycle =>
            SourceNativeGeneratedEffectLifecycleClosureAt law occurrence active
        | .inherited inherited =>
            base.projectionLaw.PayloadAt inherited occurrence active
      project := by
        intro projection current occurrence active
        cases projection with
        | lifecycle =>
            exact law.toProjectionLaw.project PUnit.unit occurrence active
        | inherited inherited =>
            exact base.projectionLaw.project inherited occurrence active }

/-- Existing coordinates remain exact components of the lifecycle uplift. -/
def SourceNativeProjectionLaw.InstallationAt.inheritedByEffectReactivation
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (base : SourceNativeAuthoritySource N V)
    (law : SourceNativeEffectReactivationClosureLaw
      base.restructuringSource.toLedgerSource) :
    SourceNativeProjectionLaw.InstallationAt base.projectionLaw
      (law.toAuthoritySource base).projectionLaw where
  embed := SourceNativeEffectReactivationProjection.inherited
  embed_injective := by
    intro left right equality
    injection equality
  outcome_heq := by
    intro current occurrence projection
    dsimp only [SourceNativeProjectionLaw.outcomeAt,
      SourceNativeEffectReactivationClosureLaw.toAuthoritySource]
    cases base.projectionLaw.classify projection occurrence <;> rfl

/-- The lifecycle face is installed as one coordinate of the same authority
source; it is not a sibling root or a second responsibility ledger. -/
def SourceNativeProjectionLaw.InstallationAt.effectReactivationComponent
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (base : SourceNativeAuthoritySource N V)
    (law : SourceNativeEffectReactivationClosureLaw
      base.restructuringSource.toLedgerSource) :
    SourceNativeProjectionLaw.InstallationAt law.toProjectionLaw
      (law.toAuthoritySource base).projectionLaw where
  embed := fun _ => SourceNativeEffectReactivationProjection.lifecycle
  embed_injective := by
    intro left right _
    cases left
    cases right
    rfl
  outcome_heq := by
    intro current occurrence projection
    cases projection
    dsimp only [SourceNativeProjectionLaw.outcomeAt,
      SourceNativeEffectReactivationClosureLaw.toAuthoritySource,
      SourceNativeEffectReactivationClosureLaw.toProjectionLaw]
    rfl

/-- Exact live row selected by one lifecycle status. -/
def SourceNativeEffectReactivationClosureLaw.entryAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    (law : SourceNativeEffectReactivationClosureLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current)
    (status : SourceNativeEffectLifecycleStatusAt law occurrence) :
    OpenResponsibilityAt N
      (source.source.toRootSource.account.supportOf occurrence) :=
  match status with
  | .inl active => law.effectLaw.vocabulary.effectEntryAt
      (law.effectLaw.eventVocabulary.emit occurrence) active
  | .inr inactive => law.dormantVocabulary.inactiveEntryAt
      (law.effectLaw.eventVocabulary.emit occurrence) inactive

/-- Recognition that a fixed living root was born with the total effect
lifecycle face in its pre-emitter source inventory. -/
structure SourceNativeEffectReactivationRecognitionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V) : Type (u + 2) where
  lifecycleLaw : SourceNativeEffectReactivationClosureLaw
    root.toAuthoritativeRoot.toLedgerRoot.source
  installation : SourceNativeProjectionLaw.InstallationAt
    lifecycleLaw.toProjectionLaw
    root.toAuthoritativeRoot.source.projectionLaw

namespace SourceNativeEffectReactivationRecognitionAt

def rootLifecycleProjection
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeEffectReactivationRecognitionAt root) :
    root.toAuthoritativeRoot.source.projectionLaw.Projection :=
  recognition.installation.embed PUnit.unit

def lifecycleComponent
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeEffectReactivationRecognitionAt root) :
    SourceNativeProjectionLaw
      root.toAuthoritativeRoot.toLedgerRoot.source :=
  recognition.lifecycleLaw.toProjectionLaw

/-- Rooted total lifecycle outcome.  Its status is fixed by the source
classifier and its exact row authority comes from the same temporal ledger. -/
structure RootedLifecycleOutcomeAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeEffectReactivationRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) : Type (u + 1) where
  private mk ::
  status : SourceNativeEffectLifecycleStatusAt recognition.lifecycleLaw
    (root.emitted visit.current)
  private classify_eq :
    recognition.lifecycleLaw.effectLaw.vocabulary.classify
        (recognition.lifecycleLaw.effectLaw.eventVocabulary.emit
          (root.emitted visit.current)) = status
  sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit
    (recognition.lifecycleLaw.entryAt
      (root.emitted visit.current) status)

def generatedRootedLifecycleAtVisit
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeEffectReactivationRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (status : SourceNativeEffectLifecycleStatusAt recognition.lifecycleLaw
      (root.emitted visit.current))
    (classify_eq :
      recognition.lifecycleLaw.effectLaw.vocabulary.classify
          (recognition.lifecycleLaw.effectLaw.eventVocabulary.emit
            (root.emitted visit.current)) = status)
    (sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit
      (recognition.lifecycleLaw.entryAt
        (root.emitted visit.current) status)) :
    recognition.RootedLifecycleOutcomeAt visit :=
  ⟨status, classify_eq, sourceAuthority⟩

namespace RootedLifecycleOutcomeAt

def payload
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeEffectReactivationRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (registered : recognition.RootedLifecycleOutcomeAt visit) :
    SourceNativeGeneratedEffectLifecycleClosureAt recognition.lifecycleLaw
      (root.emitted visit.current) registered.status :=
  recognition.lifecycleComponent.project PUnit.unit
    (root.emitted visit.current) registered.status

/-- Canonical source classification fixes the status and therefore the whole
dependent lifecycle payload at one exact visit. -/
theorem status_eq_of_same_visit
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeEffectReactivationRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (left right : recognition.RootedLifecycleOutcomeAt visit) :
    left.status = right.status :=
  left.classify_eq.symm.trans right.classify_eq

theorem payload_heq_of_same_visit
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeEffectReactivationRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (left right : recognition.RootedLifecycleOutcomeAt visit) :
    HEq left.payload right.payload := by
  apply SourceNativeProjectionLaw.project_heq_of_classify_eq
    recognition.lifecycleComponent
  · change Sum.inl
      (recognition.lifecycleLaw.effectLaw.vocabulary.classify
        (recognition.lifecycleLaw.effectLaw.eventVocabulary.emit
          (root.emitted visit.current))) = Sum.inl left.status
    rw [left.classify_eq]
  · change Sum.inl
      (recognition.lifecycleLaw.effectLaw.vocabulary.classify
        (recognition.lifecycleLaw.effectLaw.eventVocabulary.emit
          (root.emitted visit.current))) = Sum.inl right.status
    rw [right.classify_eq]

end RootedLifecycleOutcomeAt
end SourceNativeEffectReactivationRecognitionAt

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
