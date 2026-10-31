import H0mework.Versions.R2.Foundation.Authority.OperationalInstallation

/-!
# Source-native operational-search focused regression

The fixture fixes a one-support world with two responsibility fields.  Its
ledger patch generates only the `false` row, while two sibling operational
sources consume `false` and `true` respectively.  The generated operational
effect remains source-fixed in both worlds, but only the independently
generated consumer row can enter target answer-and-next.  This separates
rooted effect provenance from fieldwise ledger authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace OperationalSearchSourceNativeRootRegression

def network : WorldRelationNetwork where
  Support := Unit
  Anchor := Unit
  Incidence := Unit
  Lineage := Unit
  Responsibility := Bool
  Claim := Bool
  anchorAt := fun _ => ()
  incidenceAt := fun _ => ()
  lineageAt := fun _ => ()
  OpenAt := fun _ _ => Unit
  openClaimAt := fun {_support} {responsibility} _ => responsibility
  HoldsAt := fun _ _ => Unit
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := fun obstruction => nomatch obstruction
  SemanticChangeAt := fun _ _ _ => Unit
  DispositionAt := fun _ _ => Unit

abbrev N := network

def vocabulary : Vocabulary where
  Current := Unit
  Anchor := Unit
  Incidence := Unit
  Lineage := Unit
  anchorAt := fun _ => ()
  incidenceAt := fun _ => ()
  lineageAt := fun _ => ()
  NativeWriteAt := fun _ => Unit
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  cofinal :=
    { Event := Unit
      emit? := some ()
      pathAt := fun _ _ => ()
      target := fun _ => () }
  nativeTarget := fun _ => ()
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev V := vocabulary

def entry (responsibility : Bool) : OpenResponsibilityAt N () :=
  ⟨responsibility, ()⟩

def openPresentation :
    ConstructivePresentation Bool (OpenResponsibilityAt N ()) where
  forward := entry
  backward := fun value => value.1
  backward_forward := fun _ => rfl
  forward_backward := by
    rintro ⟨responsibility, receipt⟩
    cases receipt
    rfl

def eventLaw : SourceNativeEventAlgebra N V where
  EventAt := fun _ _ => Unit
  compile := fun _ => .nativeWrite ()
  AffectedInventoryAt := fun _ => Bool
  affectedInventoryPresentation := fun _ => openPresentation
  anchorKey := fun _ => ()
  incidenceKey := fun _ => ()
  lineageKey := fun _ => ()
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl

def nativeSource : SourceNativeSource N V where
  initial := ()
  law := eventLaw

def emitted (_current : V.Current) :
    nativeSource.toRootSource.actual.OccurrenceAt () :=
  ⟨(), ()⟩

abbrev liveLedger : CompleteLiveLedgerAt N := ⟨()⟩

def liveEntry : OpenResponsibilityAt N () := entry false

def writeRowSource : LedgerWriteRowSourceAt nativeSource
    (fun _ _ _ _ => Unit) where
  IncidenceOccurrenceAt := fun _ _ sourceEntry targetEntry =>
    LedgerEntryEvolutionAt N sourceEntry targetEntry
  compileEvolution := fun event => event
  compileExact := fun _ => ()

def generatedPatch
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt ()) :
    FiniteGeneratedLedgerWritePatchAt writeRowSource occurrence liveLedger :=
  .identityRemainder
    { size := 1
      sourceEntryAt := fun _ => liveEntry
      targetEntryAt := fun _ => liveEntry
      rowAt := fun _ =>
        writeRowSource.generate (.transferred () rfl rfl (Nat.le_refl _)) }
    { destinationIndex := fun candidate =>
        match candidate with
        | ⟨false, receipt⟩ =>
            some ⟨⟨0, Nat.zero_lt_succ 0⟩, by cases receipt; rfl⟩
        | ⟨true, _⟩ => none
      originIndex := fun candidate =>
        match candidate with
        | ⟨false, receipt⟩ =>
            some ⟨⟨0, Nat.zero_lt_succ 0⟩, by cases receipt; rfl⟩
        | ⟨true, _⟩ => none }

def ledgerCompiler : SourceNativeLedgerCompiler nativeSource where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := fun _ _ _ _ => Unit
  exact_incidence := fun _ => ()
  exact_lineage := fun _ => rfl
  writeRowSource := writeRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty nativeSource
  compile := fun occurrence =>
    .nativeWrite () rfl (emitted ())
      (generatedPatch occurrence).toLedgerWriteEvolution
  compilePatch := fun occurrence =>
    ⟨generatedPatch occurrence, rfl⟩

def ledgerSource : SourceNativeLedgerSource N V where
  source := nativeSource
  ledgerCompiler := ledgerCompiler

def restructuringLaw : SourceNativeLedgerRestructuringLaw nativeSource :=
  identityOnlyWorldLedgerRestructuringLaw nativeSource () <| by
    intro support responsibility
    change Subsingleton Unit
    infer_instance

theorem generatedPatch_origin_entry_eq
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt ())
    (candidate : OpenResponsibilityAt N ()) :
    ((generatedPatch occurrence).toLedgerWriteEvolution.origin candidate).1 =
      candidate := by
  rcases candidate with ⟨responsibility, receipt⟩
  cases responsibility <;> cases receipt <;> rfl

theorem generatedPatch_destination_entry_eq
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt ())
    (candidate : OpenResponsibilityAt N ()) :
    ((generatedPatch occurrence).toLedgerWriteEvolution.destination candidate).1 =
      candidate := by
  rcases candidate with ⟨responsibility, receipt⟩
  cases responsibility <;> cases receipt <;> rfl

def restructuringCertification
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt ()) :
    SourceNativeLedgerRestructuringCertificationAt restructuringLaw
      (ledgerCompiler.compile occurrence) := by
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (by
      intro left right equality
      change
        ((generatedPatch occurrence).toLedgerWriteEvolution.origin left).1 =
          ((generatedPatch occurrence).toLedgerWriteEvolution.origin right).1
        at equality
      exact (generatedPatch_origin_entry_eq occurrence left).symm.trans
        (equality.trans (generatedPatch_origin_entry_eq occurrence right)))
    (by
      intro left right equality
      change
        ((generatedPatch occurrence).toLedgerWriteEvolution.destination left).1 =
          ((generatedPatch occurrence).toLedgerWriteEvolution.destination right).1
        at equality
      exact (generatedPatch_destination_entry_eq occurrence left).symm.trans
        (equality.trans (generatedPatch_destination_entry_eq occurrence right)))

def restructuringCompiler :
    SourceNativeRestructuringLedgerCompiler nativeSource where
  ledgerCompiler := ledgerCompiler
  restructuringLaw := restructuringLaw
  certifyRestructuring := restructuringCertification

def restructuringSource : SourceNativeRestructuringLedgerSource N V where
  source := nativeSource
  compiler := restructuringCompiler

def baseProjectionLaw :
    SourceNativeProjectionLaw restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} _ _ => Unit
  project := fun _ {_} _ _ => ()

def baseAuthoritySource : SourceNativeAuthoritySource N V where
  restructuringSource := restructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal restructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic N
  projectionLaw := baseProjectionLaw

def communication : ActualCommunicationNetwork N where
  Carrier := fun _ => Bool
  Observation := fun _ => Bool
  observe := fun _ value => value
  ContactAt := fun _ _ => Unit
  IncidenceTransportAt := fun _ _ => Unit
  LineageTransportAt := fun _ _ => Unit
  Event := PEmpty
  sourceSupport := PEmpty.elim
  targetSupport := PEmpty.elim
  contact := PEmpty.elim
  incidenceTransport := PEmpty.elim
  lineageTransport := PEmpty.elim
  carrierTransport := PEmpty.elim

abbrev C := communication

def payloadSource : ActualPayloadSource C where
  EventAt := fun _ => Unit
  emit := fun _ => ()
  payload := fun _ => true

def consumerSource (answer : Bool) : ActualTargetConsumerSource C where
  EventAt := fun _ _ => Unit
  emit := fun _ _ => ()
  EffectAt := fun _ => Bool
  effectFromObservation := fun _ _ => answer
  openEntryAt := fun _ => ⟨answer, ()⟩

/-- A target effect cannot lend authority to a sibling claim: the public
claim is definitionally the claim of the exact open responsibility row. -/
theorem consumer_claim_is_exact_open_row
    (answer observation : Bool) :
    (consumerSource answer).claimAt
        ((consumerSource answer).emit () observation) = answer :=
  rfl

theorem false_consumer_cannot_claim_true (observation : Bool) :
    (consumerSource false).claimAt
        ((consumerSource false).emit () observation) ≠ true := by
  intro equality
  cases equality

def operationalSources (answer : Bool) :
    ActualOperationalSeparationSources C where
  payloadSource := payloadSource
  consumerSource := consumerSource answer
  CutEventAt := fun _ _ => PEmpty
  cutSide := fun event => nomatch event
  cut_source_side := fun event => nomatch event
  cut_target_side := fun event => nomatch event
  cut_blocks := fun event => nomatch event
  cutObstruction := fun event => nomatch event

def u7 : U7ProducerCalculus N where
  DemandAt := fun obstruction => nomatch obstruction
  generateDemand := fun obstruction => nomatch obstruction

def u7Source : U7ActualSuccessorSource N u7 where
  EventAt := fun obstruction => nomatch obstruction
  emit := fun obstruction => nomatch obstruction
  demandGeneratedAt := fun event => nomatch event
  demandEntryAt := fun event => nomatch event

def u7Calculus : U7ObstructionEvolutionCalculus N u7 where
  source := u7Source
  compile := fun event => nomatch event

def searchProcess (answer : Bool) :
    ActualOperationalSearchProcess C (operationalSources answer) u7Calculus where
  QueryEventAt := fun _ _ => Unit
  admit := fun _ _ => ()
  emit := by
    intro source target query current
    cases source
    cases target
    exact .reached rfl

def initialQuery (answer : Bool) :
    (searchProcess answer).QueryEventAt () () :=
  (searchProcess answer).admit () ()

def initialSearchCurrent (answer : Bool) :
    OperationalSearchCurrentAt C () () :=
  (searchProcess answer).initial (initialQuery answer)

def initialHistory (answer : Bool) :
    GeneratedOperationalSearchPrefixAt
      (searchProcess answer) (initialQuery answer)
      (initialSearchCurrent answer) 0 :=
  .initial

def operationalLaw (answer : Bool) :
    SourceNativeOperationalSearchLaw ledgerSource where
  communication := C
  sources := operationalSources answer
  U7 := u7
  calculus := u7Calculus
  process := searchProcess answer
  positionAt := fun _ =>
    { source := ()
      target := ()
      query := initialQuery answer
      searchCurrent := initialSearchCurrent answer
      rootSupport_eq_frontier := rfl
      steps := 0
      history := initialHistory answer }
  continuation_commutes := by
    intro current occurrence continuation
    cases continuation.emitted_eq
  cut_disposition_commutes := by
    intro current occurrence cutEvent emitted_eq
    cases emitted_eq

def root (answer : Bool) : SourceNativeLivingRootClosure N V where
  source :=
    { base := baseAuthoritySource.withOperationalSearch (operationalLaw answer)
      terminalHandoff :=
        (baseAuthoritySource.withOperationalSearch
          (operationalLaw answer)).emptyFaithfulTerminalHandoff
          (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := emitted
  compiler_commutes := fun _ => rfl

def baseRoot : SourceNativeLivingRootClosure N V where
  source :=
    { base := baseAuthoritySource
      terminalHandoff := baseAuthoritySource.emptyFaithfulTerminalHandoff
        (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := emitted
  compiler_commutes := fun _ => rfl

def recognition (answer : Bool) :
    SourceNativeOperationalSearchRecognitionAt (root answer) where
  operationalLaw := operationalLaw answer
  installation := SourceNativeProjectionLaw.InstallationAt.operationalComponent
    baseAuthoritySource (operationalLaw answer)

/-- A search law cannot be recognized after emission when the fixed source
inventory did not install its operational component. -/
theorem fixed_base_root_rejects_posthoc_operational_search : True := by
  fail_if_success
    exact ({
      operationalLaw := operationalLaw false
      installation := SourceNativeProjectionLaw.InstallationAt.operationalComponent
        baseAuthoritySource (operationalLaw false)
    } : SourceNativeOperationalSearchRecognitionAt baseRoot)
  trivial

def falseVisit : RootVisit (root false).toAuthoritativeRoot.toRoot :=
  { current := ()
    history := .initial }

def trueVisit : RootVisit (root true).toAuthoritativeRoot.toRoot :=
  { current := ()
    history := .initial }

def falsePayload : SourceNativeOperationalSearchOutcomeAt
    (recognition false).operationalLaw
    ((root false).emitted falseVisit.current) :=
  (recognition false).generatedTemporalOutcomeAt
    (.finite falseVisit)

/-- The exact delivery branch is the fixed root operational effect.  Its
consumer responsibility still needs a generated causal row. -/
def falseDelivery : SourceNativeOperationalDeliveryAt
    (recognition false).operationalLaw
    ((root false).emitted falseVisit.current) :=
  ((recognition false).generatedTemporalOutcomeAt
    (.finite falseVisit)).getLeft (by rfl)

theorem false_delivery_target_is_root_support :
    ((recognition false).operationalLaw.positionAt
        ((root false).emitted falseVisit.current)).target =
      (root false).toAuthoritativeRoot.toRoot.supportAt falseVisit.current :=
  falseDelivery.target_eq_rootSupport (visit := .finite falseVisit)

def falseDeliveryRootConsumerEntry : OpenResponsibilityAt N
    ((root false).toAuthoritativeRoot.toRoot.supportAt falseVisit.current) :=
  falseDelivery.rootConsumerEntry (visit := .finite falseVisit)

theorem false_delivery_consumer_entry_is_generated_field :
    falseDeliveryRootConsumerEntry = entry false :=
  rfl

def falseDeliveryGeneratedRow :
    ((root false).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite falseVisit)).GeneratedEntryRowAt
        falseDeliveryRootConsumerEntry :=
  (((root false).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite falseVisit)).canonicalGeneratedEntryRow?
        falseDeliveryRootConsumerEntry).get (by rfl)

def falseDeliveryCausalAuthority :
    SourceNativeLivingTemporalCausalEntryAuthorityAt (root false)
      (.finite falseVisit) falseDeliveryRootConsumerEntry :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    (root false) falseDeliveryRootConsumerEntry falseDeliveryGeneratedRow

/-- Rooted effect plus the consumer field's own generated row enters the sole
target answer-and-next court. -/
def falseDeliveryTargetAnswerAndNext :
    SourceNativeLivingCausalEntryAnswerAndNextAt (root false)
      (.finite falseVisit) falseDeliveryRootConsumerEntry
        falseDeliveryCausalAuthority :=
  falseDelivery.targetAnswerAndNext falseDeliveryCausalAuthority

theorem false_delivery_consumer_effect_is_source_generated :
    falseDelivery.generated.delivery.effect = false :=
  rfl

theorem false_delivery_effect_is_root_factor :
    let visit : SourceNativeTemporalVisitAt
        (root false).toAuthoritativeRoot.toLedgerRoot := .finite falseVisit
    let evolution := (root false).canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        (root false).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          visit ∧
      HEq (evolution.generated.projectionOutcome
          (recognition false).rootOperationalProjection)
        (Sum.inl ⟨PUnit.unit, Sum.inl falseDelivery⟩ :
          SourceNativeProjectionFiberAt
            (recognition false).operationalLaw.toProjectionLaw PUnit.unit
            ((root false).emitted visit.current)) ∧
      evolution.nextCurrent = (root false).generatedNextCurrentAt visit :=
  falseDelivery.rootEffect_factorizes

def truePayload : SourceNativeOperationalSearchOutcomeAt
    (recognition true).operationalLaw
    ((root true).emitted trueVisit.current) :=
  (recognition true).generatedTemporalOutcomeAt
    (.finite trueVisit)

def trueDelivery : SourceNativeOperationalDeliveryAt
    (recognition true).operationalLaw
    ((root true).emitted trueVisit.current) :=
  ((recognition true).generatedTemporalOutcomeAt
    (.finite trueVisit)).getLeft (by rfl)

def trueDeliveryRootConsumerEntry : OpenResponsibilityAt N
    ((root true).toAuthoritativeRoot.toRoot.supportAt trueVisit.current) :=
  trueDelivery.rootConsumerEntry (visit := .finite trueVisit)

theorem true_delivery_consumer_entry_is_unselected_field :
    trueDeliveryRootConsumerEntry = entry true :=
  rfl

/-- A rooted delivery effect cannot make an unselected sibling responsibility
row canonical. -/
theorem true_delivery_consumer_row_is_absent :
    ((root true).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite trueVisit)).canonicalGeneratedEntryRow?
        trueDeliveryRootConsumerEntry = none :=
  rfl

/-- Consequently the public causal-authority producer refuses the sibling
field even though the operational effect itself is rooted. -/
theorem true_delivery_consumer_authority_is_not_generated :
    SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial?
      (root true) trueDeliveryRootConsumerEntry (.initial) = none :=
  rfl

/-- The absent row is a type-level boundary: no causal-entry authority exists
for the sibling consumer field at this exact visit. -/
theorem true_delivery_consumer_has_no_causal_authority :
    IsEmpty (SourceNativeLivingTemporalCausalEntryAuthorityAt (root true)
      (.finite trueVisit) trueDeliveryRootConsumerEntry) := by
  constructor
  intro authority
  have history := authority.toLedgerReadout
  cases history with
  | initialAdmission _entry row =>
      have selected :
          (((root true).toAuthoritativeRoot.toLedgerRoot
            |>.generatedAtTemporalVisit (.finite trueVisit))
            |>.canonicalGeneratedEntryRow?
              trueDeliveryRootConsumerEntry).isSome = true := by
        unfold SourceNativeTemporalVisitGeneratedEvolutionAt.canonicalGeneratedEntryRow?
        exact sourceNativeFiniteLedgerPatchGeneratedEntry?_isSome
          _ _ _ row.sourceRow
      exact Bool.noConfusion selected

def falseProductiveHistory :
    ProductiveFiniteRootHistoryAt
      (root false).toAuthoritativeRoot.toLedgerRoot where
  currentAt := fun _ => ()
  initial_eq := rfl
  next_eq := fun _ => rfl

def falseCofinalVisit : SourceNativeCofinalVisitAt
    (root false).toAuthoritativeRoot.toLedgerRoot :=
  (falseProductiveHistory.generatedCofinalVisit?
      (fun _emitted_eq _index => rfl)).get (by rfl)

def falseDeliveryEffect : Bool :=
  match (recognition false).generatedTemporalOutcomeAt (.finite falseVisit) with
  | .inl delivery => delivery.generated.delivery.effect
  | .inr (.inl obstruction) => nomatch obstruction.generated.cutEvent
  | .inr (.inr continuation) => nomatch continuation.continuation.edge.actualEvent

def trueDeliveryEffect : Bool :=
  match (recognition true).generatedTemporalOutcomeAt (.finite trueVisit) with
  | .inl delivery => delivery.generated.delivery.effect
  | .inr (.inl obstruction) => nomatch obstruction.generated.cutEvent
  | .inr (.inr continuation) => nomatch continuation.continuation.edge.actualEvent

/-- The exact source compiler fixes the operational delivery effect. -/
theorem fixed_source_generates_its_pre_emitter_consumer_effect :
    falseDeliveryEffect = false ∧ trueDeliveryEffect = true :=
  ⟨rfl, rfl⟩

/-- A cofinal query remains inside the same operational source law.  Since
this fixture emits an immediate delivery, the boundary cannot turn it into an
unknown, sibling cut, or caller-selected outcome. -/
def falseCofinalDeliveryEffect : Bool :=
  match (recognition false).generatedTemporalOutcomeAt
      (.cofinal falseCofinalVisit) with
  | .inl delivery => delivery.generated.delivery.effect
  | .inr (.inl obstruction) => nomatch obstruction.generated.cutEvent
  | .inr (.inr continuation) =>
      nomatch continuation.continuation.edge.actualEvent

theorem cofinal_operational_effect_is_same_source_answer :
    falseCofinalDeliveryEffect = false :=
  rfl

/-- Two sibling operational laws are part of two different generated source
identities.  They cannot reuse the flat base event and then erase their law
choice into one authoritative root. -/
theorem sibling_operational_laws_cannot_share_authoritative_root : True := by
  fail_if_success
    exact (rfl :
      (root false).toAuthoritativeRoot =
        (root true).toAuthoritativeRoot)
  trivial

/-- The current search frontier, not a stale historical query source, is the
exact support of the compiled root occurrence. -/
theorem operational_frontier_is_exact_root_support :
    ((recognition false).operationalLaw.positionAt
      ((root false).emitted falseVisit.current)).searchCurrent.frontier =
      nativeSource.toRootSource.account.supportOf (emitted ()) :=
  (recognition false).operationalFrontier_eq_rootSupport (.finite falseVisit)

/-- The domain search result, its exact temporal occurrence, and the living
successor are one root compiler image rather than three compatible receipts. -/
theorem operational_authority_is_root_answer_and_next_factor :
    let visit : SourceNativeTemporalVisitAt
        (root false).toAuthoritativeRoot.toLedgerRoot := .finite falseVisit
    let evolution := (root false).canonicalCausalAnswerAndNext (ULift.up visit)
    evolution.generated =
        (root false).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          visit ∧
      HEq (evolution.generated.projectionOutcome
          (recognition false).rootOperationalProjection)
          (Sum.inl ⟨PUnit.unit,
          (recognition false).generatedTemporalOutcomeAt visit⟩ :
            SourceNativeProjectionFiberAt
              (recognition false).operationalLaw.toProjectionLaw PUnit.unit
              ((root false).emitted visit.current)) ∧
      evolution.nextCurrent = (root false).generatedNextCurrentAt visit := by
  dsimp only
  exact (recognition false).installedAuthority_factorizes (.finite falseVisit)

/-- The source law inventory cannot execute its classifier at a bare
occurrence.  Operational authority first needs a registered temporal visit. -/
theorem raw_operational_executor_is_not_public : True := by
  fail_if_success
    exact (operationalLaw false).exhaustiveAt (emitted ())
  trivial

/-- The exact delivery constructor is likewise not a second public registry. -/
theorem caller_cannot_mint_delivery : True := by
  fail_if_success
    let _constructor := @SourceNativeOperationalDeliveryAt.mk
  trivial

/-- Replacing only the consumer produces another source type and cannot be
used as authority of the fixed false-consumer source. -/
theorem opposite_consumer_cannot_retype_as_same_source_authority : True := by
  fail_if_success
    exact (truePayload : SourceNativeOperationalSearchOutcomeAt
      (recognition false).operationalLaw
      ((root false).emitted falseVisit.current))
  trivial

#print axioms SourceNativeOperationalSearchRecognitionAt.installedAuthority_factorizes
#print axioms operational_authority_is_root_answer_and_next_factor
#print axioms fixed_base_root_rejects_posthoc_operational_search

end OperationalSearchSourceNativeRootRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
