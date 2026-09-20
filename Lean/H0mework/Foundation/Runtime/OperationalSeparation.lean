import H0mework.Foundation.Inquiry.ObstructionLineage
import H0mework.Foundation.Responsibility.Observer

/-!
# Source-owned operational separation

This kernel replaces a bare graph-distance question by an actual transport
question.  A contact is a source event with exact world endpoints,
incidence/lineage transport, and a whole-carrier presentation.  Finite paths
are generated only by composing those events and now generate their own
dependent trace and whole-carrier write-back.  Payload and target-consumer
events come from a fixed source algebra; observer safety is proved by the
exact consumer factorization.  A failed path carries one actual cut event,
whose partition, blocking law, and obstruction are canonical projections
before the obstruction enters the existing U7 successor calculus.

There is no `unknown` constructor, raw outcome oracle, preloaded terminal
path/cut witness, or caller-supplied result compiler.  Pair admission creates
only an empty-path current.  The fixed source-native search process must then
emit, at that exact current, either one actual contact continuation, an exact
frontier cut event, or a proof that the already generated frontier has reached
the target.  Finite delivery and obstruction packages retain the same query
and the exact sequence of emitted continuations.  Numeric distance bounds,
including a possible bound of six in a concrete social network, are downstream
readouts of generated path lengths rather than connectivity premises.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution

universe u

/-- Source-owned communication algebra over one world relation network.
Contact events determine their exact endpoints and carry explicit transport
for the payload carrier, incidence, and lineage. -/
structure ActualCommunicationNetwork
    (N : WorldRelationNetwork.{u}) : Type (u + 1) where
  Carrier : N.Support → Type u
  Observation : N.Support → Type u
  observe : (support : N.Support) → Carrier support → Observation support
  ContactAt : N.Anchor → N.Anchor → Type u
  IncidenceTransportAt : N.Incidence → N.Incidence → Type u
  LineageTransportAt : N.Lineage → N.Lineage → Type u
  Event : Type u
  sourceSupport : Event → N.Support
  targetSupport : Event → N.Support
  contact : (event : Event) →
    ContactAt (N.anchorAt (sourceSupport event))
      (N.anchorAt (targetSupport event))
  incidenceTransport : (event : Event) →
    IncidenceTransportAt (N.incidenceAt (sourceSupport event))
      (N.incidenceAt (targetSupport event))
  lineageTransport : (event : Event) →
    LineageTransportAt (N.lineageAt (sourceSupport event))
      (N.lineageAt (targetSupport event))
  carrierTransport : (event : Event) →
    ConstructivePresentation (Carrier (sourceSupport event))
      (Carrier (targetSupport event))

/-- Exact endpoint recognition of one actual contact event.  No edge exists
without an event from the communication source. -/
structure ActualContactEdgeAt
    {N : WorldRelationNetwork.{u}}
    (C : ActualCommunicationNetwork N)
    (source target : N.Support) : Type u where
  actualEvent : C.Event
  source_eq : C.sourceSupport actualEvent = source
  target_eq : C.targetSupport actualEvent = target

namespace ActualContactEdgeAt

variable
  {N : WorldRelationNetwork.{u}}
  {C : ActualCommunicationNetwork N}
  {source target : N.Support}

/-- Every actual contact event has a canonical dependent edge at its own
source and target supports. -/
def canonical (event : C.Event) :
    ActualContactEdgeAt C (C.sourceSupport event) (C.targetSupport event) :=
  ⟨event, rfl, rfl⟩

/-- Reindex the event's source-owned carrier presentation to the exact public
endpoint indices. -/
def carrierPresentation (edge : ActualContactEdgeAt C source target) :
    ConstructivePresentation (C.Carrier source) (C.Carrier target) :=
  (ConstructivePresentation.cast
      (F := C.Carrier) edge.source_eq.symm).trans <|
    (C.carrierTransport edge.actualEvent).trans <|
      ConstructivePresentation.cast (F := C.Carrier) edge.target_eq

end ActualContactEdgeAt

/-- Finite source-owned transport path.  The only non-reflexive constructor
adds an exact actual contact edge; arbitrary endpoint relations cannot enter
the path. -/
inductive SourceOwnedTransportPath
    {N : WorldRelationNetwork.{u}}
    (C : ActualCommunicationNetwork N) :
    N.Support → N.Support → Type u
  | nil (support : N.Support) : SourceOwnedTransportPath C support support
  | cons {source middle target : N.Support}
      (edge : ActualContactEdgeAt C source middle)
      (tail : SourceOwnedTransportPath C middle target) :
      SourceOwnedTransportPath C source target

namespace SourceOwnedTransportPath

variable
  {N : WorldRelationNetwork.{u}}
  {C : ActualCommunicationNetwork N}
  {source target : N.Support}

def length : {source target : N.Support} →
    SourceOwnedTransportPath C source target → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ tail => length tail + 1

/-- Ordered actual-event trace of the path. -/
def events : {source target : N.Support} →
    SourceOwnedTransportPath C source target → List C.Event
  | _, _, .nil _ => []
  | _, _, .cons edge tail => edge.actualEvent :: events tail

/-- Whole-carrier transport is generated by ordered composition of the exact
edge presentations. -/
def carrierPresentation : {source target : N.Support} →
    (path : SourceOwnedTransportPath C source target) →
      ConstructivePresentation (C.Carrier source) (C.Carrier target)
  | _, _, .nil support => ConstructivePresentation.refl (C.Carrier support)
  | _, _, .cons edge tail =>
      edge.carrierPresentation.trans (carrierPresentation tail)

def transport : {source target : N.Support} →
    SourceOwnedTransportPath C source target →
      C.Carrier source → C.Carrier target
  | _, _, .nil _, value => value
  | _, _, .cons edge tail, value =>
      transport tail (edge.carrierPresentation.forward value)

theorem transport_eq_carrierPresentation
    (path : SourceOwnedTransportPath C source target)
    (value : C.Carrier source) :
    path.transport value = path.carrierPresentation.forward value := by
  induction path with
  | nil => rfl
  | cons edge tail inductionHypothesis =>
      change tail.transport (edge.carrierPresentation.forward value) =
        tail.carrierPresentation.forward
          (edge.carrierPresentation.forward value)
      exact inductionHypothesis _

/-- Append one newly emitted contact edge to an already generated path.  The
new endpoint is determined by the edge; callers cannot submit a replacement
path or terminal target. -/
def snoc : {source frontier next : N.Support} →
    SourceOwnedTransportPath C source frontier →
    ActualContactEdgeAt C frontier next →
    SourceOwnedTransportPath C source next
  | _, _, next, .nil _, edge =>
      .cons edge (.nil next)
  | _, _, _, .cons head tail, edge =>
      .cons head (snoc tail edge)

theorem length_snoc
    {source frontier next : N.Support}
    (path : SourceOwnedTransportPath C source frontier)
    (edge : ActualContactEdgeAt C frontier next) :
    (path.snoc edge).length = path.length + 1 := by
  induction path with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change (tail.snoc edge).length + 1 = (tail.length + 1) + 1
      rw [inductionHypothesis]

/-- Dependent trace generated by replaying one exact source-owned contact
path on one source value.  The endpoint of every constructor is determined
by the corresponding contact presentation; no caller supplies a target. -/
inductive GeneratedTransportTraceAt :
    {source target : N.Support} →
    (path : SourceOwnedTransportPath C source target) →
    (sourceValue : C.Carrier source) → C.Carrier target → Type u
  | nil (support : N.Support) (value : C.Carrier support) :
      GeneratedTransportTraceAt (.nil support) value value
  | cons {source middle target : N.Support}
      (edge : ActualContactEdgeAt C source middle)
      (tail : SourceOwnedTransportPath C middle target)
      (sourceValue : C.Carrier source) (targetValue : C.Carrier target)
      (tailTrace : GeneratedTransportTraceAt tail
        (edge.carrierPresentation.forward sourceValue) targetValue) :
      GeneratedTransportTraceAt (.cons edge tail) sourceValue targetValue

/-- Canonical replay trace of the exact contact path. -/
def generatedTrace : {source target : N.Support} →
    (path : SourceOwnedTransportPath C source target) →
    (sourceValue : C.Carrier source) →
      GeneratedTransportTraceAt path sourceValue (path.transport sourceValue)
  | _, _, .nil support, value => .nil support value
  | _, _, .cons edge tail, value =>
      .cons edge tail value _
        (generatedTrace tail (edge.carrierPresentation.forward value))

/-- Canonical whole-carrier write-back of one generated path.  The target,
trace, and endpoint equation all come from the same ordered contact run. -/
structure GeneratedPathWriteBackAt
    (path : SourceOwnedTransportPath C source target)
    (sourceValue : C.Carrier source) : Type u where
  private mk ::
  targetValue : C.Carrier target
  trace : GeneratedTransportTraceAt path sourceValue targetValue
  target_eq : targetValue = path.transport sourceValue

/-- Generate the only public write-back from the exact path and source value. -/
def generatedWriteBack
    (path : SourceOwnedTransportPath C source target)
    (sourceValue : C.Carrier source) :
    GeneratedPathWriteBackAt path sourceValue :=
  ⟨path.transport sourceValue, path.generatedTrace sourceValue, rfl⟩

/-- A dependent trace over one exact source-owned path is its canonical replay.
The path index fixes every intermediate carrier coordinate. -/
theorem generatedTransportTrace_eq
    (path : SourceOwnedTransportPath C source target)
    (sourceValue : C.Carrier source)
    (trace : GeneratedTransportTraceAt path sourceValue
      (path.transport sourceValue)) :
    trace = path.generatedTrace sourceValue := by
  induction path with
  | nil =>
      cases trace
      rfl
  | cons edge tail inductionHypothesis =>
      cases trace with
      | cons _ _ _ _ tailTrace =>
          rw [inductionHypothesis _ tailTrace]
          rfl

/-- Every whole-carrier write-back inhabitant is the exact replay compiler
image; a hypothetical value cannot replace its trace or endpoint. -/
theorem GeneratedPathWriteBackAt.eq_generated
    {path : SourceOwnedTransportPath C source target}
    {sourceValue : C.Carrier source}
    (writeBack : GeneratedPathWriteBackAt path sourceValue) :
    writeBack = path.generatedWriteBack sourceValue := by
  rcases writeBack with ⟨targetValue, trace, target_eq⟩
  cases target_eq
  rw [generatedTransportTrace_eq path sourceValue trace]
  rfl

end SourceOwnedTransportPath

/-- Source-native payload producer.  Its dependent support is the anchor,
incidence, and lineage authority; the source stores no duplicate provenance
fields that a generated payload could accidentally ground. -/
structure ActualPayloadSource
    {N : WorldRelationNetwork.{u}}
    (C : ActualCommunicationNetwork N) : Type (u + 1) where
  EventAt : N.Support → Type u
  emit : (support : N.Support) → EventAt support
  payload : {support : N.Support} → EventAt support → C.Carrier support

/-- Source-native target consumer.  Its event is indexed by the exact target
observation, so consumer safety is generated by factorization through that
observation rather than assumed as global injectivity of the observer.

The consumer names exactly one open responsibility row.  Its claim, anchor,
incidence, and lineage are derived from that row and its dependent support;
they are not sibling fields that can borrow authority from the generated
effect. -/
structure ActualTargetConsumerSource
    {N : WorldRelationNetwork.{u}}
    (C : ActualCommunicationNetwork N) : Type (u + 1) where
  EventAt : (support : N.Support) → C.Observation support → Type u
  emit : (support : N.Support) → (observation : C.Observation support) →
    EventAt support observation
  EffectAt : N.Support → Type u
  effectFromObservation : (support : N.Support) →
    C.Observation support → EffectAt support
  openEntryAt :
    {support : N.Support} → {observation : C.Observation support} →
      EventAt support observation →
      (Sigma fun responsibility : N.Responsibility =>
        N.OpenAt support responsibility)

/-- Fixed source algebra for pair transport.  Payload generation, target
consumption, and cut obstruction compilation are three source-native event
families.  An exact cut never stores an independently chosen obstruction. -/
structure ActualOperationalSeparationSources
    {N : WorldRelationNetwork.{u}}
    (C : ActualCommunicationNetwork N) : Type (u + 1) where
  payloadSource : ActualPayloadSource C
  consumerSource : ActualTargetConsumerSource C
  CutEventAt : (source target : N.Support) → Type u
  cutSide : {source target : N.Support} → CutEventAt source target →
    N.Support → Bool
  cut_source_side : {source target : N.Support} →
    (event : CutEventAt source target) → cutSide event source = false
  cut_target_side : {source target : N.Support} →
    (event : CutEventAt source target) → cutSide event target = true
  cut_blocks : {source target left right : N.Support} →
    (event : CutEventAt source target) →
    (edge : ActualContactEdgeAt C left right) →
      cutSide event left = false → cutSide event right = true → False
  cutObstruction : {source target : N.Support} →
    CutEventAt source target → N.ObstructionAt source

namespace ActualTargetConsumerSource

variable
  {N : WorldRelationNetwork.{u}}
  {C : ActualCommunicationNetwork N}

def consumerAt
    (consumer : ActualTargetConsumerSource C)
    (support : N.Support) : C.Carrier support → consumer.EffectAt support :=
  fun value => consumer.effectFromObservation support (C.observe support value)

/-- Exact open-responsibility field named by one target-consumer event.

The field is a source readout.  Temporal admission is supplied by the fixed
root compiler's generated causal-entry row. -/
def entryAt
    (consumer : ActualTargetConsumerSource C)
    {support : N.Support} {observation : C.Observation support}
    (event : consumer.EventAt support observation) :
    (Sigma fun responsibility : N.Responsibility =>
      N.OpenAt support responsibility) :=
  consumer.openEntryAt event

/-- The claim acted on by a target-consumer occurrence is the claim already
carried by its exact open ledger row.  A generated effect cannot grant
authority to an independently supplied claim. -/
def claimAt
    (consumer : ActualTargetConsumerSource C)
    {support : N.Support} {observation : C.Observation support}
    (event : consumer.EventAt support observation) : N.Claim :=
  N.openClaimAt (consumer.entryAt event).2

@[simp] theorem claimAt_eq_open_row
    (consumer : ActualTargetConsumerSource C)
    {support : N.Support} {observation : C.Observation support}
    (event : consumer.EventAt support observation) :
    consumer.claimAt event = N.openClaimAt (consumer.entryAt event).2 :=
  rfl

/-- Observer-kernel safety is proved from the exact target consumer's
factorization.  No injectivity or caller-supplied safety certificate enters
the theorem mouth. -/
theorem observer_safe
    (consumer : ActualTargetConsumerSource C)
    (support : N.Support) :
    ConsumerSafe (C.observe support) (consumer.consumerAt support) :=
  ConsumerSafe.of_factorization
    (consumer.effectFromObservation support) (fun _ => rfl)

end ActualTargetConsumerSource

/-- Successful operational delivery.  Once the fixed source algebra and
contact path are fixed, payload, whole-path write-back, observation, consumer
event, and effect have no caller-selectable fields. -/
structure GeneratedDeliveryAt
    {N : WorldRelationNetwork.{u}}
    (C : ActualCommunicationNetwork N)
    (S : ActualOperationalSeparationSources C)
    (source target : N.Support) : Type u where
  path : SourceOwnedTransportPath C source target

namespace GeneratedDeliveryAt

variable
  {N : WorldRelationNetwork.{u}}
  {C : ActualCommunicationNetwork N}
  {S : ActualOperationalSeparationSources C}
  {source target : N.Support}

def sourceEvent (_delivery : GeneratedDeliveryAt C S source target) :
    S.payloadSource.EventAt source :=
  S.payloadSource.emit source

def sourceValue (delivery : GeneratedDeliveryAt C S source target) :
    C.Carrier source :=
  S.payloadSource.payload delivery.sourceEvent

def writeBack (delivery : GeneratedDeliveryAt C S source target) :
    SourceOwnedTransportPath.GeneratedPathWriteBackAt
      delivery.path delivery.sourceValue :=
  delivery.path.generatedWriteBack delivery.sourceValue

def targetValue (delivery : GeneratedDeliveryAt C S source target) :
    C.Carrier target :=
  delivery.writeBack.targetValue

def targetObservation (delivery : GeneratedDeliveryAt C S source target) :
    C.Observation target :=
  C.observe target delivery.targetValue

def consumerEvent (delivery : GeneratedDeliveryAt C S source target) :
    S.consumerSource.EventAt target delivery.targetObservation :=
  S.consumerSource.emit target delivery.targetObservation

def effect (delivery : GeneratedDeliveryAt C S source target) :
    S.consumerSource.EffectAt target :=
  S.consumerSource.effectFromObservation target delivery.targetObservation

theorem targetValue_eq_transport
    (delivery : GeneratedDeliveryAt C S source target) :
    delivery.targetValue = delivery.path.transport delivery.sourceValue :=
  delivery.writeBack.target_eq

theorem effect_eq_generatedObservation
    (delivery : GeneratedDeliveryAt C S source target) :
    delivery.effect =
      S.consumerSource.effectFromObservation target
        delivery.targetObservation :=
  rfl

theorem observer_safe
    (_delivery : GeneratedDeliveryAt C S source target) :
    ConsumerSafe (C.observe target)
      (S.consumerSource.consumerAt target) :=
  S.consumerSource.observer_safe target

end GeneratedDeliveryAt

/-- Exact directed cut recognized from one source-native cut occurrence.
Its partition, blocking law, and U7 obstruction are all projections of that
same occurrence; none is a field of this public receipt. -/
structure ExactContactCutAt
    {N : WorldRelationNetwork.{u}}
    (C : ActualCommunicationNetwork N)
    (S : ActualOperationalSeparationSources C)
    (source target : N.Support) : Type u where
  actualEvent : S.CutEventAt source target

namespace ExactContactCutAt

variable
  {N : WorldRelationNetwork.{u}}
  {C : ActualCommunicationNetwork N}
  {S : ActualOperationalSeparationSources C}
  {source target : N.Support}

def side (cut : ExactContactCutAt C S source target) : N.Support → Bool :=
  S.cutSide cut.actualEvent

theorem source_side (cut : ExactContactCutAt C S source target) :
    cut.side source = false :=
  S.cut_source_side cut.actualEvent

theorem target_side (cut : ExactContactCutAt C S source target) :
    cut.side target = true :=
  S.cut_target_side cut.actualEvent

def obstruction (cut : ExactContactCutAt C S source target) :
    N.ObstructionAt source :=
  S.cutObstruction cut.actualEvent

theorem blocks
    (cut : ExactContactCutAt C S source target)
    {left right : N.Support}
    (edge : ActualContactEdgeAt C left right)
    (left_side : cut.side left = false)
    (right_side : cut.side right = true) : False :=
  S.cut_blocks cut.actualEvent edge left_side right_side

theorem side_eq_false_of_path
    (cut : ExactContactCutAt C S source target)
    {left right : N.Support}
    (path : SourceOwnedTransportPath C left right)
    (left_side : cut.side left = false) :
    cut.side right = false := by
  induction path with
  | nil => exact left_side
  | @cons pathSource middle pathTarget edge tail inductionHypothesis =>
      have middle_side : cut.side middle = false := by
        cases middle_eq : cut.side middle with
        | false => rfl
        | true => exact False.elim (cut.blocks edge left_side middle_eq)
      exact inductionHypothesis middle_side

/-- A generated path cannot cross an exact cut. -/
theorem noPath (cut : ExactContactCutAt C S source target) :
    IsEmpty (SourceOwnedTransportPath C source target) :=
  ⟨fun path => by
    have target_false := cut.side_eq_false_of_path path cut.source_side
    rw [cut.target_side] at target_false
    cases target_false⟩

end ExactContactCutAt

/-- Raw exact-cut evolution syntax used by one operational-search emission.

This wrapper is intentionally not U7 authority: a caller can construct an
exact cut without proving that it was emitted for an admitted query after a
generated search history.  `GeneratedOperationalObstructionAt` below seals
that chronology, but world authority is granted only by its fixed-root
recognition. -/
structure GeneratedCutEvolutionAt
    {N : WorldRelationNetwork.{u}}
    {U7 : U7ProducerCalculus N}
    (C : ActualCommunicationNetwork N)
    (S : ActualOperationalSeparationSources C)
    (calculus : U7ObstructionEvolutionCalculus N U7)
    (source target : N.Support) : Type u where
  cut : ExactContactCutAt C S source target

/-- A completed delivery path and an exact cut at the same endpoints cannot
both be generated. -/
theorem GeneratedDeliveryAt.excludesCut
    {N : WorldRelationNetwork.{u}}
    {U7 : U7ProducerCalculus N}
    {C : ActualCommunicationNetwork N}
    {S : ActualOperationalSeparationSources C}
    {calculus : U7ObstructionEvolutionCalculus N U7}
    {source target : N.Support}
    (delivery : GeneratedDeliveryAt C S source target)
    (cutEvolution : GeneratedCutEvolutionAt C S calculus source target) :
    False :=
  cutEvolution.cut.noPath.false delivery.path

/-- Search current generated from one admitted pair query.  It stores only the
path prefix that has already occurred; the target is an index, not a terminal
witness. -/
structure OperationalSearchCurrentAt
    {N : WorldRelationNetwork.{u}}
    (C : ActualCommunicationNetwork N)
    (source target : N.Support) : Type u where
  frontier : N.Support
  path : SourceOwnedTransportPath C source frontier

def OperationalSearchCurrentAt.initial
    {N : WorldRelationNetwork.{u}}
    (C : ActualCommunicationNetwork N)
    (source target : N.Support) :
    OperationalSearchCurrentAt C source target :=
  ⟨source, .nil source⟩

@[simp] theorem OperationalSearchCurrentAt.initial_path_length
    {N : WorldRelationNetwork.{u}}
    (C : ActualCommunicationNetwork N)
    (source target : N.Support) :
    (OperationalSearchCurrentAt.initial C source target).path.length = 0 :=
  rfl

/-- One actual search continuation.  Its next current is generated by
appending exactly one actual contact event to the existing prefix. -/
structure ActualOperationalSearchContinuationAt
    {N : WorldRelationNetwork.{u}}
    (C : ActualCommunicationNetwork N)
    {source target : N.Support}
    (current : OperationalSearchCurrentAt C source target) : Type u where
  nextSupport : N.Support
  edge : ActualContactEdgeAt C current.frontier nextSupport

def ActualOperationalSearchContinuationAt.next
    {N : WorldRelationNetwork.{u}}
    {C : ActualCommunicationNetwork N}
    {source target : N.Support}
    {current : OperationalSearchCurrentAt C source target}
    (continuation : ActualOperationalSearchContinuationAt C current) :
    OperationalSearchCurrentAt C source target :=
  ⟨continuation.nextSupport, current.path.snoc continuation.edge⟩

/-- Canonical progress debit of one search continuation.  The debit is the
same contact occurrence that extends the path, and its generated prefix is
strictly longer. -/
structure ActualOperationalSearchProgressDebitAt
    {N : WorldRelationNetwork.{u}}
    {C : ActualCommunicationNetwork N}
    {source target : N.Support}
    {current : OperationalSearchCurrentAt C source target}
    (continuation : ActualOperationalSearchContinuationAt C current) :
    Type u where
  private mk ::
  actualEvent : C.Event
  actualEvent_eq : actualEvent = continuation.edge.actualEvent
  source_eq : C.sourceSupport actualEvent = current.frontier
  target_eq : C.targetSupport actualEvent = continuation.nextSupport
  path_length_strict : current.path.length < continuation.next.path.length

def ActualOperationalSearchContinuationAt.progressDebit
    {N : WorldRelationNetwork.{u}}
    {C : ActualCommunicationNetwork N}
    {source target : N.Support}
    {current : OperationalSearchCurrentAt C source target}
    (continuation : ActualOperationalSearchContinuationAt C current) :
    ActualOperationalSearchProgressDebitAt continuation where
  actualEvent := continuation.edge.actualEvent
  actualEvent_eq := rfl
  source_eq := continuation.edge.source_eq
  target_eq := continuation.edge.target_eq
  path_length_strict := by
    change current.path.length <
      (current.path.snoc continuation.edge).length
    rw [SourceOwnedTransportPath.length_snoc]
    exact Nat.lt_succ_self _

/-- One source-native search event at the current frontier.  `reached` must
prove that the already generated frontier is the target; `cut` carries an
actual obstruction event at the current frontier; `continued` pays one
actual contact event and generates the next prefix. -/
inductive ActualOperationalSearchEventAt
    {N : WorldRelationNetwork.{u}}
    (C : ActualCommunicationNetwork N)
    (S : ActualOperationalSeparationSources C)
    {source target : N.Support}
    (current : OperationalSearchCurrentAt C source target) : Type u
  | reached (target_eq : current.frontier = target)
  | cut (event : S.CutEventAt current.frontier target)
  | continued
      (continuation : ActualOperationalSearchContinuationAt C current)

/-- One generated living-law search evolution.  There is no `unknown`: a
nonterminal search must extend its actual path, while a cut immediately emits
the existing canonical U7 obstruction evolution. -/
inductive OperationalSearchEvolutionAt
    {N : WorldRelationNetwork.{u}}
    {U7 : U7ProducerCalculus N}
    (C : ActualCommunicationNetwork N)
    (S : ActualOperationalSeparationSources C)
    (calculus : U7ObstructionEvolutionCalculus N U7)
    {source target : N.Support}
    (current : OperationalSearchCurrentAt C source target) : Type u
  | delivered (delivery : GeneratedDeliveryAt C S source target)
  | obstructed
      (cutEvolution : GeneratedCutEvolutionAt C S calculus
        current.frontier target)
  | continued
      (continuation : ActualOperationalSearchContinuationAt C current)

def ActualOperationalSearchEventAt.toEvolution
    {N : WorldRelationNetwork.{u}}
    {U7 : U7ProducerCalculus N}
    {C : ActualCommunicationNetwork N}
    {S : ActualOperationalSeparationSources C}
    {calculus : U7ObstructionEvolutionCalculus N U7}
    {source target : N.Support}
    {current : OperationalSearchCurrentAt C source target} :
    ActualOperationalSearchEventAt C S current →
      OperationalSearchEvolutionAt C S calculus current
  | .reached target_eq =>
      .delivered ⟨target_eq ▸ current.path⟩
  | .cut event => .obstructed ⟨⟨event⟩⟩
  | .continued continuation => .continued continuation

/-- Source-owned actual pair-query process.  Admission emits only a query
identity.  Every search event is generated at the exact current prefix; no
field can submit a completed path or cut at query admission. -/
structure ActualOperationalSearchProcess
    {N : WorldRelationNetwork.{u}}
    {U7 : U7ProducerCalculus N}
    (C : ActualCommunicationNetwork N)
    (S : ActualOperationalSeparationSources C)
    (calculus : U7ObstructionEvolutionCalculus N U7) : Type (u + 1) where
  QueryEventAt : (source target : N.Support) → Type u
  admit : (source target : N.Support) → QueryEventAt source target
  emit : {source target : N.Support} →
    QueryEventAt source target →
    (current : OperationalSearchCurrentAt C source target) →
      ActualOperationalSearchEventAt C S current

namespace ActualOperationalSearchProcess

variable
  {N : WorldRelationNetwork.{u}}
  {U7 : U7ProducerCalculus N}
  {C : ActualCommunicationNetwork N}
  {S : ActualOperationalSeparationSources C}
  {calculus : U7ObstructionEvolutionCalculus N U7}

def initial
    (process : ActualOperationalSearchProcess C S calculus)
    {source target : N.Support}
    (_query : process.QueryEventAt source target) :
    OperationalSearchCurrentAt C source target :=
  OperationalSearchCurrentAt.initial C source target

def generated
    (process : ActualOperationalSearchProcess C S calculus)
    {source target : N.Support}
    (query : process.QueryEventAt source target)
    (current : OperationalSearchCurrentAt C source target) :
    OperationalSearchEvolutionAt C S calculus current :=
  (process.emit query current).toEvolution

end ActualOperationalSearchProcess

/-- Finite prefix generated by one exact admitted query and repeated calls to
the same source-native process.  The only successor constructor requires that
the process actually emitted the continuation being appended. -/
inductive GeneratedOperationalSearchPrefixAt
    {N : WorldRelationNetwork.{u}}
    {U7 : U7ProducerCalculus N}
    {C : ActualCommunicationNetwork N}
    {S : ActualOperationalSeparationSources C}
    {calculus : U7ObstructionEvolutionCalculus N U7}
    (process : ActualOperationalSearchProcess C S calculus)
    {source target : N.Support}
    (query : process.QueryEventAt source target) :
    (current : OperationalSearchCurrentAt C source target) → Nat → Type u
  | initial : GeneratedOperationalSearchPrefixAt process query
      (process.initial query) 0
  | continued {current : OperationalSearchCurrentAt C source target}
      {steps : Nat}
      (history : GeneratedOperationalSearchPrefixAt process query current steps)
      (continuation : ActualOperationalSearchContinuationAt C current)
      (emitted_eq : process.emit query current = .continued continuation) :
      GeneratedOperationalSearchPrefixAt process query continuation.next
        (steps + 1)

/-- One continuation certified as the exact next emission of the same
admitted query and the same generated prefix.  A bare contact edge is not a
generated search step: the process emission equality is part of this carrier.
World authority is added only by the fixed-root operational recognition. -/
structure GeneratedOperationalSearchContinuationAt
    {N : WorldRelationNetwork.{u}}
    {U7 : U7ProducerCalculus N}
    {C : ActualCommunicationNetwork N}
    {S : ActualOperationalSeparationSources C}
    {calculus : U7ObstructionEvolutionCalculus N U7}
    (process : ActualOperationalSearchProcess C S calculus)
    {source target : N.Support}
    (query : process.QueryEventAt source target)
    {current : OperationalSearchCurrentAt C source target}
    (steps : Nat) : Type u where
  history : GeneratedOperationalSearchPrefixAt process query current steps
  continuation : ActualOperationalSearchContinuationAt C current
  emitted_eq : process.emit query current = .continued continuation

/-- Extend the generated history by the exact process-emitted continuation. -/
def GeneratedOperationalSearchContinuationAt.nextHistory
    {N : WorldRelationNetwork.{u}}
    {U7 : U7ProducerCalculus N}
    {C : ActualCommunicationNetwork N}
    {S : ActualOperationalSeparationSources C}
    {calculus : U7ObstructionEvolutionCalculus N U7}
    {process : ActualOperationalSearchProcess C S calculus}
    {source target : N.Support}
    {query : process.QueryEventAt source target}
    {current : OperationalSearchCurrentAt C source target}
    {steps : Nat}
    (generated :
      GeneratedOperationalSearchContinuationAt
        (current := current) process query steps) :
    GeneratedOperationalSearchPrefixAt process query
      generated.continuation.next (steps + 1) :=
  .continued generated.history generated.continuation generated.emitted_eq

namespace GeneratedOperationalSearchPrefixAt

variable
  {N : WorldRelationNetwork.{u}}
  {U7 : U7ProducerCalculus N}
  {C : ActualCommunicationNetwork N}
  {S : ActualOperationalSeparationSources C}
  {calculus : U7ObstructionEvolutionCalculus N U7}
  {process : ActualOperationalSearchProcess C S calculus}
  {source target : N.Support}
  {query : process.QueryEventAt source target}
  {current : OperationalSearchCurrentAt C source target}
  {steps : Nat}

theorem path_length_eq
    (history : GeneratedOperationalSearchPrefixAt process query current steps) :
    current.path.length = steps := by
  induction history with
  | initial => rfl
  | @continued previous steps history continuation emitted_eq
      inductionHypothesis =>
      change (previous.path.snoc continuation.edge).length = _
      rw [SourceOwnedTransportPath.length_snoc]
      rw [inductionHypothesis]

end GeneratedOperationalSearchPrefixAt

/-- A completed delivery is certified only after a generated finite prefix
reaches the target and the same process emits `reached` at that exact current.
The terminal path is derived from the prefix; it is not a query-source field. -/
structure GeneratedOperationalDeliveryAt
    {N : WorldRelationNetwork.{u}}
    {U7 : U7ProducerCalculus N}
    {C : ActualCommunicationNetwork N}
    {S : ActualOperationalSeparationSources C}
    {calculus : U7ObstructionEvolutionCalculus N U7}
    (process : ActualOperationalSearchProcess C S calculus)
    {source target : N.Support}
    (query : process.QueryEventAt source target) : Type u where
  steps : Nat
  current : OperationalSearchCurrentAt C source target
  history : GeneratedOperationalSearchPrefixAt process query current steps
  target_eq : current.frontier = target
  emitted_eq : process.emit query current = .reached target_eq

def GeneratedOperationalDeliveryAt.delivery
    {N : WorldRelationNetwork.{u}}
    {U7 : U7ProducerCalculus N}
    {C : ActualCommunicationNetwork N}
    {S : ActualOperationalSeparationSources C}
    {calculus : U7ObstructionEvolutionCalculus N U7}
    {process : ActualOperationalSearchProcess C S calculus}
    {source target : N.Support}
    {query : process.QueryEventAt source target}
    (generated : GeneratedOperationalDeliveryAt process query) :
    GeneratedDeliveryAt C S source target :=
  ⟨generated.target_eq ▸ generated.current.path⟩

/-- A generated frontier cut is likewise tied to the exact admitted query,
generated prefix, and process emission.  It produces U7 at the current
frontier; it is not misreported as a global completed-path witness. -/
structure GeneratedOperationalObstructionAt
    {N : WorldRelationNetwork.{u}}
    {U7 : U7ProducerCalculus N}
    {C : ActualCommunicationNetwork N}
    {S : ActualOperationalSeparationSources C}
    {calculus : U7ObstructionEvolutionCalculus N U7}
    (process : ActualOperationalSearchProcess C S calculus)
    {source target : N.Support}
    (query : process.QueryEventAt source target) : Type u where
  steps : Nat
  current : OperationalSearchCurrentAt C source target
  history : GeneratedOperationalSearchPrefixAt process query current steps
  cutEvent : S.CutEventAt current.frontier target
  emitted_eq : process.emit query current = .cut cutEvent

def GeneratedOperationalObstructionAt.cutEvolution
    {N : WorldRelationNetwork.{u}}
    {U7 : U7ProducerCalculus N}
    {C : ActualCommunicationNetwork N}
    {S : ActualOperationalSeparationSources C}
    {calculus : U7ObstructionEvolutionCalculus N U7}
    {process : ActualOperationalSearchProcess C S calculus}
    {source target : N.Support}
    {query : process.QueryEventAt source target}
    (generated : GeneratedOperationalObstructionAt process query) :
    GeneratedCutEvolutionAt C S calculus generated.current.frontier target :=
  ⟨⟨generated.cutEvent⟩⟩

end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
