import H0mework.Foundation.Runtime.OperationalSeparation

/-!
# Operational separation focused regression

The two-support fixture has one directed actual contact, `false → true`.
The forward pair is first admitted with an empty path; the same source-native
process then emits the exact contact continuation and, at the generated next
current, recognizes delivery.  The resulting path generates payload delivery,
dependent trace, whole-carrier write-back, and the target consumer effect.  The
reverse query emits one actual frontier-cut occurrence whose canonical
obstruction immediately enters U7.  The cut cannot coexist with the generated
forward path, while the reverse path is empty.  There is no raw-world
`eventView`, preloaded terminal witness, or caller-supplied result compiler
through which payload or outcome can be replaced.

The numerical bound `1` is read from the generated path.  It is not supplied
as connectivity, expansion, or diameter data.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace OperationalSeparationRegression

/-- Fixed live-row budget for this regression root.  It is source data, not a
phase tag, capacity verdict, or downstream target.  The later M14 consumer
tests this exact budget against an independently generated actual debit run. -/
def rootProgressBudget (_responsibility : Unit) : Nat := 2

abbrev network : WorldRelationNetwork where
  Support := Bool
  Anchor := Unit
  Incidence := Unit
  Lineage := Unit
  Responsibility := Unit
  Claim := Unit
  anchorAt := fun _ => ()
  incidenceAt := fun _ => ()
  lineageAt := fun _ => ()
  OpenAt := fun _ _ => Unit
  openClaimAt := fun _ => ()
  openProgressBudgetAt := rootProgressBudget
  HoldsAt := fun _ _ => Unit
  ObstructionAt := fun _ => Unit
  obstructionClaim := fun _ => ()
  SemanticChangeAt := fun _ _ _ => Unit
  DispositionAt := fun _ _ => Unit

abbrev N := network

structure ContactWitness (_source _target : Unit) : Type where
  token : Unit

inductive ContactEvent
  | forward

abbrev communication : ActualCommunicationNetwork N where
  Carrier := fun _ => Bool
  Observation := fun _ => Bool
  observe := fun _ value => value
  ContactAt := ContactWitness
  IncidenceTransportAt := fun _ _ => Unit
  LineageTransportAt := fun _ _ => Unit
  Event := ContactEvent
  sourceSupport := fun _ => false
  targetSupport := fun _ => true
  contact := fun _ => ⟨()⟩
  incidenceTransport := fun _ => ()
  lineageTransport := fun _ => ()
  carrierTransport := fun _ => ConstructivePresentation.refl Bool

abbrev C := communication

abbrev U7 : U7ProducerCalculus N where
  DemandAt := fun _ => Unit
  generateDemand := fun _ => ()

abbrev u7Source : U7ActualSuccessorSource N U7 where
  EventAt := SourceGeneratedU7DemandAt U7
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := fun event => event
  demandEntryAt := fun _ => ⟨(), ()⟩

/-- The one registered transfer row shared by the U7 face and every rooted
consumer of this fixture.  Keeping it source-owned prevents proof fields from
becoming a second presentation-level outcome. -/
def u7TransferEvolution (support : N.Support) :
    ConstructiveRoot.LedgerEntryEvolutionAt N
      (⟨(), ()⟩ : ConstructiveRoot.OpenResponsibilityAt N support)
      (⟨(), ()⟩ : ConstructiveRoot.OpenResponsibilityAt N support) :=
  .transferred () rfl rfl (Nat.le_refl _)

abbrev u7Calculus : U7ObstructionEvolutionCalculus N U7 where
  source := u7Source
  compile := by
    intro support obstruction demand event
    exact
      { disposition := .redirected ⟨(), rfl⟩
        demandEntryDisposition :=
          ⟨u7TransferEvolution support, rfl⟩ }

abbrev payloadSource : ActualPayloadSource C where
  EventAt := fun _ => Unit
  emit := fun _ => ()
  payload := fun _ => true

abbrev consumerSource : ActualTargetConsumerSource C where
  EventAt := fun _ _ => Unit
  emit := fun _ _ => ()
  EffectAt := fun _ => Bool
  effectFromObservation := fun _ observation => observation
  openEntryAt := fun _ => ⟨(), ()⟩

inductive CutEventAt : Bool → Bool → Type
  | reverse : CutEventAt true false

abbrev sources : ActualOperationalSeparationSources C where
  payloadSource := payloadSource
  consumerSource := consumerSource
  CutEventAt := CutEventAt
  cutSide := fun event => by
    cases event
    exact fun support => !support
  cut_source_side := by
    intro source target event
    cases event
    rfl
  cut_target_side := by
    intro source target event
    cases event
    rfl
  cut_blocks := by
    intro source target left right cutEvent edge left_side right_side
    cases cutEvent
    rcases edge with ⟨event, source_eq, target_eq⟩
    cases event
    cases source_eq
    cases target_eq
    cases left_side
  cutObstruction := by
    intro source target event
    cases event
    exact ()

abbrev S := sources

def forwardEdge : ActualContactEdgeAt C false true :=
  ActualContactEdgeAt.canonical ContactEvent.forward

def forwardPath : SourceOwnedTransportPath C false true :=
  .cons forwardEdge (SourceOwnedTransportPath.nil (C := C) true)

def forwardDelivery : GeneratedDeliveryAt C S false true where
  path := forwardPath

def reverseCut : ExactContactCutAt C S true false :=
  ⟨.reverse⟩

def reverseCutEvolution :
    GeneratedCutEvolutionAt C S u7Calculus true false where
  cut := reverseCut

def searchProcess : ActualOperationalSearchProcess C S u7Calculus where
  QueryEventAt := fun _source _target => Unit
  admit := fun _source _target => ()
  emit := by
    intro source target _query current
    rcases current with ⟨frontier, path⟩
    cases source <;> cases target <;> cases frontier
    · exact .reached rfl
    · exact .cut CutEventAt.reverse
    · exact .continued ⟨true, forwardEdge⟩
    · exact .reached rfl
    · exact (reverseCut.noPath.false path).elim
    · exact .cut CutEventAt.reverse
    · exact (reverseCut.noPath.false path).elim
    · exact .reached rfl

abbrev P := searchProcess

def forwardQuery : P.QueryEventAt false true :=
  P.admit false true

def forwardInitial : OperationalSearchCurrentAt C false true :=
  P.initial forwardQuery

def forwardContinuation :
    ActualOperationalSearchContinuationAt C forwardInitial where
  nextSupport := true
  edge := forwardEdge

def forwardAfterOne : OperationalSearchCurrentAt C false true :=
  forwardContinuation.next

def forwardHistory0 :
    GeneratedOperationalSearchPrefixAt P forwardQuery forwardInitial 0 :=
  .initial

def forwardHistory1 :
    GeneratedOperationalSearchPrefixAt P forwardQuery forwardAfterOne 1 :=
  .continued forwardHistory0 forwardContinuation rfl

def generatedForwardDelivery :
    GeneratedOperationalDeliveryAt P forwardQuery where
  steps := 1
  current := forwardAfterOne
  history := forwardHistory1
  target_eq := rfl
  emitted_eq := rfl

theorem query_admission_starts_with_empty_path :
    forwardInitial.path.length = 0 :=
  rfl

theorem forward_query_first_generates_actual_continuation :
    P.generated forwardQuery forwardInitial =
      OperationalSearchEvolutionAt.continued forwardContinuation :=
  rfl

theorem forward_query_then_generates_delivery :
    P.generated forwardQuery forwardAfterOne =
      OperationalSearchEvolutionAt.delivered forwardDelivery :=
  rfl

theorem generated_delivery_is_derived_from_history :
    generatedForwardDelivery.delivery = forwardDelivery :=
  rfl

theorem forward_history_length_is_generated :
    forwardAfterOne.path.length = 1 :=
  forwardHistory1.path_length_eq

theorem forward_continuation_pays_exact_actual_event :
    forwardContinuation.progressDebit.actualEvent = ContactEvent.forward :=
  rfl

theorem forward_continuation_is_strict_progress :
    forwardInitial.path.length < forwardAfterOne.path.length :=
  forwardContinuation.progressDebit.path_length_strict

def reverseQuery : P.QueryEventAt true false :=
  P.admit true false

def reverseInitial : OperationalSearchCurrentAt C true false :=
  P.initial reverseQuery

def reverseHistory0 :
    GeneratedOperationalSearchPrefixAt P reverseQuery reverseInitial 0 :=
  .initial

def generatedReverseObstruction :
    GeneratedOperationalObstructionAt P reverseQuery where
  steps := 0
  current := reverseInitial
  history := reverseHistory0
  cutEvent := CutEventAt.reverse
  emitted_eq := rfl

theorem reverse_query_generates_exact_frontier_cut :
    P.generated reverseQuery reverseInitial =
      OperationalSearchEvolutionAt.obstructed reverseCutEvolution :=
  rfl

theorem forward_path_length_is_generated : forwardPath.length = 1 :=
  rfl

theorem forward_delivery_reaches_independent_consumer :
    forwardDelivery.effect = true :=
  rfl

theorem forward_delivery_writeBack_is_generated :
    forwardDelivery.targetValue =
      forwardPath.transport forwardDelivery.sourceValue :=
  forwardDelivery.targetValue_eq_transport

theorem every_forward_writeBack_is_canonical
    (writeBack : SourceOwnedTransportPath.GeneratedPathWriteBackAt
      forwardPath forwardDelivery.sourceValue) :
    writeBack = forwardPath.generatedWriteBack forwardDelivery.sourceValue :=
  writeBack.eq_generated

theorem every_forward_delivery_uses_fixed_source_payload
    (delivery : GeneratedDeliveryAt C S false true) :
    delivery.sourceValue = true :=
  rfl

theorem forward_transport_avoids_observer_kernel
    : ConsumerSafe (C.observe true) (S.consumerSource.consumerAt true) :=
  forwardDelivery.observer_safe

theorem connected_pair_has_no_exact_cut
    (cut : ExactContactCutAt C S false true) : False :=
  cut.noPath.false forwardPath

theorem delivery_and_cut_are_not_alternative_oracles
    (cut : GeneratedCutEvolutionAt C S u7Calculus false true) : False :=
  forwardDelivery.excludesCut cut

theorem reverse_path_is_empty :
    IsEmpty (SourceOwnedTransportPath C true false) :=
  reverseCut.noPath

end OperationalSeparationRegression
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
