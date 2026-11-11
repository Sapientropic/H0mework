import H0mework.Foundation.Inquiry.Protocol

/-!
# Focused U7 obstruction-lineage evolution regression

The fixture locks three dispositions on one shared world support:

* a source-backed theory-audit demand;
* a paid redirect whose successor has the same world claim;
* a terminal settlement.

Every step is the canonical image of the exact generated U7 demand and is
reflected in the existing dependent responsibility run.  The lookalike
negative proves that the redirected successor state is not the one-event
state obtained by admitting that successor as a fresh root: the old admission
and supersession remain in its history.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ObstructionLineageEvolutionRegression

universe u

inductive TestObstruction
  | audit
  | redirected
  | settled
  deriving DecidableEq

inductive TestClaim
  | old
  | revised
  deriving DecidableEq

abbrev network : WorldRelationNetwork where
  Support := Unit
  Anchor := Unit
  Incidence := Unit
  Lineage := Bool
  Responsibility := Bool
  Claim := TestClaim
  anchorAt := fun _ => ()
  incidenceAt := fun _ => ()
  lineageAt := fun _ => false
  OpenAt := fun _ _ => Unit
  openClaimAt := fun _ => .old
  openProgressBudgetAt := by
    intro _support responsibility _open
    exact match responsibility with
      | false => 1
      | true => 0
  HoldsAt := fun _ _ => Unit
  ObstructionAt := fun _ => TestObstruction
  obstructionClaim := fun obstruction =>
    match obstruction with
    | .audit => .old
    | .redirected | .settled => .revised
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := fun _ _ => Unit

abbrev N := network

structure TestDemand (obstruction : TestObstruction) where
  value : TestObstruction
  value_eq : value = obstruction

abbrev U7 : U7ProducerCalculus N where
  DemandAt := TestDemand
  generateDemand := fun obstruction => ⟨obstruction, rfl⟩

abbrev TestEvent
    {support : N.Support} (obstruction : N.ObstructionAt support)
    (demand : U7.DemandAt obstruction) :=
  SourceGeneratedU7DemandAt U7 obstruction demand

def demandResponsibility : TestObstruction → Bool
  | .audit | .redirected => false
  | .settled => true

abbrev actualSource : U7ActualSuccessorSource N U7 where
  EventAt := TestEvent
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := fun event => event
  demandEntryAt := by
    intro support obstruction _demand _event
    cases support
    exact ⟨demandResponsibility obstruction, ()⟩

def redirectedTransition :
    U7RedirectContinuationAt N (support := ()) .redirected .settled :=
  ⟨(), rfl⟩

abbrev calculus : U7ObstructionEvolutionCalculus N U7 where
  source := actualSource
  compile := by
    intro support obstruction demand event
    cases support
    cases event
    cases obstruction with
    | audit =>
        exact
          { disposition := .requiresTheoryAudit ()
            demandEntryDisposition := PUnit.unit }
    | redirected =>
        exact
          { disposition := .redirected redirectedTransition
            demandEntryDisposition :=
              ⟨ConstructiveRoot.LedgerEntryEvolutionAt.transferred ()
                  rfl rfl (by decide), rfl⟩ }
    | settled =>
        exact
          { disposition := .settled ()
            demandEntryDisposition := ⟨⟨()⟩, rfl⟩ }

/-- error: Unknown identifier `U6SuccessorAccountAt` -/
#guard_msgs in
#check U6SuccessorAccountAt

/-- Theory audit is an exact U8 handoff, not a renewable U7 step. -/
theorem theory_audit_has_no_u7_successor_prefix :
    calculus.generatedPrefix? (support := ()) TestObstruction.audit 1 =
      (none : Option
        (GeneratedU7Prefix (support := ()) calculus
          TestObstruction.audit 1)) :=
  rfl

def generatedPrefix :
    GeneratedU7Prefix (support := ()) calculus .redirected 1 :=
  (calculus.generatedPrefix? TestObstruction.redirected 1).get (by rfl)

theorem settled_prefix_cannot_claim_one_more_step :
    calculus.generatedPrefix? (support := ()) TestObstruction.settled 1 =
      (none : Option
        (GeneratedU7Prefix (support := ()) calculus TestObstruction.settled 1)) :=
  rfl

/--
error: Unknown identifier `GeneratedU7PrefixSeal.token`
-/
#guard_msgs in
#check GeneratedU7PrefixSeal.token

theorem generated_prefix_keeps_all_obstruction_claims :
    generatedPrefix.claimTrace =
      [TestClaim.revised, TestClaim.revised] :=
  rfl

theorem generated_prefix_length_is_exact :
    generatedPrefix.claimTrace.length = 2 := by
  simpa using generatedPrefix.claimTrace_length

/-- An actual U7 event cannot pay with an arbitrary inhabitant of the demand
vocabulary: its dependent payload is the compiler image of the exact
obstruction. -/
theorem actual_event_demand_is_compiler_image
    {support : N.Support}
    {obstruction : N.ObstructionAt support}
    {demand : U7.DemandAt obstruction}
    (event : actualSource.EventAt obstruction demand) :
    demand = U7.generateDemand obstruction :=
  (actualSource.demandAuthority event).payload_eq_generated

/-- The actual U7 event pays the exact source-selected open row. -/
theorem actual_event_entry_is_source_fixed
    {support : N.Support}
    {obstruction : N.ObstructionAt support}
    {demand : U7.DemandAt obstruction}
    (event : actualSource.EventAt obstruction demand) :
    U7ActualSuccessorSource.demandEntry event =
      ⟨demandResponsibility obstruction, ()⟩ := by
  cases support
  rfl

/-- A sibling responsibility value cannot borrow the event's open row. -/
theorem actual_event_cannot_name_sibling_row
    {demand : U7.DemandAt (support := ()) .redirected}
    (event : actualSource.EventAt .redirected demand) :
    (U7ActualSuccessorSource.demandEntry event).1 ≠ true := by
  rw [actual_event_entry_is_source_fixed event]
  intro h
  cases h

/-- The redirected obstruction is an inquiry answer only because the exact
successor demand row spends the live budget from `1` to `0`. -/
def paid_redirect_has_inquiry_answer_authority :
    ConstructiveRoot.RootInquiryCompletion.SourceNativeU7AnswersAt
      calculus (support := ()) .redirected :=
  ULift.up (PLift.up (by decide))

def paid_redirect_is_u7_answer :
    ConstructiveRoot.RootInquiryCompletion.SourceNativeInquiryAuditAt
      U7 calculus (TheoryState.rootSemantic N) (support := ()) .redirected :=
  .u7Answered paid_redirect_has_inquiry_answer_authority

/- The legacy empty-ledger presentation no longer exports an authority mouth. -/
theorem parallel_empty_ledger_u7_lifecycle_is_not_public : True := by
  fail_if_success exact U7ObstructionLifecycle.lifecycleProcess
  fail_if_success exact U7ObstructionLifecycle.admissionEdge
  fail_if_success exact U7ObstructionLifecycle.demandEvolutionRun
  trivial

theorem settled_obstruction_has_typed_terminal_disposition :
    (calculus.generated (support := ()) .settled).2.disposition =
      (.settled () : U7ObstructionDispositionAt N U7 .settled
        (U7.generateDemand (support := ()) .settled)) :=
  rfl

#print axioms paid_redirect_has_inquiry_answer_authority
#print axioms paid_redirect_is_u7_answer

end ObstructionLineageEvolutionRegression
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
