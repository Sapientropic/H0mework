import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Payment.Face

set_option autoImplicit false

open private sameSupportLedger sameSupportLedger_heq sameSupportLedger_rows from
  H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted.Ledger

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Payment

open Capitalism.Universal.Root Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Conflict.Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)
  (repair : Request Party Good Port Technology Instrument)
  (paid : Conflict.Root.Paid source (attack ++ [repair]))

abbrev target := root claim repair paid
abbrev initial := (target claim repair paid).toAuthoritativeRoot.toRoot.initialVisit
abbrev first := Accounting.Root.Compiler.successor (flow claim repair paid) none

theorem initial_is_the_same_filed_support :
    (target claim repair paid).toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt (initial claim repair paid).current =
      (filedRoot claim repair).toAuthoritativeRoot.toLedgerRoot.toRoot.supportAt (filedVisit claim).current := by
  have aligned : (filedVisit claim).current = Birth.next claim .pending :=
    Accounting.Root.Compiler.successor_current (Birth.flow claim) .pending
  change support claim repair paid none = Birth.support claim (filedVisit claim).current
  rw [aligned]
  exact payment_starts_at_the_already_filed_support claim repair paid

private def occurrencePresentation : ConstructivePresentation
    ((filedRoot claim repair).toAuthoritativeRoot.toRoot.actual.OccurrenceAt (filedVisit claim).current)
    ((target claim repair paid).toAuthoritativeRoot.toRoot.actual.OccurrenceAt (initial claim repair paid).current) where
  forward := fun _ => (target claim repair paid).emitted (initial claim repair paid).current
  backward := fun _ => (filedRoot claim repair).emitted (filedVisit claim).current
  backward_forward := fun event => (Accounting.Root.Compiler.occurrence_eq_emitted (Birth.flow claim) event).symm
  forward_backward := fun event => (Accounting.Root.Compiler.occurrence_eq_emitted (flow claim repair paid) event).symm

set_option maxHeartbeats 1000000 in
def action (event : ExactTemporalCausalRootEventAt
    (filedRoot claim repair).toAuthoritativeRoot.toLedgerRoot (filedVisit claim)) :
    SourceNativeSequentialActualActionTargetAt (filedRoot claim repair) (filedVisit claim) event
      (filedOwner claim) (filedAuthority claim repair) := by
  rw [event.eq_generated]
  let same := initial_is_the_same_filed_support claim repair paid
  let ledger := sameSupportLedger same
  exact {
    TargetN := Birth.N claim
    translation := Financial.Installation.Ingress.identityTranslation (Birth.N claim)
    TargetV := Accounting.Root.Compiler.V (flow claim repair paid)
    targetRoot := target claim repair paid
    targetTheory := TheoryState.rootSemantic (Birth.N claim)
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id, fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation claim repair paid
    occurrence_commutes := rfl
    initialSupport_heq := heq_of_eq same
    initialOpenLedger := ledger
    initialOpenLedger_heq := sameSupportLedger_heq same
    initialLedger_responsibility_commutes := fun row => ((sameSupportLedger_rows same).1 row).symm
    initialLedger_claim_commutes := fun row => ((sameSupportLedger_rows same).2.1 row).symm
    initialLedger_budget_conservative := fun row => ((sameSupportLedger_rows same).2.2.1 row).le
    initialLedgerNoFresh := fun row => ⟨⟨ledger.backward row, ⟨(sameSupportLedger_rows same).2.2.2 row⟩⟩⟩
    translatedSourceEntryRow := Accounting.Root.Compiler.generatedRow (flow claim repair paid)
      (Accounting.Root.Compiler.initialVisit (flow claim repair paid)) (ledger.forward (filedOwner claim))
    firstSuccessor := first claim repair paid
    canonical_targetNextVisit_eq := Root.Registered.Macro.Ingress.next_is_the_same_generated_successor
      (target claim repair paid) (.finite (initial claim repair paid)) (first claim repair paid)
    Answer := ℚ
    answer := remaining source attack [repair] community key
    Receipt := fun q => ULift.{3,0} (PLift (q = remaining source attack [repair] community key ∧
      Conflict.Root.Paid source (attack ++ [repair])))
    receipt := ⟨⟨rfl, paid⟩⟩ }

def program : SourceNativeSequentialActualActionProgramAt (filedRoot claim repair) (filedVisit claim)
    (filedOwner claim) (filedAuthority claim repair) where
  targetAt := action claim repair paid

def generated := (program claim repair paid).generate
  ((filedRoot claim repair).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (filedVisit claim))

theorem actual_payment_generates_the_same_claim_successor :
    (generated claim repair paid).answer = remaining source attack [repair] community key ∧
    (generated claim repair paid).target.targetAnswerAndNext.nextCurrent =
      ⟨_, (target claim repair paid).toAuthoritativeRoot, (generated claim repair paid).target.targetVisit⟩ :=
  ⟨rfl, (generated claim repair paid).target.targetAnswerAndNext_next_eq⟩

open DebtActivationWorld DebtActivationLedger in
theorem the_next_budget_is_the_same_original_debt_coordinate :
    (debtEntry (N := (frame claim repair).N) (law := Birth.law claim)
      (support claim repair paid (next claim repair none)).1 (stage repair paid)).claim =
        .inr (Birth.law claim).debtClaim ∧
    (debtEntry (N := (frame claim repair).N) (law := Birth.law claim)
      (support claim repair paid (next claim repair none)).1 (stage repair paid)).progressBudget =
        if remaining source attack [repair] community key = 0 then 0 else 1 :=
  ⟨rfl, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Payment
