import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InterfaceQuorum
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationObservation

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StagePaymentQuorum
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev Subject := StageBudget.Ballot (code := code) × Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument)

-- Both classifiers read the same request position of the same actual stage.
def resolveAt (row : StageTrace.Record (code := code)) (scope : Scope) : Option (Subject (code := code)) :=
  match StageBudget.issued vocabulary row scope.instanceId,
    Settlement.issuedAt code.law row.before.current row.submitted scope.instanceId with
  | some ballot, some payment => if ballot.scope = scope ∧ payment.scope = scope then some (ballot,payment) else none
  | _,_ => none

theorem at_has_both_original_origins (row : StageTrace.Record (code := code)) (scope : Scope)
    (subject : Subject (code := code)) (made : resolveAt vocabulary row scope = some subject) :
    StageBudget.issued vocabulary row scope.instanceId = some subject.1 ∧
      Settlement.issuedAt code.law row.before.current row.submitted scope.instanceId = some subject.2 ∧
      subject.1.scope = scope ∧ subject.2.scope = scope := by
  unfold resolveAt at made
  split at made <;> try contradiction
  rename_i ballot payment one two
  split at made <;> try contradiction
  rename_i aligned
  cases Option.some.inj made
  exact ⟨one,two,aligned⟩

def resolveRows (rows : List (StageTrace.Record (code := code))) (scope : Scope) : Option (Subject (code := code)) :=
  (rows.find? fun row => (resolveAt vocabulary row scope).isSome).bind fun row => resolveAt vocabulary row scope

abbrev resolve (start : Cursor code) (stages : List (EventHistory.Stage (code := code))) :=
  resolveRows vocabulary (StageTrace.records start stages)

theorem resolved_has_an_actual_paid_stage (start : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (scope : Scope) (subject : Subject (code := code)) (made : resolve vocabulary start stages scope = some subject) :
    ∃ row ∈ StageTrace.records start stages,
      StageBudget.issued vocabulary row scope.instanceId = some subject.1 ∧
      Settlement.issuedAt code.law row.before.current row.submitted scope.instanceId = some subject.2 ∧
      subject.1.scope = scope ∧ subject.2.scope = scope := by
  unfold resolve resolveRows at made
  cases found : (StageTrace.records start stages).find? (fun row => (resolveAt vocabulary row scope).isSome) with
  | none => simp [found] at made
  | some row =>
    simp only [found,Option.bind_some] at made
    exact ⟨row,List.mem_of_find?_eq_some found,at_has_both_original_origins vocabulary row scope subject made⟩

theorem at_equal {left right : StageTrace.Record (code := code)} (same : CommunicationObservation.Same left right) (scope : Scope) :
    resolveAt vocabulary left scope = resolveAt vocabulary right scope := by
  have issued : StageBudget.issued vocabulary left scope.instanceId = StageBudget.issued vocabulary right scope.instanceId := by
    simp only [StageBudget.issued,StageBudget.outcome,same.activation,CommunicationObservation.items_equal same,
      OwnedAttestation.classify,same.cut]
  simp only [resolveAt,issued,same.before,same.submitted]

theorem resolve_equal {left right : List (StageTrace.Record (code := code))}
    (same : CommunicationObservation.Related left right) (scope : Scope) :
    resolveRows vocabulary left scope = resolveRows vocabulary right scope := by
  induction same with
  | nil => rfl
  | @cons a b left right head tail ih =>
    simp only [resolveRows,List.find?_cons,at_equal vocabulary head scope]
    split
    · simpa only [Option.bind_some] using at_equal vocabulary head scope
    · exact ih

variable (start : Cursor code) (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)

def received (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites)
    (scope : Scope) (subject : Subject (code := code)) : StageReception.Receiver (code := code) :=
  let actual := StageReception.run vocabulary encoding law start stages receiver stages.length
  ⟨actual.receipts.filter (fun receipt => decide (receipt.wire.ballot.scope = scope ∧
    (subject.1.cut < receipt.wire.ballot.cut ∨
     subject.1.cut = receipt.wire.ballot.cut ∧ subject.1.position ≤ receipt.wire.ballot.position))),actual.audit⟩

abbrev Result := SubjectQuorum.ResultData (Subject (code := code))

def produce (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites)
    (scope : Scope) (threshold : Nat) : Result (code := code) :=
  if ¬ code.sites + InterfaceDeviationEnvelope.budget start.source vocabulary scope < threshold+threshold then .blocked .unsafeBudget
  else match resolve vocabulary start stages scope with
    | none => .blocked .missingSourceSubject
    | some subject => match StageQuorum.readout (received vocabulary start encoding law stages receiver scope subject) scope threshold with
      | .blocked => .blocked .missingQuorum
      | .decided value => .decided value subject

theorem decided_has_actual_subject_and_quorum (stages : List (EventHistory.Stage (code := code)))
    (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) (value : Bool) (subject : Subject (code := code))
    (done : produce vocabulary start encoding law stages receiver scope threshold = .decided value subject) :
    code.sites + InterfaceDeviationEnvelope.budget start.source vocabulary scope < threshold+threshold ∧
      resolve vocabulary start stages scope = some subject ∧
      StageQuorum.readout (received vocabulary start encoding law stages receiver scope subject) scope threshold = .decided value := by
  unfold produce at done
  split at done <;> try contradiction
  rename_i safe
  split at done <;> try contradiction
  rename_i generated original
  split at done <;> try contradiction
  rename_i choice quorum
  cases done
  exact ⟨of_not_not safe,original,quorum⟩

theorem every_decision_consumes_actual_payment_effects (stages : List (EventHistory.Stage (code := code)))
    (receiver : Fin code.sites) (scope : Scope) (threshold : Nat) (value : Bool) (subject : Subject (code := code))
    (done : produce vocabulary start encoding law stages receiver scope threshold = .decided value subject) :
    ∃ row ∈ StageTrace.records start stages, ∃ item ∈ StageTrace.items row,
      code.law.Valid item.before item.request ∧ 0 < subject.2.amount ∧
      flowAt (code.law.actualDebit item.before item.request) subject.2.debtor subject.2.unit = subject.2.amount ∧
      flowAt (code.law.actualCredit item.before item.request) subject.2.creditor subject.2.unit = subject.2.amount ∧
      (code.law.step item.before item.request).claims subject.2.instrument subject.2.debtor subject.2.creditor =
        subject.2.priorClaim-subject.2.quantity := by
  obtain ⟨row,inside,_,original,_⟩ := resolved_has_an_actual_paid_stage vocabulary start stages scope subject
    (decided_has_actual_subject_and_quorum vocabulary start encoding law stages receiver scope threshold value subject done).2.1
  obtain ⟨item,located,valid,positive,_,debit,credit,claims⟩ := Settlement.issued_payment_has_actual_material_and_claim_effects
    code.law row.before.current row.submitted scope.instanceId subject.2 original
  exact ⟨row,inside,item,List.mem_of_getElem? located,valid,positive,debit,credit,claims⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StagePaymentQuorum
