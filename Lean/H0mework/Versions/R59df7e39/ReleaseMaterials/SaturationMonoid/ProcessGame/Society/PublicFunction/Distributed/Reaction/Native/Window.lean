import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Synthesis

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Feedback Distributed.Recall.Information.Agency.Protocol

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (start span : Nat)

abbrev finish := start+span+1
abbrev first := Financial.accountAt bound.source.input (start+1)
abbrev last := Financial.accountAt bound.source.input (finish start span)
abbrev terminal := bound.source.currentAt (finish start span)

def migration (index : Fin (first bound start).current.slots.length) :=
  Financial.Migration.actual bound.source.input (start+1) span index.val
    ((first bound start).current.slots.get index) (List.getElem?_eq_getElem index.isLt)

def holdings : List (List (ℚ × ℚ)) := List.ofFn fun index : Fin (first bound start).current.slots.length =>
  let actual := migration bound start span index
  bound.source.code.parties.map fun holder =>
    (Financial.slotBalance bound.source.input actual.slot holder,actual.path.receivedBy bound.source.input holder)

theorem holding_is_the_actual_slot_and_receipt
    (index : Fin (first bound start).current.slots.length) (holder : Party) :
    Settlement.holdingAt (holdings bound start span) index.val (bound.source.code.parties.idxOf holder) =
      (Financial.slotBalance bound.source.input (migration bound start span index).slot holder,
        (migration bound start span index).path.receivedBy bound.source.input holder) := by
  have lookup : (holdings bound start span)[index.val]? = some (bound.source.code.parties.map fun holder =>
      (Financial.slotBalance bound.source.input (migration bound start span index).slot holder,
        (migration bound start span index).path.receivedBy bound.source.input holder)) := by
    unfold holdings
    rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using index.isLt)]
    simp only [List.getElem_ofFn]
  unfold Settlement.holdingAt
  rw [lookup]
  simp only [Option.getD_some,List.getElem?_map,List.getElem?_idxOf (bound.source.code.parties_cover holder),Option.map_some]

theorem every_original_holder_has_exact_native_conservation
    (index : Fin (first bound start).current.slots.length) (holder : Party) :
    (Settlement.holdingAt (holdings bound start span) index.val (bound.source.code.parties.idxOf holder)).1 +
      (Settlement.holdingAt (holdings bound start span) index.val (bound.source.code.parties.idxOf holder)).2 =
      Financial.slotBalance bound.source.input ((first bound start).current.slots.get index) holder +
        (migration bound start span index).path.assignedTo bound.source.input holder := by
  rw [holding_is_the_actual_slot_and_receipt]
  exact (migration bound start span index).path.holder_conservation _ holder

def profile : Settlement.Profile Party Good Port (Mandate.State Party Technology) Instrument :=
  ⟨Identity.financeImage bound.source.code bound.source.input (first bound start),
    (Identity.financeImage bound.source.code bound.source.input (last bound start span)).drop (first bound start).current.slots.length,
    Settlement.rights (holdings bound start span),
    bound.source.code.instruments.flatMap fun instrument => bound.source.code.parties.flatMap fun debtor =>
      bound.source.code.parties.map fun creditor => (terminal bound start span).claims instrument debtor creditor -
        Financial.BalanceConservation.ledgerClaims bound.source.input (last bound start span).current instrument debtor creditor,
    (List.finRange bound.source.code.task.slots.length).map (Identity.firstService bound.source start),
    ⟨(terminal bound start span).technology,(terminal bound start span).clock,(terminal bound start span).round⟩⟩

def grants (count : Nat) :=
  ((Authority.recordsAt bound count).filter (fun record => decide (record.1.val < count))).map fun record =>
    Feedback.Authority.Trace.grantImage bound record.1.val (count-1)
      (Authority.traceGrant bound record.1.val (count-1) record.2.admission.grant)

def manifest : Feedback.Authority.Trace.Manifest Party Good Port Technology Instrument where
  worlds := (List.range (finish start span)).map fun ordinal =>
    Identity.occurrenceImage bound.source.code bound.source.input (ProgrammeHistory.visitAt bound.source.input ordinal).current
  originalGrants := ((Authority.recordsAt bound start).filter (fun record => decide (record.1.val < start))).map fun record =>
    (Feedback.Authority.Trace.grantImage bound record.1.val (start-1)
        (Authority.traceGrant bound record.1.val (start-1) record.2.admission.grant),
      Feedback.Authority.Trace.grantImage bound record.1.val (start+span-1)
        (Authority.traceGrant bound record.1.val (start+span-1) record.2.admission.grant))
  originalChallenges := (Authority.challengesAt bound (start+1)).map fun record =>
    (Feedback.Authority.Trace.challengeImage bound.source.code (Authority.programme bound) (Authority.sourceIndex bound) record.1,
      Feedback.Authority.Trace.challengeStateImage bound.source.code (Authority.programme bound) (Authority.sourceIndex bound) record.2.state.current,
      Feedback.Authority.Trace.challengeStateImage bound.source.code (Authority.programme bound) (Authority.sourceIndex bound)
        (Mandate.Challenge.through (Authority.programme bound) (Authority.sourceIndex bound) record.1 (finish start span)).state.current)
  candidateGrants := grants bound (start+span)
  candidateChallenges := (Authority.challengesAt bound (finish start span)).map fun record =>
    (Feedback.Authority.Trace.challengeImage bound.source.code (Authority.programme bound) (Authority.sourceIndex bound) record.1,
      Feedback.Authority.Trace.challengeStateImage bound.source.code (Authority.programme bound) (Authority.sourceIndex bound) record.2.state.current)

def legal : Bool := (List.range span).all fun offset =>
  let actual := bound.source.actualExecution (start+offset)
  decide (Open.Legal bound.source.code.law actual.before actual.submitted)

def material : Settlement.Material Party Good → ℚ
  | .debit party good => ((List.range span).map fun offset =>
      let actual := bound.source.actualExecution (start+offset)
      bound.source.code.law.totalDebit actual.interpreted.items party good).sum
  | .credit party good => -((List.range span).map fun offset =>
      let actual := bound.source.actualExecution (start+offset)
      bound.source.code.law.totalCredit actual.interpreted.items party good).sum
  | .inventory party good => -(terminal bound start span).stock party good
  | .clock => (terminal bound start span).clock
  | .admissibility => if legal bound start span then 0 else 1

def value : EconomicAxis bound.source.code → ℚ
  | .material metric => material bound start span metric
  | .unpaid index holder => (Settlement.holdingAt (holdings bound start span) index (bound.source.code.parties.idxOf holder)).1
  | .service index => ((Identity.firstService bound.source (finish start span-1) index).getD (finish start span) : ℚ)

def axes : List (EconomicAxis bound.source.code) :=
  (Settlement.materials bound.source.code).map .material ++
    (List.range (first bound start).current.slots.length).flatMap (fun index => bound.source.code.parties.map (.unpaid index)) ++
    (List.finRange bound.source.code.task.slots.length).map .service

def evaluate : Evaluation bound.source.code where
  legal := legal bound start span
  complete := (List.finRange bound.source.code.task.slots.length).all fun index =>
    (Identity.firstService bound.source (finish start span-1) index).isSome
  profile := profile bound start span
  native := manifest bound start span
  value := value bound start span

theorem every_native_debit_is_counted (party : Party) (good : Good) :
    (evaluate bound start span).value (.material (.debit party good)) =
      material bound start span (.debit party good) := rfl

theorem legal_iff : legal bound start span = true ↔
    ∀ offset < span, let actual := bound.source.actualExecution (start+offset)
      Open.Legal bound.source.code.law actual.before actual.submitted := by
  simp only [legal,List.all_eq_true,List.mem_range,decide_eq_true_eq]

theorem complete_manifest_is_read_from_the_actual_source :
    (evaluate bound start span).native.candidateGrants = grants bound (start+span) ∧
    (evaluate bound start span).profile = profile bound start span := ⟨rfl,rfl⟩

def verify (supplied : Evaluation bound.source.code) : Bool :=
  decide (supplied.legal = (evaluate bound start span).legal ∧
    supplied.complete = (evaluate bound start span).complete ∧
    supplied.profile = (evaluate bound start span).profile ∧
    supplied.native = (evaluate bound start span).native ∧
    ∀ axis ∈ axes bound start, supplied.value axis = (evaluate bound start span).value axis)

theorem verifies_generated : verify bound start span (evaluate bound start span) = true := by
  unfold verify
  apply decide_eq_true
  exact ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window
