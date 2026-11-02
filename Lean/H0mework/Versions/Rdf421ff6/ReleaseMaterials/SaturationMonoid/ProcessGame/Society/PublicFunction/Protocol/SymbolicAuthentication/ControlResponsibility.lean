import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlExecution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlResponsibility

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input bound.source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule bound.source.code)
  (rival : Opponent bound.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : AttestationTransport.Encoding bound.source)
  (law : AttestationReception.ReceptionLaw bound.source)
  (empty : bound.source.continuation = [])

abbrev actualBound := CommunicationRuntime.actualBound bound input cut protocol rival
abbrev actualInput := CommunicationRuntime.actualInput bound input cut protocol rival
abbrev depth (n : Nat) := bound.source.history.length + 1 + (cut + n)
abbrev runtime (n : Nat) := CommunicationRuntime.activated bound input cut protocol rival vocabulary encoding law empty
  (CommunicationRuntime.ordinal bound cut n)

/-- Read the generated record, not the comparison-only `occurrence` projection. -/
def material (n : Nat) : ControlExecution.Occurrence bound.source :=
  (ControlExecution.run bound.source input cut protocol rival (n + 1)).events[n]'(by
    rw [ControlExecution.generated_events_are_the_actual_coupled_occurrences]
    simp only [List.length_map, List.length_range]
    omega)

theorem material_is_generated (n : Nat) : material bound input cut protocol rival n ∈
    (ControlExecution.run bound.source input cut protocol rival (n + 1)).events := by
  unfold material
  exact List.getElem_mem _

theorem material_eq_occurrence (n : Nat) : material bound input cut protocol rival n =
    ControlExecution.occurrence bound.source input cut protocol rival n := by
  unfold material
  simp only [ControlExecution.generated_events_are_the_actual_coupled_occurrences,
    List.getElem_map, List.getElem_range]

def authorityAt (n : Nat) : Feedback.Authority.Disposition (actualBound bound input cut protocol rival)
    (actualInput bound input cut protocol rival) (cut + n) rfl empty :=
  match (CommunicationRuntime.facade bound input cut protocol rival vocabulary encoding law empty).readoutAt
      (runtime bound input cut protocol rival vocabulary encoding law empty n) (.previous .responsibilities) with
  | .inl payload => payload.2 (cut + n) (by
      change (ProgrammeHistory.visitAt (actualBound bound input cut protocol rival).source.input
        (runtime bound input cut protocol rival vocabulary encoding law empty n).state).current = _
      rw [CommunicationRuntime.activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem authority_is_original_root_generated (n : Nat) :
    authorityAt bound input cut protocol rival vocabulary encoding law empty n =
      Feedback.Authority.generate (actualBound bound input cut protocol rival)
        (actualInput bound input cut protocol rival) (cut + n) rfl empty := rfl

def items (n : Nat) : List (ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument) :=
  (Financial.inventoryAt (actualBound bound input cut protocol rival).source.input
    (ProgrammeHistory.visitAt (actualBound bound input cut protocol rival).source.input
      (depth bound cut n + 1))).filterMap
    (Financial.InstructionOrigin.instruction? (actualBound bound input cut protocol rival).source.input)

def audit (n : Nat) := (items bound input cut protocol rival n).map fun item =>
  (item, decide (bound.source.code.law.Valid item.before item.request))

def authenticationAt (n : Nat) :=
  (CommunicationRuntime.rooted bound input cut protocol rival vocabulary encoding law empty (n + 1)).requests
    ⟨n, Nat.lt_succ_self n⟩

structure Envelope (n : Nat) where
  private mk ::
  control : ControlExecution.Occurrence bound.source
  responsibility : Feedback.Authority.Disposition (actualBound bound input cut protocol rival)
    (actualInput bound input cut protocol rival) (cut + n) rfl empty
  requests : List (ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument × Bool)
  authentication : List (ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument ×
    OwnedAttestation.OutcomeData (OwnedAttestation.Ballot bound.source))

/-- The original root supplies the native histories; the material execution
supplies the control record. Their common index is paid below by actual-word equalities. -/
def produce (n : Nat) : Envelope bound input cut protocol rival empty n :=
  ⟨material bound input cut protocol rival n,
    authorityAt bound input cut protocol rival vocabulary encoding law empty n,
    audit bound input cut protocol rival n,
    authenticationAt bound input cut protocol rival vocabulary encoding law empty n⟩

include empty

theorem material_has_original_before_word_after_and_next (n : Nat) :
    let record := material bound input cut protocol rival n
    record.before.current = (AttestationTransport.execution bound.source input cut protocol rival n).before ∧
      record.submitted = (AttestationTransport.execution bound.source input cut protocol rival n).submitted ∧
      record.after.current = (AttestationTransport.execution bound.source input cut protocol rival n).after ∧
      record.after.current = bound.source.code.law.next record.before.current record.submitted := by
  have all := ControlExecution.every_record_has_original_word_and_literal_next bound.source input cut protocol rival
    empty (n + 1) _ (material_is_generated bound input cut protocol rival n)
  rw [material_eq_occurrence] at all ⊢
  exact all.2.2

theorem financial_origins_are_exactly_the_record_items (n : Nat) :
    items bound input cut protocol rival n = bound.source.code.law.rawItems
      (material bound input cut protocol rival n).before.current (material bound input cut protocol rival n).submitted := by
  rw [items, Native.both_consumers_use_the_same_actual_word]
  have same := material_has_original_before_word_after_and_next bound input cut protocol rival empty n
  rw [same.1, same.2.1]

theorem audit_is_material_requests (n : Nat) :
    (produce bound input cut protocol rival vocabulary encoding law empty n).requests =
      (bound.source.code.law.rawItems (material bound input cut protocol rival n).before.current
        (material bound input cut protocol rival n).submitted).map (fun item =>
          (item, decide (bound.source.code.law.Valid item.before item.request))) := by
  change (items bound input cut protocol rival n).map _ = _
  rw [financial_origins_are_exactly_the_record_items bound input cut protocol rival empty]

theorem audit_retains_every_request_and_actual_validity (n : Nat) :
    ((produce bound input cut protocol rival vocabulary encoding law empty n).requests.map fun row => row.1.request) =
      (produce bound input cut protocol rival vocabulary encoding law empty n).control.submitted ∧
      ∀ row ∈ (produce bound input cut protocol rival vocabulary encoding law empty n).requests,
        row.2 = true ↔ bound.source.code.law.Valid row.1.before row.1.request := by
  constructor
  · change ((items bound input cut protocol rival n).map _).map _ = _
    rw [financial_origins_are_exactly_the_record_items bound input cut protocol rival empty]
    simpa only [List.map_map, Function.comp_def, RawLaw.rawItems, produce] using
      bound.source.code.law.inventory_requests_exact
        (material bound input cut protocol rival n).before.current 0 (material bound input cut protocol rival n).submitted
  · intro row inside
    obtain ⟨item, _, rfl⟩ := List.mem_map.mp inside
    simp only [decide_eq_true_eq]

theorem authentication_and_validity_use_the_same_items (n : Nat) :
    (produce bound input cut protocol rival vocabulary encoding law empty n).authentication.map Prod.fst =
      (produce bound input cut protocol rival vocabulary encoding law empty n).requests.map Prod.fst := by
  change (OwnedAttestation.audit bound.source input cut protocol rival vocabulary n).map Prod.fst =
    ((items bound input cut protocol rival n).map _).map Prod.fst
  have original : (OwnedAttestation.audit bound.source input cut protocol rival vocabulary n).map Prod.fst =
      bound.source.code.law.rawItems (AttestationTransport.execution bound.source input cut protocol rival n).before
        (AttestationTransport.execution bound.source input cut protocol rival n).submitted := by
    apply List.ext_getElem?
    intro i
    simp [OwnedAttestation.audit, Function.comp_def]
  have same := material_has_original_before_word_after_and_next bound input cut protocol rival empty n
  rw [original, financial_origins_are_exactly_the_record_items bound input cut protocol rival empty,
    same.1, same.2.1]
  rw [List.map_map]
  exact (List.map_id _).symm

theorem authentication_is_on_the_same_generated_next (n : Nat) :
    (runtime bound input cut protocol rival vocabulary encoding law empty n).tick.next =
      runtime bound input cut protocol rival vocabulary encoding law empty (n + 1) := by
  change ((CommunicationRuntime.facade bound input cut protocol rival vocabulary encoding law empty).seed.advance
    (CommunicationRuntime.ordinal bound cut n)).tick.next =
      (CommunicationRuntime.facade bound input cut protocol rival vocabulary encoding law empty).seed.advance
        (CommunicationRuntime.ordinal bound cut (n + 1))
  rw [show CommunicationRuntime.ordinal bound cut (n + 1) = CommunicationRuntime.ordinal bound cut n + 1 by
    dsimp only [CommunicationRuntime.ordinal]
    omega]
  rfl

theorem rejected_request_has_no_material_or_financial_debit (n : Nat)
    (row : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument × Bool)
    (inside : row ∈ (produce bound input cut protocol rival vocabulary encoding law empty n).requests)
    (rejected : row.2 = false) :
    bound.source.code.law.step row.1.before row.1.request = row.1.before ∧
      bound.source.code.law.actualDebit row.1.before row.1.request = [] ∧
      bound.source.code.law.actualCredit row.1.before row.1.request = [] := by
  have invalid : ¬ bound.source.code.law.Valid row.1.before row.1.request := by
    intro valid
    have accepted := ((audit_retains_every_request_and_actual_validity bound input cut protocol rival
      vocabulary encoding law empty n).2 row inside).mpr valid
    rw [rejected] at accepted
    contradiction
  simp [RawLaw.step, RawLaw.actualDebit, RawLaw.actualCredit, invalid]

theorem refused_interface_attempt_cannot_originate_requests (n : Nat)
    (rejected : ControlExecution.suppressed bound.source.code
      (produce bound input cut protocol rival vocabulary encoding law empty n).control.call = true) :
    (produce bound input cut protocol rival vocabulary encoding law empty n).requests = [] ∧
      (produce bound input cut protocol rival vocabulary encoding law empty n).control.after.frame =
        (produce bound input cut protocol rival vocabulary encoding law empty n).control.before.frame := by
  have inside : material bound input cut protocol rival n ∈
      ControlExecution.refusals bound.source input cut protocol rival (n + 1) :=
    List.mem_filter.mpr ⟨material_is_generated bound input cut protocol rival n, rejected⟩
  have refused := ControlExecution.refused_external_attempt_cannot_create_work_or_packets
    bound.source input cut protocol rival (n + 1) _ inside
  refine ⟨?_, refused.2.1⟩
  rw [audit_is_material_requests, refused.1]
  rfl

theorem valid_mandate_request_has_current_command_permission (n : Nat)
    (row : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument × Bool)
    (inside : row ∈ (produce bound input cut protocol rival vocabulary encoding law empty n).requests)
    (signer : Party) (command : Mandate.Command Party)
    (request : row.1.request = Mandate.request bound.scope row.1.before signer command)
    (accepted : row.2 = true) : Mandate.CanRun bound.scope row.1.before signer command := by
  have valid := ((audit_retains_every_request_and_actual_validity bound input cut protocol rival
    vocabulary encoding law empty n).2 row inside).mp accepted
  rw [request, bound.law_exact] at valid
  exact (Mandate.command_policy bound.base bound.scope _ _ _).mp valid.1.2

theorem native_service_payment_is_the_record_payment (n : Nat)
    (slot : Native.Slot (actualBound bound input cut protocol rival).source) :
    Native.Paid (actualBound bound input cut protocol rival).source (depth bound cut n) slot ↔
      bound.source.code.task.earliest ≤ (material bound input cut protocol rival n).before.current.clock ∧
      (material bound input cut protocol rival n).after.current.clock ≤ bound.source.code.task.deadline ∧
      Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid bound.source.code.law
        (material bound input cut protocol rival n).before.current (material bound input cut protocol rival n).submitted
        (Native.slot (actualBound bound input cut protocol rival).source slot).bearer
        (Native.slot (actualBound bound input cut protocol rival).source slot).goods
        (Native.slot (actualBound bound input cut protocol rival).source slot).purpose := by
  have same := material_has_original_before_word_after_and_next bound input cut protocol rival empty n
  rw [same.1, same.2.1, same.2.2.1]
  rfl

theorem original_service_archive_survives_later_control (n later : Nat)
    (slot : Native.Slot (actualBound bound input cut protocol rival).source)
    (terminal : ((produce bound input cut protocol rival vocabulary encoding law empty n).responsibility.feedback.native.services
      slot).state.TerminalAt 0) :
    ((produce bound input cut protocol rival vocabulary encoding law empty (n + later)).responsibility.feedback.native.services
      slot).state =
      ((produce bound input cut protocol rival vocabulary encoding law empty n).responsibility.feedback.native.services slot).state := by
  change (Native.historyAt (actualBound bound input cut protocol rival).source slot
    (depth bound cut (n + later) + 1)).state = _
  rw [show depth bound cut (n + later) + 1 = (depth bound cut n + 1) + later by
    dsimp only [depth]
    omega]
  exact Native.first_archive_is_retained _ slot _ later terminal

theorem external_call_retains_its_actual_callback_source (n : Nat) (attempt : Move bound.source.code)
    (external : (produce bound input cut protocol rival vocabulary encoding law empty n).control.call = .external attempt) :
    rival (produce bound input cut protocol rival vocabulary encoding law empty n).control.before.history
      (produce bound input cut protocol rival vocabulary encoding law empty n).control.before.past
      (produce bound input cut protocol rival vocabulary encoding law empty n).control.before.frame = attempt :=
  (ControlExecution.external_record_has_the_original_callback_origin bound.source input cut protocol rival
    (n + 1) _ (material_is_generated bound input cut protocol rival n) attempt external).2.2.2

theorem original_native_histories_and_root_next_are_consumed_together (n : Nat) :
    let generated := produce bound input cut protocol rival vocabulary encoding law empty n
    let actual := runtime bound input cut protocol rival vocabulary encoding law empty n
    generated.responsibility.current = Native.Authority.fullGenerate (actualBound bound input cut protocol rival)
        (depth bound cut n) ∧
      generated.responsibility.feedback.native = Native.generate (actualBound bound input cut protocol rival).source
        (depth bound cut n) ∧
      HEq ((CommunicationRuntime.facade bound input cut protocol rival vocabulary encoding law empty).readoutAt
        actual (.previous .responsibilities)) (actual.tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq actual.tick.generated.wholeLedgerWriteBack
        (actual.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt actual.current.visit.current) ∧
      actual.tick.nextCurrent = (CommunicationRuntime.facade bound input cut protocol rival vocabulary encoding law empty).process.stateAt
        ((CommunicationRuntime.facade bound input cut protocol rival vocabulary encoding law empty).process.successor actual.state) := by
  have rooted := (CommunicationRuntime.facade bound input cut protocol rival vocabulary encoding law empty).readoutAt_factorizes
    (runtime bound input cut protocol rival vocabulary encoding law empty n) (.previous .responsibilities)
  exact ⟨(authorityAt bound input cut protocol rival vocabulary encoding law empty n).current_exact,
    (authorityAt bound input cut protocol rival vocabulary encoding law empty n).feedback.native_exact,
    rooted.2.2.2.1, rooted.2.2.1, rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlResponsibility
