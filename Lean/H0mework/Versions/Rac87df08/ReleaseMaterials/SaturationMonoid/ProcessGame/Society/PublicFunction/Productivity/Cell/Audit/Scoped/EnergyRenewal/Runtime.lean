import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

theorem access_valid_iff {plan : Plan} (ready : Ready plan) (before : AuditCurrent) (actor : Party) (query : Query) :
    ready.law.Valid before (accessRequest actor query) ↔ before.technology.holder = some actor ∧
      ready.task.earliest ≤ before.clock ∧ before.clock ≤ ready.task.deadline ∧
      1 ≤ before.stock actor .energy ∧ (if actor = 0 then 2 else 1) ≤ before.stock 0 .energy := by
  simp [Ready.law,accessRequest,RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,
    RawPolicy.eval,RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,
    Mandate.law,Mandate.eraseCurrent,Mandate.eraseRequest,Mandate.eraseOperation,
    energyBase,baseLaw,erasePort,Cell.law,Ready.scope,native,NonnegativeBundle,locate,flowAt,amount]
  tauto

private abbrev operationDecidableEq : DecidableEq (Operation Party Good (Mandate.State Party Technology) Unit) := by
  intro left right
  cases left <;> cases right <;> (try simp only [Operation.produce.injEq,Operation.transfer.injEq,Operation.use.injEq,
    Operation.issue.injEq,Operation.assign.injEq,Operation.settle.injEq,Operation.revise.injEq,reduceCtorEq]) <;> infer_instance
private abbrev actionDecidableEq : DecidableEq Action := by
  letI := operationDecidableEq
  intro left right
  cases left
  cases right
  simp only [Request.mk.injEq]
  infer_instance
attribute [local instance] actionDecidableEq

structure Delivery {plan : Plan} (ready : Ready plan) (before : AuditCurrent) (word : List Action) (query : Query) where
  private mk ::
  access : {item // item ∈ ready.law.rawItems before word}
  accessRequest : access.val.request = EnergyRenewal.accessRequest plan.candidate query
  accessPaid : ready.law.Valid access.val.before access.val.request
  fee : {item // item ∈ ready.law.rawItems before word}
  feeRequest : fee.val.request = deliveryFee
  feePaid : ready.law.Valid fee.val.before fee.val.request
  consecutive : fee.val.index = access.val.index+1

def deliveries {plan : Plan} (ready : Ready plan) (before : AuditCurrent) (word : List Action) (query : Query) :
    List (Delivery ready before word query) :=
  (ready.law.rawItems before word).attach.flatMap fun access =>
    (ready.law.rawItems before word).attach.filterMap fun fee =>
      if linked : access.val.request = accessRequest plan.candidate query ∧
          ready.law.Valid access.val.before access.val.request ∧
          fee.val.request = deliveryFee ∧ ready.law.Valid fee.val.before fee.val.request ∧
          fee.val.index = access.val.index+1 then
        some ⟨access,linked.1,linked.2.1,fee,linked.2.2.1,linked.2.2.2.1,linked.2.2.2.2⟩
      else none

namespace Delivery
variable {plan : Plan} {ready : Ready plan} {before : AuditCurrent} {word : List Action} {query : Query}
  (receipt : Delivery ready before word query)

theorem authority_is_paid_and_within_the_new_window :
    receipt.access.val.before.technology.holder = some plan.candidate ∧
    ready.task.earliest ≤ receipt.access.val.before.clock ∧
    receipt.access.val.before.clock ≤ ready.task.deadline ∧
    1 ≤ receipt.access.val.before.stock plan.candidate .energy := by
  have paid := receipt.accessPaid
  rw [receipt.accessRequest,access_valid_iff] at paid
  exact ⟨paid.1,paid.2.1,paid.2.2.1,paid.2.2.2.1⟩

theorem service_really_debits_the_candidate :
    (ready.law.step receipt.access.val.before receipt.access.val.request).stock plan.candidate .energy+1 =
      receipt.access.val.before.stock plan.candidate .energy := by
  have balance := ready.law.material_step_balance receipt.access.val.before receipt.access.val.request plan.candidate .energy
  simp only [RawLaw.actualDebit,RawLaw.actualCredit,if_pos receipt.accessPaid] at balance
  simpa [receipt.accessRequest,RawLaw.debit,RawLaw.credit,EnergyRenewal.accessRequest,flowAt,locate,amount] using balance

theorem delivery_really_debits_the_service :
    (ready.law.step receipt.fee.val.before receipt.fee.val.request).stock 0 .energy+1 = receipt.fee.val.before.stock 0 .energy := by
  have balance := ready.law.material_step_balance receipt.fee.val.before receipt.fee.val.request 0 .energy
  simp only [RawLaw.actualDebit,RawLaw.actualCredit,if_pos receipt.feePaid] at balance
  simpa [receipt.feeRequest,RawLaw.debit,RawLaw.credit,deliveryFee,flowAt,locate,amount] using balance

def evidence (_receipt : Delivery ready before word query) : List (Slot × Evidence) :=
  (selected query).map fun slot => (slot,restrict (fields query) (originalEvidence slot))

theorem every_slice_has_original_service_origin (slot : Slot) (evidence : Evidence)
    (released : (slot,evidence) ∈ receipt.evidence) : Origin slot evidence := by
  obtain ⟨original,_,same⟩ := List.mem_map.mp released
  rcases Prod.mk.inj same with ⟨rfl,rfl⟩
  exact restrict_has_origin _ _ _ (original_evidence_has_origin _)

theorem both_independent_checks_consume_the_original_service (slot : Slot) (evidence : Evidence)
    (released : (slot,evidence) ∈ receipt.evidence) :
    (traceCheck slot evidence = .verified → source.ActualSlotPaid 1 (originalIndex slot)) ∧
    (lifecycleCheck slot evidence = .verified → source.ActualSlotPaid 1 (originalIndex slot)) :=
  ⟨trace_verifies_original _ _ (receipt.every_slice_has_original_service_origin _ _ released),
    lifecycle_verifies_original _ _ (receipt.every_slice_has_original_service_origin _ _ released)⟩
end Delivery

inductive Outcome (plan : Plan) : Type where
  | ready (generated : Ready plan)
  | blocked (reason : Blocked plan)

def generate (plan : Plan) : Outcome plan :=
  match selected : choose plan with
  | some ready => .ready ready
  | none => .blocked (refusal_has_an_actual_reason plan selected)

namespace Runtime

/-- An epoch is obtainable from the paid supply output; neither state nor Ready is an external witness. -/
private inductive Stage where
  | supply (plan : Plan)
  | epoch {plan : Plan} (ready : Ready plan) (queries : Nat → Query)

def Stage.input : Stage → ProgrammeSource.Input Party Good AuditPort (Mandate.State Party Technology) Unit
  | .supply plan => EnergyRenewal.input plan
  | .epoch ready queries => ready.epochInput queries

structure EpochResult {plan : Plan} (ready : Ready plan) (queries : Nat → Query) (ordinal : Nat) where
  commands : List (Mandate.ActualCommand energyBase ready.scope
    (ready.epochCurrent queries ordinal) (if ordinal = 0 then [] else ready.epochWord queries (ready.epochCurrent queries ordinal)))
  actualCommands : commands = Mandate.commandsAt energyBase ready.scope
    (ready.epochCurrent queries ordinal) (if ordinal = 0 then [] else ready.epochWord queries (ready.epochCurrent queries ordinal))
  packets : List (Delivery ready (ready.epochCurrent queries ordinal)
    (if ordinal = 0 then [] else ready.epochWord queries (ready.epochCurrent queries ordinal)) (queries ordinal))
  actualPackets : packets = deliveries ready (ready.epochCurrent queries ordinal)
    (if ordinal = 0 then [] else ready.epochWord queries (ready.epochCurrent queries ordinal)) (queries ordinal)
  financeMatrix : (ready.epochCurrent queries (ordinal+1)).claims = (before plan).claims

def Output : Stage → Nat → Type
  | .supply plan,_ => Outcome plan
  | .epoch ready queries,ordinal => EpochResult ready queries ordinal

def result : (stage : Stage) → (ordinal : Nat) → Output stage ordinal
  | .supply plan,_ => generate plan
  | .epoch ready queries,ordinal =>
    ⟨Mandate.commandsAt energyBase ready.scope (ready.epochCurrent queries ordinal)
        (if ordinal = 0 then [] else ready.epochWord queries (ready.epochCurrent queries ordinal)),rfl,
      deliveries ready (ready.epochCurrent queries ordinal)
        (if ordinal = 0 then [] else ready.epochWord queries (ready.epochCurrent queries ordinal)) (queries ordinal),rfl,
      ready.epoch_preserves_claims queries (ordinal+1)⟩

def projectionLaw (stage : Stage) : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource stage.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    (ordinal : Nat) → current = (ProgrammeHistory.visitAt stage.input ordinal).current →
      (match stage with | .supply plan => ordinal = plan.cut | .epoch .. => True) → Output stage ordinal
  project := fun _ {_} _ _ ordinal _canonical _chosen => result stage ordinal

def root (stage : Stage) :=
  (ProgrammeLiving.livingRoot stage.input).withProjectionCoface (projectionLaw stage)

theorem emitting_root_is_preserved (stage : Stage) :
    (root stage).toAuthoritativeRoot.toRoot = (ProgrammeLiving.livingRoot stage.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (stage : Stage) (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N stage.input) :=
  ⟨ProgrammeSource.V stage.input,root stage,ProgrammeHistory.temporalVisit stage.input ordinal⟩

def process (stage : Stage) : SourceNativeLivingRootProcess (ProgrammeSource.N stage.input) where
  State := Nat
  stateAt := stateAt stage
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N stage.input) =>
      (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective stage.input (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | execution | continuation

def facade (stage : Stage) : SourceNativeLivingRuntimeFacade (ProgrammeSource.N stage.input) where
  process := process stage
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .execution => ProgrammeLiving.projectionLaw stage.input
    | .continuation => projectionLaw stage
  installationAt := by
    intro state face
    cases face
    · exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
        (ProgrammeLiving.authoritySource stage.input) (projectionLaw stage)
    · exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (ProgrammeLiving.authoritySource stage.input) (projectionLaw stage)
  projectionAt := fun _ face => match face with | .execution => .execution | .continuation => ()

def activated (stage : Stage) (ordinal : Nat) := (facade stage).seed.advance ordinal

theorem activated_state (stage : Stage) (ordinal : Nat) : (activated stage ordinal).state = ordinal := by
  induction ordinal with | zero => rfl | succ ordinal ih => exact congrArg Nat.succ ih

theorem shares_actual_writeback_and_generated_next (stage : Stage) (ordinal : Nat) :
    (activated stage ordinal).tick.generated.occurrence =
      (activated stage ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (activated stage ordinal).current.visit.current ∧
    HEq (activated stage ordinal).tick.generated.wholeLedgerWriteBack
      ((activated stage ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated stage ordinal).current.visit.current) ∧
    HEq ((facade stage).readoutAt (activated stage ordinal) .continuation)
      ((activated stage ordinal).tick.generated.projectionOutcome
        (((facade stage).installationAt (activated stage ordinal) .continuation).embed
          ((facade stage).projectionAt (activated stage ordinal) .continuation))) ∧
    (activated stage ordinal).tick.nextCurrent =
      (process stage).stateAt ((process stage).successor (activated stage ordinal).state) :=
  ((facade stage).readoutAt_factorizes (activated stage ordinal) .continuation).2

def consume (stage : Stage) (ordinal : Nat)
    (chosen : match stage with | .supply plan => ordinal = plan.cut | .epoch .. => True) : Output stage ordinal :=
  match (facade stage).readoutAt (activated stage ordinal) .continuation with
  | .inl ⟨_,payload⟩ => payload ordinal (by
      change (ProgrammeHistory.visitAt stage.input (activated stage ordinal).state).current = _
      rw [activated_state]) (by cases stage <;> exact chosen)
  | .inr impossible => nomatch impossible

structure EpochSeed (plan : Plan) : Type where
  private mk ::
  ready : Ready plan
  generated : consume (.supply plan) plan.cut rfl = .ready ready
  previous : (ordinal : Nat) → Governance.Runtime.Result plan.queries plan.larger plan.births plan.replies ordinal
  previousGenerated : ∀ ordinal, previous ordinal = Governance.Runtime.result plan.queries plan.larger plan.births plan.replies ordinal

/-- The network decoder obtains its epoch only from this actual cut's installed payload. -/
def nextEpoch (plan : Plan) : Option (EpochSeed plan) :=
  match generated : consume (.supply plan) plan.cut rfl with
  | .ready ready => some ⟨ready,generated,Governance.Runtime.result plan.queries plan.larger plan.births plan.replies,fun _ => rfl⟩
  | .blocked _ => none

theorem EpochSeed.starts_at_the_supply_roots_generated_next {plan : Plan} (seed : EpochSeed plan) (queries : Nat → Query) :
    (seed.ready.epochInput queries).initial =
      ProgrammeSource.rawCurrent (input plan) (ProgrammeHistory.visitAt (input plan) (plan.cut+1)).current := by
  rw [current_is_own_root_current]
  rfl

theorem EpochSeed.preserves_owner_roles_and_original_failures {plan : Plan} (seed : EpochSeed plan)
    (ordinal : Nat) :
    (seed.previous ordinal).roles = (Governance.Runtime.result plan.queries plan.larger plan.births plan.replies ordinal).roles ∧
    (seed.previous ordinal).rejected = (Governance.Runtime.result plan.queries plan.larger plan.births plan.replies ordinal).rejected := by
  rw [seed.previousGenerated]
  exact ⟨rfl,rfl⟩

def EpochSeed.facade {plan : Plan} (seed : EpochSeed plan) (queries : Nat → Query) :=
  Runtime.facade (.epoch seed.ready queries)

def EpochSeed.consume {plan : Plan} (seed : EpochSeed plan) (queries : Nat → Query) (ordinal : Nat) :
    EpochResult seed.ready queries ordinal := Runtime.consume (.epoch seed.ready queries) ordinal True.intro

end Runtime
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal
