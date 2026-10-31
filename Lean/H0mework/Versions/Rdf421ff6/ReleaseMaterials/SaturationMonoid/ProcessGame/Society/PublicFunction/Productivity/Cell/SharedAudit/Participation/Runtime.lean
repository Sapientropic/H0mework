import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Transport
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Safety

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.Program

abbrev productionSource := source true

structure AtVisit (ordinal : Nat) where
  arrived : 12 ≤ ordinal
  dialogue : Native.History true
  generated : dialogue = Native.historyAt true (ordinal - 12)
  exact_history : dialogue.state.history = dialogue.run.events
  original_responsibility : dialogue.state.slots = [.live (Native.obligation true)]
  old_services : (slot : productionSource.Slot) → OutstandingSource.NativeService.Prefix productionSource slot ordinal
  old_archives : ∀ slot, (old_services slot).state =
    (OutstandingSource.NativeService.historyAt productionSource slot 1).state
  finance : (Financial.process productionSource.input).Run
    (account true 0).current (account true (ordinal + 1)).current
  full_claims : Financial.BalanceConservation.ledgerClaims productionSource.input
    (account true (ordinal + 1)).current = (productionSource.currentAt (ordinal + 1)).claims
  row : ProgrammeLedger.transferReceiptOf productionSource.input (productionSource.taskWrite (ordinal - 1)).2 =
    some (productionSource.writtenReceipt (ordinal - 1))
  next : (productionSource.actualExecution (ordinal - 1)).after = productionSource.currentAt (ordinal + 1)

def atVisit (ordinal : Nat) (arrived : 12 ≤ ordinal) : AtVisit ordinal where
  arrived := arrived
  dialogue := Native.historyAt true (ordinal - 12)
  generated := rfl
  exact_history := Native.native_history_is_exact true _
  original_responsibility := Native.original_admission_and_residue_are_retained true _
  old_services := fun slot => OutstandingSource.NativeService.historyAt productionSource slot ordinal
  old_archives := fun slot => by
    have same : 1 + (ordinal - 1) = ordinal := by omega
    have archived := original_service_archives_survive true slot (ordinal - 1)
    rw [same] at archived
    exact archived
  finance := by simpa only [Nat.zero_add] using Financial.BalanceConservation.fromActualCut productionSource.input 0 (ordinal + 1)
  full_claims := financial_matrix true _
  row := productionSource.receipt_is_in_original_task_write _
  next := by
    have same : ordinal - 1 + 2 = ordinal + 1 := by omega
    exact (productionSource.actualExecution _).root_next_exact.trans (congrArg productionSource.currentAt same)

/-- These tags are read from the dependent Run's actual event records. -/
theorem actual_native_boundaries_include_refusal_release_and_renewal (shared : Bool) :
    ((Native.historyAt shared 12).state.history.map LifecycleEvent.kind) =
      [.admitted, .maintained, .deferred, .maintained, .bearerRelease, .maintained] := by
  cases shared <;> decide +kernel

structure Certificate where
  current : AtVisit 24
  current_generated : current = atVisit 24 (by decide)
  boundaries : current.dialogue.state.history.map LifecycleEvent.kind =
    [.admitted, .maintained, .deferred, .maintained, .bearerRelease, .maintained]
  messages : ∀ message : Message true,
    (messageOrigin true message).instruction? productionSource.input = some message.item
  chosen_silence : (frameAt true 21).register 1 = .released ∧
    (frameAt true 21).register 2 = .declined ∧ law.Valid (frameAt true 21).raw (audit 1) ∧
    (wordAt true 21 (frameAt true 21)).isEmpty = true
  own_production : (frameAt true 22).register 1 = .released ∧
    (wordAt true 22 (frameAt true 22)).length = 3 ∧
    (∀ item ∈ itemsAt true 22, law.Valid item.before item.request) ∧
    (frameAt true 23).raw.stock 1 .seed = (frameAt true 22).raw.stock 1 .seed + 2 ∧
    1 ≤ (frameAt true 23).raw.stock 1 .life ∧ 1 ≤ (frameAt true 23).raw.stock 1 .spare
  voluntary_return : (frameAt true 24).register 1 = .released ∧
    law.Valid (frameAt true 24).raw (request 1 .accept) ∧ (frameAt true 25).register 1 = .active ∧
    flowAt (law.actualDebit (frameAt true 24).raw (request 1 .accept)) 1 .labor = 1
  newborn : (index : Fin 4) → (kind : Born.Kind) → CarriedService index kind
  newborn_generated : newborn = carriedService
  birth_origin : ∀ index, (carriedBirthOrigin index).instruction? productionSource.input = some (Born.born index).item
  amount : ℚ
  generated_amount : amount = dividend
  positive : 0 < amount
  inventory : ∀ actor good, (productionSource.currentAt 25).stock actor good =
    ((source false).currentAt 25).stock actor good + if actor = 0 ∧ good = .labor then 1 else 0
  credit : ∀ actor good, law.totalCredit (receipts true 25) actor good = law.totalCredit (receipts false 25) actor good
  debit : ∀ actor good, law.totalDebit (receipts true 25) actor good + (if actor = 0 ∧ good = .labor then 1 else 0) =
    law.totalDebit (receipts false 25) actor good
  floor : ∀ item ∈ receipts true 25, ∀ actor : Party,
    ((actor < 3 ∨ 0 < item.before.stock actor .seed) →
      1 ≤ item.before.stock actor .life ∧ 1 ≤ item.before.stock actor .spare) ∧
    ((actor < 3 ∨ 0 < (law.step item.before item.request).stock actor .seed) →
      1 ≤ (law.step item.before item.request).stock actor .life ∧
        1 ≤ (law.step item.before item.request).stock actor .spare)
  carrier : productionSource.currentAt 25 = withLabor ((source false).currentAt 25) 1
  old_capabilities : ∀ word,
    (∀ item ∈ law.rawItems ((source false).currentAt 25) word, law.Valid item.before item.request) →
    (∀ item ∈ law.rawItems (productionSource.currentAt 25) word, law.Valid item.before item.request) ∧
      (law.execute (productionSource.currentAt 25) 0 word).final =
        withLabor (law.execute ((source false).currentAt 25) 0 word).final 1

def certificate : Certificate where
  current := atVisit 24 (by decide)
  current_generated := rfl
  boundaries := actual_native_boundaries_include_refusal_release_and_renewal true
  messages := message_origin_decodes_exactly true
  chosen_silence := withdrawn_work_is_physically_available_but_not_emitted true
  own_production := withdrawal_does_not_cancel_own_production true
  voluntary_return := voluntary_return_is_an_actual_paid_choice true
  newborn := carriedService
  newborn_generated := rfl
  birth_origin := carried_birth_origin_decodes_exactly
  amount := dividend
  generated_amount := rfl
  positive := extended_strict_dividend.2
  inventory := complete_inventory_difference
  credit := complete_credits_equal
  debit := complete_debit_difference
  floor := every_actual_cut_keeps_all_original_and_seeded_bearers true
  carrier := full_carrier_has_exactly_the_same_dividend
  old_capabilities := old_capability_transport_after_all_dialogue_costs

abbrev previousRoot := OutstandingSource.NativeService.Runtime.root productionSource
abbrev previousFacade := OutstandingSource.NativeService.Runtime.facade productionSource

inductive Projection where
  | dialogue | complete

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource productionSource.input).restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {current} _ _ => match projection with
    | .dialogue => (ordinal : Nat) → 12 ≤ ordinal →
        current = (ProgrammeHistory.visitAt productionSource.input ordinal).current → AtVisit ordinal
    | .complete => current = (ProgrammeHistory.visitAt productionSource.input 24).current → Certificate
  project := fun projection {_} _ _ => match projection with
    | .dialogue => fun ordinal arrived _canonical => atVisit ordinal arrived
    | .complete => fun _canonical => certificate

def root := previousRoot.withProjectionCoface projectionLaw

theorem original_root_is_preserved : root.toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot productionSource.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N productionSource.input) :=
  ⟨ProgrammeSource.V productionSource.input, root, ProgrammeHistory.temporalVisit productionSource.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N productionSource.input) where
  State := Nat
  stateAt := stateAt
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N productionSource.input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt productionSource.input first).current =
        (ProgrammeHistory.visitAt productionSource.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective productionSource.input currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : OutstandingSource.NativeService.Runtime.Face productionSource)
  | dialogue | complete

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N productionSource.input) where
  process := process
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => previousFacade.componentAt previousFacade.seed previous
    | .dialogue | .complete => projectionLaw
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
      exact (previousFacade.installationAt previousFacade.seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface previousRoot.toAuthoritativeRoot.source projectionLaw)
    | dialogue => exact SourceNativeProjectionLaw.InstallationAt.componentCoface previousRoot.toAuthoritativeRoot.source projectionLaw
    | complete => exact SourceNativeProjectionLaw.InstallationAt.componentCoface previousRoot.toAuthoritativeRoot.source projectionLaw
  projectionAt := fun _ face => match face with
    | .previous previous => previousFacade.projectionAt previousFacade.seed previous
    | .dialogue => .dialogue
    | .complete => .complete

def activated (ordinal : Nat) : LivingRuntimeState process := facade.seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

theorem actual_complete_payload : projectionLaw.project .complete
    (ProgrammeSource.emitted productionSource.input (ProgrammeHistory.visitAt productionSource.input 24).current) () rfl = certificate := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Runtime
