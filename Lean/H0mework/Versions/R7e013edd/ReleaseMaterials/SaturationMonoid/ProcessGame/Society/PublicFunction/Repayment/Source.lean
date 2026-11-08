import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Local
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Delegation.FinancedGenesis
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Productive

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open OutstandingSource.NativeService
open Delegation.Funded (Party Port)

inductive Good where
  | feedstock | service
  deriving DecidableEq

abbrev Current := RawCurrent Party Good (Unit × Option Party) Unit
abbrev Action := Request Party Good Port (Unit × Option Party) Unit

def task : PublicTaskSpec Party Good :=
  ⟨[⟨1, [(.service, 1)], .necessity⟩, ⟨1, [(.service, 1)], .maintenance⟩], 1, 3, by decide +kernel⟩

def base : RawLaw Party Good Port Unit Unit where
  technique := fun _ operator => ⟨[(.feedstock, 1)], [(.service, 3)], [], [.reserve operator]⟩
  controller := fun _ port => match port with | .reserve owner => owner | _ => 1
  allowed := fun _ port actor => match port with | .reserve owner => decide (actor = owner) | _ => false
  stockPort := fun _ owner _ => .reserve owner
  revisionPort := fun _ => .challenge
  revisionCost := fun _ _ => [(.service, 1)]
  settlementUnit := fun _ => .service
  settlementRate := fun _ => 1
  issuerPort := fun _ => .reserve 1
  necessities := fun _ _ => [(.service, 1)]
  mandatoryMaintenance := fun _ _ => [(.service, 1)]
  duration := fun _ => 1
  policy := .opaque (fun current request => match request.operation with
    | .issue _ debtor creditor quantity => decide
        (debtor = 1 ∧ creditor = 2 ∧
          ((quantity = 7 ∧ current.claims () 1 2 = 0) ∨
           (quantity = 3 ∧ current.claims () 1 2 = 7)))
    | .transfer sender recipient goods => decide
        (sender = 2 ∧ recipient = 1 ∧
          ((goods = [(.service, 7)] ∧ current.claims () 1 2 = 7) ∨
           (goods = [(.service, 3)] ∧ current.claims () 1 2 = 10)))
    | _ => true)

def scope : Delegation.Jurisdiction Party Good Port :=
  ⟨task, .service, .challenge, by decide, [(.service, 1)]⟩

def law := Delegation.law base scope
def position : Position Party Unit := ⟨(), 1, 2⟩

def initial (fuel : ℚ) : Current where
  stock := fun person good =>
    if person = 2 ∧ good = .service then 10
    else if person = 1 ∧ good = .feedstock then fuel else 0
  claims := fun _ _ _ => 0
  technology := ((), some 0)
  clock := 0
  round := 0

def issue (quantity : ℚ) : Action := ⟨1, [], .reserve 1, [], .issue () 1 2 quantity⟩
def payout (quantity : ℚ) : Action := ⟨2, [], .reserve 2, [], .transfer 2 1 [(.service, quantity)]⟩
def oldUse : Action := ⟨1, [], .reserve 1, [], .use 1 [(.service, 7)] .investment⟩
def oldRequest : Action := ⟨1, [], .service, [.service], .present⟩
def necessity : Action := ⟨1, [], .service, [.service], .use 1 [(.service, 1)] .necessity⟩
def maintenance : Action := ⟨1, [], .service, [.service], .use 1 [(.service, 1)] .maintenance⟩

def alphabet (current : Current) : List Action :=
  [issue 3, payout 3] ++ (Delegation.members task).eraseDups.map (Delegation.revokeRequest scope current) ++
    [necessity, maintenance]

def sourceWithFuel (fuel : ℚ) : OutstandingSource Party Good Port (Unit × Option Party) Unit where
  seed := {
    law := law
    initial := initial fuel
    task := task
    actionsAt := alphabet
    budget := 5
    original := [issue 7, payout 7, oldUse, oldRequest]
    refused := by
      let before := law.next (initial fuel) []
      let endOfPrefix := law.step (law.step (law.step before (issue 7)) (payout 7)) oldUse
      refine ⟨⟨3, endOfPrefix, oldRequest⟩, ?_, ?_⟩
      · change _ ∈ (law.execute before 0 [issue 7, payout 7, oldUse, oldRequest]).items
        simp only [RawLaw.execute, List.mem_cons]
        exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · have technology : endOfPrefix.technology = ((), some 0) := by
          have keepIssue (current : Current) : (law.step current (issue 7)).technology = current.technology := by
            unfold RawLaw.step
            split <;> rfl
          have keepPayout (current : Current) : (law.step current (payout 7)).technology = current.technology := by
            unfold RawLaw.step
            split <;> rfl
          have keepUse (current : Current) : (law.step current oldUse).technology = current.technology := by
            unfold RawLaw.step
            split <;> rfl
          change (law.step (law.step (law.step before (issue 7)) (payout 7)) oldUse).technology = _
          rw [keepUse, keepPayout, keepIssue]
          rfl
        intro accepted
        have required : Port.service ∈ law.requiredPorts endOfPrefix oldRequest := by
          simp [RawLaw.requiredPorts, RawLaw.debit, oldRequest]
        have guard := accepted.2.1 Port.service required
        have denied : law.allowed endOfPrefix.technology Port.service (1 : Party) = false := by
          rw [technology]
          decide +kernel
        rcases guard with direct | consent
        · change law.allowed endOfPrefix.technology Port.service (1 : Party) = true at direct
          rw [denied] at direct
          cases direct
        · change _ ∈ ([] : List Party) at consent
          exact List.not_mem_nil consent }
  positive := by
    intro slot inside
    simp only [task, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> exact ⟨(.service, 1), by decide, by decide⟩
  completionReport := fun current => .original current (respond law position current).word

def source := sourceWithFuel 4
def shortSource := sourceWithFuel 3

private theorem raw_current_frame
    (actual : OutstandingSource Party Good Port (Unit × Option Party) Unit) (ordinal : Nat) :
    actual.currentAt ordinal = (actual.frameAt ordinal).raw := (actual.canonical_frame ordinal).1

theorem zero_financial_genesis : source.input.initial.claims = fun _ _ _ => 0 := rfl

theorem actual_finance_revocation_and_service :
    (source.actualExecution 1).submitted = [issue 3, payout 3,
      Delegation.revokeRequest scope (source.currentAt 2) 1, necessity, maintenance] ∧
    (source.currentAt 3).claims () 1 2 = 10 ∧
    (source.currentAt 3).stock 1 .service = 0 ∧
    (source.currentAt 3).stock 1 .feedstock = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [source.actual_execution_word, raw_current_frame source 2]; with_unfolding_all rfl
  all_goals rw [(source.canonical_frame 3).1]; decide +kernel

theorem services_paid_before_production (index : source.Slot) :
    (historyAt source index 2).state.TerminalAt 0 := by
  apply (native_terminal_iff_recorded source index 2).mpr
  refine ⟨2, ?_⟩
  have bound : index.val < 2 := index.isLt
  by_cases zero : index.val = 0
  · have same : index = ⟨0, by decide⟩ := Fin.ext zero
    subst index
    decide +kernel
  · have same : index = ⟨1, by decide⟩ := Fin.ext (by change index.val = 1; omega)
    subst index
    decide +kernel

theorem actual_generated_repayments :
    (List.range 4).map (fun offset =>
      (source.actualExecution (2 + offset)).after.claims () 1 2) = [7, 4, 1, 0] ∧
    (List.range 4).map (fun offset => quantity law position (source.currentAt (3 + offset))) = [3, 3, 3, 1] ∧
    (source.currentAt 7).stock 1 .feedstock = 0 ∧
    (source.currentAt 7).stock 1 .service = 2 ∧
      (source.currentAt 7).stock 2 .service = 10 := by
  simp only [OutstandingSource.actual_execution_after, raw_current_frame]
  decide +kernel

theorem each_repayment_consumes_actual_input (offset : Fin 4) :
    (source.actualExecution (2 + offset.val)).submitted =
      [production law position (source.currentAt (3 + offset.val)),
       payment law position (source.currentAt (3 + offset.val))] ∧
    (source.actualExecution (2 + offset.val)).before.stock 1 .feedstock =
      (source.actualExecution (2 + offset.val)).after.stock 1 .feedstock + 1 := by
  simp only [OutstandingSource.actual_execution_word, OutstandingSource.actual_execution_before,
    OutstandingSource.actual_execution_after, raw_current_frame]
  rcases offset with ⟨value, bound⟩
  interval_cases value <;> dsimp only
  all_goals
    constructor
    · with_unfolding_all rfl
    · decide +kernel

theorem fuel_exhaustion_retains_unpaid_principal :
    (shortSource.currentAt 6).claims () 1 2 = 1 ∧
    (shortSource.currentAt 6).stock 1 .feedstock = 0 ∧
    (shortSource.actualExecution 5).submitted = [] ∧
    (shortSource.currentAt 7).claims () 1 2 = 1 ∧
    ¬ Ready law position (shortSource.currentAt 6) := by
  simp only [OutstandingSource.actual_execution_word, raw_current_frame]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · with_unfolding_all rfl
  · decide +kernel
  · decide +kernel

theorem original_service_archives_survive_repayment (index : source.Slot) (later : Nat) :
    (historyAt source index (2 + later)).state = (historyAt source index 2).state :=
  terminal_state_is_preserved source index 2 later (services_paid_before_production index)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Productive
