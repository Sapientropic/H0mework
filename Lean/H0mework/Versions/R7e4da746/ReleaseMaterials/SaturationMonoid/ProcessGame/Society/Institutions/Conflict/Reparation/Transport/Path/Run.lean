import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Path.Step
import Mathlib.Data.List.Induction

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld
open Quantities.Execution (observedScript)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)

local notation "Input" => Option (Compile.RawInput Party Good Port Technology Instrument)
local notation "Script" => List Input

/-- Start at the actual filed visit. Each subsequent source input consumes
the authority that the preceding kernel action returned. -/
def run (history : Script) : State claim history :=
  List.reverseRecOn (motive := State claim) history (initial claim)
    (fun _ input earlier => (step earlier input).next)

theorem run_nil : run claim [] = initial claim := by
  rw [run, List.reverseRecOn_nil]

theorem run_snoc (past : Script) (input : Input) :
    run claim (past ++ [input]) = (step (run claim past) input).next := by
  unfold run
  rw [List.reverseRecOn_concat]

theorem every_input_consumes_the_original_whole_ledger (past : Script) (input : Input) :
    (step (run claim past) input).emission.next = (run claim (past ++ [input])).resident.erase :=
  (step (run claim past) input).generated.trans
    (congrArg (fun state : State claim (past ++ [input]) => state.resident.erase) (run_snoc claim past input)).symm

theorem the_observed_policy_consumes_every_generated_next
    (policy : Nat → Root.Cut Party Good Port Technology Instrument → Input) (tick : Nat) :
    let past := observedScript policy tick (Birth.attacked claim)
    let input := policy tick (originalAt claim past)
    (step (run claim past) input).emission.next =
      (run claim (observedScript policy (tick + 1) (Birth.attacked claim))).resident.erase :=
  every_input_consumes_the_original_whole_ledger claim _ _

private theorem row_read {N : WorldRelationNetwork} {left right : N.Support} (same : left = right)
    (old : OpenResponsibilityAt N left) (new : OpenResponsibilityAt N right) (entry : HEq old new) :
    old.1 = new.1 ∧ old.claim = new.claim ∧ old.progressBudget = new.progressBudget := by
  cases same
  cases eq_of_heq entry
  exact ⟨rfl, rfl, rfl⟩

theorem the_generated_entry_is_the_original_reparation (history : Script) :
    let actual := run claim history
    actual.resident.entry.1 = actual.shape.repairKey ∧
      actual.resident.entry.claim = actual.shape.repairClaim ∧
      actual.resident.entry.progressBudget = (Birth.law claim).budget actual.position.phase := by
  let actual := run claim history
  have read := row_read actual.resident.support_eq actual.resident.entry _ actual.resident.repair_eq
  exact ⟨read.1.trans (actual.shape.repair_key _ _), read.2.1.trans (actual.shape.repair_claim _ _),
    read.2.2.trans (actual.shape.repair_budget _ _)⟩

private def moveAddress (past : Script) (input : Input) (prior : Address (run claim past).world) :
    Address (run claim (past ++ [input])).world :=
  cast (congrArg (fun state : State claim (past ++ [input]) => Address state.world)
    (run_snoc claim past input).symm) ((step (run claim past) input).forwardAddress prior)

/-- Follow the original victim and claim using only the address maps of
the kernel actions written on this actual trajectory. -/
def originalAddress (history : Script) : Address (run claim history).world :=
  List.reverseRecOn (motive := fun earlier => Address (run claim earlier).world) history
    ((run claim []).address) (fun past input prior => moveAddress claim past input prior)

private theorem cast_address {history : Script} {left right : State claim history} (same : left = right) :
    cast (congrArg (fun state : State claim history => Address state.world) same) left.address =
      right.address := by cases same; rfl

private theorem original_address_at_every_cut (history : Script) :
    (run claim history).address = originalAddress claim history := by
  induction history using List.reverseRecOn with
  | nil => rw [originalAddress, List.reverseRecOn_nil]
  | append_singleton past input earlier =>
    unfold originalAddress
    rw [List.reverseRecOn_concat]
    change _ = moveAddress claim past input (originalAddress claim past)
    rw [← earlier]
    unfold moveAddress
    rw [Step.the_written_address_is_the_transported_address]
    exact (cast_address claim (run_snoc claim past input).symm).symm

theorem the_live_row_is_addressed_to_the_original_victim (history : Script) :
    let actual := run claim history
    (actual.resident.entry.1, actual.resident.entry.claim) = originalAddress claim history := by
  let actual := run claim history
  have entry := the_generated_entry_is_the_original_reparation claim history
  exact (Prod.ext entry.1 entry.2.1 : (_, _) = actual.address).trans
    (original_address_at_every_cut claim history)

theorem exact_settlement_at_every_generated_visit (history : Script) :
    Nonempty ((Birth.law claim).SettlementAt (run claim history).position.phase) ↔
      recordedDue source attack history community key = 0 :=
  (run claim history).position.exact_settlement

theorem already_paid_reparation_stays_paid_at_every_generated_descendant (past suffix : Script)
    (paid : Nonempty ((Birth.law claim).SettlementAt (run claim past).position.phase)) :
    Nonempty ((Birth.law claim).SettlementAt (run claim (past ++ suffix)).position.phase) := by
  apply (exact_settlement_at_every_generated_visit claim _).mpr
  have paid := (exact_settlement_at_every_generated_visit claim past).mp paid
  have decreases := recordedDue_append_le source attack past suffix community key
  exact le_antisymm (decreases.trans_eq paid) (le_max_left _ _)

theorem a_unilateral_continuation_keeps_the_live_reparation_disposition (past suffix : Script)
    (unilateral : ∀ item ∈ Quantities.Execution.inventory (originalAt claim past) suffix,
      community item.request.signer = community key.2.1) :
    recordedDue source attack (past ++ suffix) community key =
      recordedDue source attack past community key ∧
    (Nonempty ((Birth.law claim).SettlementAt (run claim (past ++ suffix)).position.phase) ↔
      Nonempty ((Birth.law claim).SettlementAt (run claim past).position.phase)) := by
  have unchanged := recordedDue_after_a_unilateral_suffix claim past suffix unilateral
  refine ⟨unchanged, ?_⟩
  rw [exact_settlement_at_every_generated_visit, exact_settlement_at_every_generated_visit, unchanged]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport
