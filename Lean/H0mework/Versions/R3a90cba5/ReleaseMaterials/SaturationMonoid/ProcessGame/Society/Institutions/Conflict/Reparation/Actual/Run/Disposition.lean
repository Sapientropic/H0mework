import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Continuation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (inventory)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "History" => Script Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument

def SourceAuthority (seed : C) (history : History) : Prop :=
  ∀ item ∈ inventory seed history, seed.native.input.law.Valid item.before item.request

inductive Approval (seed : C) (history : History)
  | authorityRefused (item : Item) (original : item ∈ inventory seed history)
      (unlicensed : ¬ seed.native.input.law.Valid item.before item.request)
  | settlementRefused (checked : SourceAuthority seed history) (issue : Quantities.Obstruction seed history)
  | settled (checked : SourceAuthority seed history) (proof : Quantities.Settled seed history)

/-- Validate the actual recorded attempt. A refusal is a disposition of
the original submitted programme and preserves the written liability. -/
def approval (seed : C) (history : History) : Approval seed history :=
  match Material.inspectList (fun item : Item => seed.native.input.law.Valid item.before item.request)
      (inventory seed history) with
  | .failure item original unlicensed => .authorityRefused item original unlicensed
  | .clear checked => match Quantities.decideAt seed history with
    | .blocked issue => .settlementRefused checked issue
    | .feasible settled => .settled checked (Quantities.settle seed history settled)

structure Published (seed : C) (community : Party → Community) (history : History) where
  next : State seed community history
  recorded : Quantities.Recorded seed history
  result : Approval seed history

def publish (seed : C) (community : Party → Community) (history : History) : Published seed community history :=
  ⟨run seed community history, Quantities.record seed history, approval seed history⟩

def publishAfter {seed : C} {community : Party → Community} {past : History}
    (prior : State seed community past) (suffix : History) : Published seed community (past ++ suffix) :=
  ⟨resume prior suffix, Quantities.record seed _, approval seed _⟩

theorem publication_consumes_the_retained_visit (seed : C) (community : Party → Community) (past suffix : History) :
    (publishAfter (run seed community past) suffix).next = (publish seed community (past ++ suffix)).next :=
  resume_consumes_the_original_ledger past suffix

theorem refused_or_paid_the_original_losses_remain_on_the_written_successor
    (seed : C) (community : Party → Community) (past suffix : History)
    (origin : Occurrence seed community) (original : origin ∈ originalLosses seed community past) :
    let result := publish seed community (past ++ suffix)
    Quantities.Recorded seed (past ++ suffix) ∧
      ∃ balance, ∃ row, result.next.read row = .inr (origin, balance) :=
  ⟨(publish seed community _).recorded,
    every_actual_loss_has_its_own_row_on_every_later_current seed community past suffix origin original⟩

theorem publication_keeps_every_previous_loss (seed : C) (community : Party → Community)
    (past suffix : History) (origin : Occurrence seed community)
    (original : origin ∈ originalLosses seed community past) :
    ∃ balance, ∃ row, (publishAfter (run seed community past) suffix).next.read row = .inr (origin, balance) := by
  rw [publication_consumes_the_retained_visit]
  exact (refused_or_paid_the_original_losses_remain_on_the_written_successor seed community past suffix origin original).2

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
