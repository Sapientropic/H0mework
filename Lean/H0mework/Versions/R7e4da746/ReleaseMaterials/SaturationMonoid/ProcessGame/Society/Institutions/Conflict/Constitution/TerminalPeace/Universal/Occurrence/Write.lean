import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Opening
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Writer

/-!
Finite dual-signed continuation uses one original dispatcher write per
input. Native registration, material inventory and old rows share that fold.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Reparation.Actual

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Loss" => Reparation.Actual.Occurrence seed community
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Proposal" => Reparation.Actual.Input Party Good Port Technology Instrument

variable (answers : ReceiptAnswers seed) {past : Reparation.Actual.Script Party Good Port Technology Instrument}

/-- Run the existing whole-ledger dual-signed writer on each actual
input. History casts only align the native successor indices. -/
def writeAfter (state : State seed community past) (suffix : Word) :
    State seed community (past ++ suffix) :=
  List.reverseRecOn (motive := fun tail => State seed community (past ++ tail)) suffix
    ((List.append_nil past).symm ▸ state)
    (fun front input previous => List.append_assoc past front [input] ▸ Settlement.writeTick answers previous input)

theorem writeAfter_snoc (state : State seed community past) (front : Word) (input : Proposal) :
    writeAfter answers state (front ++ [input]) =
      (List.append_assoc past front [input] ▸ Settlement.writeTick answers (writeAfter answers state front) input :
        State seed community (past ++ (front ++ [input]))) := by
  rw [writeAfter, List.reverseRecOn_concat]
  rfl

private theorem cast_keeps_balances {left right : Word} (state : State seed community left) (same : left = right) :
    (same ▸ state : State seed community right).stack.balances = state.stack.balances := by
  cases same
  rfl

theorem writeAfter_nil_balances (state : State seed community past) :
    (writeAfter answers state []).stack.balances = state.stack.balances := by
  rw [writeAfter, List.reverseRecOn_nil, cast_keeps_balances]

theorem writeAfter_snoc_balances (state : State seed community past) (front : Word) (input : Proposal) :
    (writeAfter answers state (front ++ [input])).stack.balances =
      (Settlement.writeTick answers (writeAfter answers state front) input).stack.balances := by
  rw [writeAfter_snoc, cast_keeps_balances]

theorem writeAfter_origins (state : State seed community past)
    (complete : state.stack.balances.map Prod.fst = originalLosses seed community past)
    (suffix : Word) :
    (writeAfter answers state suffix).stack.balances.map Prod.fst =
      originalLosses seed community (past ++ suffix) := by
  induction suffix using List.reverseRecOn with
  | nil => rw [writeAfter_nil_balances, List.append_nil, complete]
  | append_singleton front input ih =>
    rw [writeAfter_snoc_balances, Settlement.writeTick_origins, ih, ← List.append_assoc, losses_snoc]

theorem the_original_occurrence_stays_listed (front suffix : Word) (loss : Loss)
    (listed : loss ∈ originalLosses seed community front) :
    loss ∈ originalLosses seed community (front ++ suffix) := by
  induction suffix using List.reverseRecOn with
  | nil => simpa only [List.append_nil] using listed
  | append_singleton rest input ih =>
    rw [← List.append_assoc, losses_snoc]
    exact List.mem_append_left _ ih

def reached (loss : Loss) (suffix : Word) : State seed community (history loss ++ suffix) :=
  writeAfter answers (originState loss) suffix

theorem reached_origins (loss : Loss) (suffix : Word) :
    (reached answers loss suffix).stack.balances.map Prod.fst =
      originalLosses seed community (history loss ++ suffix) :=
  writeAfter_origins answers _ (originState_origins loss) suffix

theorem reached_records_the_whole_history (loss : Loss) (suffix : Word) :
    Quantities.Recorded seed (history loss ++ suffix) :=
  Quantities.record _ _

theorem reached_has_one_row_per_original_address (loss : Loss) (suffix : Word) :
    ((reached answers loss suffix).stack.balances.map fun row => row.1.address).Nodup := by
  have distinct := one_original_loss_has_one_address_on_the_whole_trajectory seed community (history loss ++ suffix)
  rw [← reached_origins answers loss suffix] at distinct
  simpa only [List.map_map, Function.comp_def] using distinct

/-- The dispatcher also returns its native authorization or settlement
disposition, even when a real material effect must remain in the ledger. -/
def continuationApproval (loss : Loss) (suffix : Word) :
    Approval (Quantities.Execution.endAt seed (history loss)) suffix :=
  approval (Quantities.Execution.endAt seed (history loss)) suffix

#print axioms writeAfter_origins
#print axioms reached_has_one_row_per_original_address

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence
