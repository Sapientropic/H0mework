import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Charge
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code))
  (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev feeRule := Charge.feeRule quote model worker original
abbrev past := [feeRule model original worker quote]

inductive Condition where
  | space
  | payer (world : Replanning.Point model domain)

def conditions : List (Condition model domain) := .space :: (Replanning.points model domain).map .payer

def payable (condition : Condition model domain) : Prop :=
  match condition with
  | .space => 1 ≤ horizon domain
  | .payer world =>
      Distributed.Recall.Information.Agency.ownerAt model.source.code world.val.ownerStart (Cut.seed world.val).history.length = some worker ∧
      Cut.Ready worker (Replay.inspect worker (Charge.fee quote)
        (⟨world.val,⟨arrival world.val,by omega⟩⟩ : View (code := model.source.code)) Replay.PublicDomain.silent)

instance (condition : Condition model domain) : Decidable (payable model domain worker quote condition) := by
  unfold payable
  cases condition <;> infer_instance

abbrev Gate := ∀ condition ∈ conditions model domain,payable model domain worker quote condition

inductive Result where
  | obstructed (condition : Condition model domain) (generated : condition ∈ conditions model domain)
      (unpaid : ¬ payable model domain worker quote condition)
  | searched (funded : Gate model domain worker quote)
      (outcome : Prefix.Outcome model domain original (past model original worker quote) reference)

variable (point : View (code := model.source.code)) (rival : Opponent model.source.code)

/-- Catalogue construction consumes this actual source's released resource receipt.
Every candidate already contains the same paid prefix when it is compared. -/
def produce (ordinal : Nat) (_paid : Charge.paid quote model worker point rival ordinal) :
    Result model domain original reference worker quote :=
  match Distributed.inspect (payable model domain worker quote) (conditions model domain) with
  | .rejected condition generated unpaid => .obstructed condition generated unpaid
  | .accepted funded => .searched funded (Prefix.compile model domain original (past model original worker quote) reference)

def available (ordinal : Nat) : Option (Result model domain original reference worker quote) :=
  match seen : (Charge.read quote model worker point rival ordinal).1 with
  | some (.accepted checked) => some (produce model domain original reference worker quote point rival ordinal ⟨checked,seen⟩)
  | _ => none

theorem every_released_search_is_generated_after_its_own_actual_payment
    (ordinal : Nat) (result : Result model domain original reference worker quote)
    (released : available model domain original reference worker quote point rival ordinal = some result) :
    ∃ paid : Charge.paid quote model worker point rival ordinal,
      result = produce model domain original reference worker quote point rival ordinal paid := by
  unfold available at released
  split at released
  · rename_i checked seen
    exact ⟨⟨checked,seen⟩,(Option.some.inj released).symm⟩
  · cases released

theorem no_unpaid_search_or_empty_search_certificate
    (ordinal : Nat) (unpaid : ¬ Charge.paid quote model worker point rival ordinal) :
    available model domain original reference worker quote point rival ordinal = none := by
  cases seen : available model domain original reference worker quote point rival ordinal with
  | none => rfl
  | some result =>
      obtain ⟨paid,_⟩ := every_released_search_is_generated_after_its_own_actual_payment model domain original reference worker quote point rival ordinal result seen
      exact False.elim (unpaid paid)

theorem every_selected_plan_keeps_its_paid_fee_prefix
    (funded : Gate model domain worker quote)
    (choice : Prefix.Choice model domain original (past model original worker quote) reference) :
    choice.policy.protocol.controls.take 1 = past model original worker quote := by
  exact Prefix.the_selected_plan_really_preserves_the_committed_control_prefix
    model domain original (past model original worker quote) reference choice (funded .space List.mem_cons_self)

theorem every_generated_search_has_the_full_original_future_contract
    (outcome : Prefix.Outcome model domain original (past model original worker quote) reference) :
    Prefix.Contract model domain original (past model original worker quote) reference outcome :=
  Prefix.every_generated_outcome_has_the_complete_future_contract model domain original (past model original worker quote) reference outcome

theorem every_selected_world_really_pays_the_search_under_every_current_opponent
    (funded : Gate model domain worker quote) (world : Replanning.Point model domain)
    (external : Opponent model.source.code) :
    Cut.Ready worker (Replay.inspect worker (Charge.fee quote)
      (⟨world.val,⟨arrival world.val,by omega⟩⟩ : View (code := model.source.code)) external) := by
  have charged := funded (.payer world) (List.mem_cons_of_mem _
    (List.mem_map.mpr ⟨world,Replanning.every_point_is_source_generated model domain world,rfl⟩))
  exact Prepaid.Receipt.a_local_paid_receipt_survives_every_current_adaptive_opponent _ worker charged.1
    (Charge.fee quote) Replay.PublicDomain.silent external charged.2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search
