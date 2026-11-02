import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Projection
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Distributed.Reaction.Native.Future.Recovery
abbrev State := Recovery.Projection.State
variable (epoch : Epoch)

def quote (state : State) (actor : Bool) :=
  (Search.Billing.tariffs (Tariff.context epoch state.inputs) actor).head?
def attempt (state : State) (fee : Action) (count : Nat) :=
  Mandate.Replay.Repeated.generate base epoch.scope (current epoch state.inputs) fee count
def charged (state : State) (fee : Action) (count : Nat) : State :=
  ⟨state.inputs ++ [(attempt epoch state fee count).output],state.consumed,state.residual⟩
def catalogue (state : State) (actor : Bool) :=
  Search.catalogue (Recovery.Projection.context epoch state.inputs) (current epoch state.inputs) actor state.residual
def units (state : State) (actor : Bool) (fee : Action) :=
  let built := charged epoch state fee 1
  Search.Counting.comparisonUnits (Recovery.Projection.context epoch built.inputs)
    (current epoch built.inputs) actor state.residual

theorem units_is_original (state : State) (actor : Bool) (fee : Action) : units epoch state actor fee =
    Search.Billing.comparisonUnits state.residual (catalogue epoch (charged epoch state fee 1) actor) :=
  Search.Counting.comparisonUnits_is_original _ _ _ _
def compared (state : State) (actor : Bool) (fee : Action) :=
  charged epoch (charged epoch state fee 1) fee (units epoch state actor fee)
def restored (state : State) (actor : Bool) (fee : Action) : State :=
  let staged := compared epoch state actor fee
  let model := Recovery.Projection.context epoch staged.inputs
  let before := current epoch staged.inputs
  let chosen := Search.Billing.choose model before staged.residual
    (catalogue epoch (charged epoch state fee 1) actor)
  let retry := chosen.retry model before staged.residual
  ⟨staged.inputs ++ [chosen.word model before staged.residual],staged.consumed ++ retry.consumed,retry.residual⟩

inductive Kind where
  | finished | unpriced | constructionRefused | comparisonRefused | searched
  deriving DecidableEq, Repr
structure Observation where
  kind : Kind
  state : State

def run (state : State) : Observation :=
  match state.residual with
  | [] => ⟨.finished,state⟩
  | head::_ => match quote epoch state head.signer with
    | none => ⟨.unpriced,state⟩
    | some fee =>
      if (attempt epoch state fee 1).succeeded then
        if (attempt epoch (charged epoch state fee 1) fee (units epoch state head.signer fee)).succeeded then
          ⟨.searched,restored epoch state head.signer fee⟩
        else ⟨.comparisonRefused,compared epoch state head.signer fee⟩
      else ⟨.constructionRefused,charged epoch state fee 1⟩

def produce (inputs : List (List Action)) (word : List Action) :=
  run epoch (Recovery.Projection.begin epoch inputs word)

noncomputable section
variable {epoch} {inventory : Inventory epoch} {word : List Action}

def read {cursor : Recovery.Cursor inventory word} (result : Metering.Result cursor) : Observation :=
  ⟨(match result with
    | .finished .. => .finished
    | .unpriced .. => .unpriced
    | .constructionRefused .. => .constructionRefused
    | .comparisonRefused .. => .comparisonRefused
    | .searched .. => .searched),Recovery.Projection.read result.finish⟩

theorem quote_is_the_actual_source_directory (cursor : Recovery.Cursor inventory word) (actor : Bool) :
    quote epoch (Recovery.Projection.read cursor) actor = (Metering.quote cursor actor).map Metering.Fee.request := by
  change (Search.Billing.tariffs (Metering.feeContext cursor) actor).head? = _
  rw [←Metering.fee_projection_is_the_complete_source_tariff_list,List.head?_map]
  rfl

theorem run_is_the_actual_billed_stage (cursor : Recovery.Cursor inventory word) :
    run epoch (Recovery.Projection.read cursor) = read (Metering.run cursor) := by
  unfold Metering.run
  split
  next empty =>
    unfold run
    change (match cursor.residual with | [] => _ | _::_ => _) = _
    conv_lhs => rw [empty]
    rfl
  next head tail pending =>
    split
    next absent =>
      unfold run
      change (match cursor.residual with | [] => _ | _::_ => _) = _
      conv_lhs => rw [pending];dsimp only;rw [quote_is_the_actual_source_directory,absent]
      rfl
    next fee quoted =>
      split
      next paid =>
        split
        next compared =>
          unfold run
          change (match cursor.residual with | [] => _ | _::_ => _) = _
          conv_lhs => rw [pending];dsimp only;rw [quote_is_the_actual_source_directory,quoted]
          dsimp only [Option.map_some]
          change (if (Metering.attempt fee.request 1 cursor).succeeded = true then _ else _) = _
          rw [if_pos paid]
          change (if (Metering.attempt fee.request (Metering.units cursor head.signer fee.request)
            (Metering.construction cursor fee.request)).succeeded = true then _ else _) = _
          rw [if_pos compared]
          rfl
        next refused =>
          unfold run
          change (match cursor.residual with | [] => _ | _::_ => _) = _
          conv_lhs => rw [pending];dsimp only;rw [quote_is_the_actual_source_directory,quoted]
          dsimp only [Option.map_some]
          change (if (Metering.attempt fee.request 1 cursor).succeeded = true then _ else _) = _
          rw [if_pos paid]
          change (if (Metering.attempt fee.request (Metering.units cursor head.signer fee.request)
            (Metering.construction cursor fee.request)).succeeded = true then _ else _) = _
          rw [if_neg refused]
          rfl
      next refused =>
        unfold run
        change (match cursor.residual with | [] => _ | _::_ => _) = _
        conv_lhs => rw [pending];dsimp only;rw [quote_is_the_actual_source_directory,quoted]
        dsimp only [Option.map_some]
        change (if (Metering.attempt fee.request 1 cursor).succeeded = true then _ else _) = _
        rw [if_neg refused]
        rfl

theorem the_observation_is_consumed_by_the_original_root (inventory : Inventory epoch) (word : List Action) :
    produce epoch inventory.inputs word = read (Metering.Runtime.read inventory word).result := by
  unfold produce
  rw [Recovery.Projection.begin_is_the_actual_refused_input,run_is_the_actual_billed_stage]
  rfl
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Projection
