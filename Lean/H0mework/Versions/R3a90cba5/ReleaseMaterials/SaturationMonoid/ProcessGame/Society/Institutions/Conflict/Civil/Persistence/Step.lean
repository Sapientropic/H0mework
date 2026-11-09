import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Window

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "W" => Window Party Good Port Technology Instrument
local notation "Input" => Option (Compile.RawInput Party Good Port Technology Instrument)
local notation "Item" => ExecutionItem Party Good Port Technology Instrument
local notation "Req" => Request Party Good Port Technology Instrument
local notation "Cell" => Party × Use × Good × ℚ
local notation "items" => Boundary.Actual.items

/-- A scheduler request has no party signature. Code and review fees keep
their raw signers even when the scheduler has prior native work to do. -/
def signedRequests : Input → RawEvent Party Good Port Technology Instrument
  | some (.primitive request) => [request]
  | some (.execute word) => word
  | some (.migrate pair) => pair.1 ++ pair.2
  | some (.code submission) => submission.requests
  | some (.review code) => [code.fee]
  | _ => []

def OwnSignature (cut : C) (command : List Party) (request : Req) : Prop :=
  request.signer ∈ cut.members ∧ request.signer ∉ command ∧ request.consents = []

instance (cut : C) (command : List Party) (request : Req) :
    Decidable (OwnSignature cut command request) := by
  unfold OwnSignature
  infer_instance

/-- Civilian proposals must be theirs both before dispatch and at the
original legal and material gates. A rival's rejected proposal remains an
actual native tick and cannot be mistaken for a committed attack. -/
structure StepGood (origin : C) (command : List Party) (community : Party → Community)
    (civil : Bool) (window : W) (input : Input) : Prop where
  safe : ∀ _ : Boundary.Actual.DamageAt window.current input community, False
  standing : ∀ person ∈ window.residents origin command, person ∈ (window.nextCut input).members
  signatures : civil = true → ∀ request ∈ signedRequests input, OwnSignature window.current command request
  originalAuthority : civil = true → ∀ item ∈ items window.current input, OwnMaterial window.current command item
  onTime : window.crosses input → (window.nextCut input).raw.clock ≤ window.deadline
  paid : window.crosses input → window.Pays origin command input

theorem StepGood.protects_the_current_civilian_at_their_due_tick
    {origin : C} {command : List Party} {community : Party → Community}
    {civil : Bool} {window : W} {input : Input} (good : StepGood origin command community civil window input)
    (cell : Cell) (due : cell ∈ Quantities.Demand.requirements window.current)
    (present : cell.1 ∈ Civil.protectedMembers window.current command) (crossed : window.crosses input) :
    cell.1 ∈ (window.nextCut input).members ∧ cell.2.2.2 ≤ window.timely command input cell :=
  ⟨good.standing _ (Window.includes_current_resident origin command window present),
    good.paid crossed cell (Window.includes_current_need origin command window due present)⟩

inductive StepFailure (origin : C) (command : List Party) (community : Party → Community)
    (civil : Bool) (window : W) (input : Input)
  | attack (damage : Boundary.Actual.DamageAt window.current input community)
  | standing (person : Party) (original : person ∈ window.residents origin command)
      (lost : person ∉ (window.nextCut input).members)
  | signature (own : civil = true) (request : Req) (original : request ∈ signedRequests input)
      (refused : ¬ OwnSignature window.current command request)
  | material (own : civil = true) (item : Item) (original : item ∈ items window.current input)
      (refused : ¬ OwnMaterial window.current command item)
  | missedDeadline (crossed : window.crosses input) (late : window.deadline < (window.nextCut input).raw.clock)
  | shortage (crossed : window.crosses input) (cell : Cell)
      (original : cell ∈ window.cells origin command)
      (short : window.timely command input cell < cell.2.2.2)

theorem StepFailure.refutes {origin : C} {command : List Party} {community : Party → Community}
    {civil : Bool} {window : W} {input : Input} (issue : StepFailure origin command community civil window input) :
    ¬ StepGood origin command community civil window input := by
  intro good
  cases issue with
  | attack damage => exact good.safe damage
  | standing person original lost => exact lost (good.standing person original)
  | signature own request original refused => exact refused (good.signatures own request original)
  | material own item original refused => exact refused (good.originalAuthority own item original)
  | missedDeadline crossed late => exact (not_le_of_gt late) (good.onTime crossed)
  | shortage crossed cell original short => exact (not_le_of_gt short) (good.paid crossed cell original)

private def inspectWindow (origin : C) (command : List Party) (community : Party → Community)
    (civil : Bool) (window : W) (input : Input)
    (safe : ∀ _ : Boundary.Actual.DamageAt window.current input community, False)
    (standing : ∀ person ∈ window.residents origin command, person ∈ (window.nextCut input).members)
    (signatures : civil = true → ∀ request ∈ signedRequests input, OwnSignature window.current command request)
    (authority : civil = true → ∀ item ∈ items window.current input, OwnMaterial window.current command item) :
    StepFailure origin command community civil window input ⊕ PLift (StepGood origin command community civil window input) :=
  if crossed : window.crosses input then
    if timely : (window.nextCut input).raw.clock ≤ window.deadline then
      match Material.inspectList (fun cell : Cell => cell.2.2.2 ≤ window.timely command input cell)
          (window.cells origin command) with
      | .failure cell original unpaid => .inl (.shortage crossed cell original (lt_of_not_ge unpaid))
      | .clear paid => .inr ⟨⟨safe, standing, signatures, authority, fun _ => timely, fun _ => paid⟩⟩
    else .inl (.missedDeadline crossed (lt_of_not_ge timely))
  else .inr ⟨⟨safe, standing, signatures, authority, fun h => (crossed h).elim, fun h => (crossed h).elim⟩⟩

def inspectStep (origin : C) (command : List Party) (community : Party → Community)
    (civil : Bool) (window : W) (input : Input) :
    StepFailure origin command community civil window input ⊕ PLift (StepGood origin command community civil window input) := by
  let losses := Boundary.Actual.damages window.current input community
  cases found : losses with
  | cons damage rest => exact .inl (.attack damage)
  | nil =>
    have safe (damage : Boundary.Actual.DamageAt window.current input community) : False := by
      have listed := Boundary.Actual.every_actual_debit_is_assessed damage
      change damage ∈ losses at listed
      exact List.not_mem_nil (found ▸ listed)
    exact match Material.inspectList (fun person => person ∈ (window.nextCut input).members)
        (window.residents origin command) with
    | .failure person original lost => .inl (.standing person original lost)
    | .clear standing =>
      if own : civil = true then
        match Material.inspectList (OwnSignature window.current command) (signedRequests input) with
        | .failure request original denied => .inl (.signature own request original denied)
        | .clear signatures =>
          match Material.inspectList (OwnMaterial window.current command) (items window.current input) with
          | .failure item original denied => .inl (.material own item original denied)
          | .clear authority => inspectWindow origin command community civil window input safe standing
              (fun _ => signatures) (fun _ => authority)
      else inspectWindow origin command community civil window input safe standing
        (fun h => (own h).elim) (fun h => (own h).elim)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence
