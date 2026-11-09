import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Reserve
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Mandate.Root
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Horizon
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.SelectedPrimitive

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
  (Ready ReviewAvailable queued the_available_review_forwards_the_actual_requested_primitive)
open PublicFunction.Mandate
open Quantities.Execution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "L" => RawLaw Party Good Port Technology Instrument
local notation "J" => Scope (Party := Party) (Good := Good) (Port := Port)
local notation "Req" => Request Party Good Port (State Party Technology) Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port (State Party Technology) Instrument
local notation "Item" => ExecutionItem Party Good Port (State Party Technology) Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port (State Party Technology) Instrument

/-- The signed target belongs to the actual submission cut. A later
version may require a new signature, never an automatic re-signing. -/
def withdrawal (scope : J) (cut : C) (actor : Party) : Req :=
  request scope cut.raw actor .revoke

abbrev withdrawalInput (scope : J) (cut : C) (actor : Party) : Input :=
  some (.primitive (withdrawal scope cut actor))

structure FeeShortage (scope : J) (cut : C) (actor : Party) where
  good : Good
  original : ∃ quantity, (good, quantity) ∈ scope.revisionCost
  short : cut.raw.stock actor good < flowAt (locate actor scope.revisionCost) actor good

def feeShortage (scope : J) (cut : C) (actor : Party) : Option (FeeShortage scope cut actor) :=
  match Capitalism.Universal.Abolition.Material.inspectList
    (fun lot : Good × ℚ => flowAt (locate actor scope.revisionCost) actor lot.1 ≤ cut.raw.stock actor lot.1)
    scope.revisionCost with
  | .clear _ => none
  | .failure lot original denied => some ⟨lot.1, ⟨lot.2, original⟩, lt_of_not_ge denied⟩

structure ReleaseReceipt (base : L) (scope : J) (submittedCut atCut : C) (actor : Party) : Prop where
  member : actor ∈ PublicFunction.Delegation.members scope.task
  authority : (law base scope).Valid atCut.raw (withdrawal scope submittedCut actor)
  originalItem : inventory atCut [withdrawalInput scope submittedCut actor] =
    [⟨0, atCut.raw, withdrawal scope submittedCut actor⟩]
  released : Civil.Mandate.Released (next atCut (withdrawalInput scope submittedCut actor)).raw
  clock : (next atCut (withdrawalInput scope submittedCut actor)).raw.clock = atCut.raw.clock
  paid : ∀ good, (next atCut (withdrawalInput scope submittedCut actor)).raw.stock actor good +
    flowAt (locate actor scope.revisionCost) actor good = atCut.raw.stock actor good

theorem release_at_the_original_material_visit {base : L} {scope : J} {submittedCut atCut : C}
    (actor : Party) (installed : Emergency.Installed atCut base scope)
    (ready : Ready atCut) (review : ReviewAvailable atCut)
    (valid : (law base scope).Valid atCut.raw (withdrawal scope submittedCut actor)) :
    ReleaseReceipt base scope submittedCut atCut actor := by
  let req := withdrawal scope submittedCut actor
  have actual : atCut.native.input.law.Valid atCut.raw req := by
    change atCut.native.input.law = law base scope at installed
    rw [installed]
    exact valid
  have physical := PublicFunction.valid_physical _ _ _ actual
  let q := queued atCut req
  have paid := the_selected_primitive_is_paid_by_the_original_root q req ready
    (the_available_review_forwards_the_actual_requested_primitive atCut req review) rfl physical
  have raw : (next atCut (some (.primitive req))).raw = (law base scope).step atCut.raw req := by
    refine paid.1.trans ?_
    change (PublicFunction.physicalLaw atCut.native.input.law).step atCut.raw req = _
    rw [RawLaw.step, RawLaw.step, if_pos physical, if_pos valid]
    rw [show atCut.native.input.law = law base scope from installed]
    rfl
  have policy := valid.1.2
  simp only [withdrawal, request, law, RawLaw.operationAllowed, RawPolicy.eval, advance_last,
    decide_eq_true_eq] at policy
  have currentRequest : req = request scope atCut.raw actor .revoke :=
    congrArg (fun target => (⟨actor, [], scope.challenge, [scope.challenge], .revise actor target⟩ : Req))
      policy.2.2.2.2.1
  have here : (law base scope).Valid atCut.raw (request scope atCut.raw actor .revoke) :=
    currentRequest ▸ valid
  have member := ((command_policy base scope atCut.raw actor .revoke).mp here.1.2).1
  have effect := (paid_command_effect base scope atCut.raw actor .revoke here).1
  refine ⟨member, valid, paid.2.2, ?_, ?_, ?_⟩
  · rw [show withdrawalInput scope submittedCut actor = some (.primitive req) from rfl, raw, currentRequest]
    exact ⟨congrArg State.holder effect, congrArg State.offered effect⟩
  · rw [show withdrawalInput scope submittedCut actor = some (.primitive req) from rfl, raw, RawLaw.step, if_pos valid]
    rfl
  · intro good
    rw [show withdrawalInput scope submittedCut actor = some (.primitive req) from rfl, raw, currentRequest]
    have balance := (law base scope).material_step_balance atCut.raw
      (request scope atCut.raw actor .revoke) actor good
    rw [RawLaw.actualDebit, if_pos here, RawLaw.actualCredit, if_pos here] at balance
    change _ + flowAt (locate actor scope.revisionCost) actor good = _ + flowAt [] actor good at balance
    simpa only [flowAt, amount, List.map_nil, List.sum_nil, add_zero] using balance

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
