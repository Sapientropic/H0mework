import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PartyCursorControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveExternalSupplySource
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open WholeCursorLaw
open Repayment.Recovery (Good)
abbrev Emitter := Code Party Good Port (Mandate.State Party Bool) Unit
abbrev Word := List Action

-- These are source instructions. The supplier's primitive inputs are paid in the same word.
def preparation : List RecycledQuorumMaterial.Action :=
  DonorRegenerationLaw.word ++ [FuelMandateLaw.give] ++ RenewedQuorumMaterial.supply
def recipes : List Word := [cycle,(RenewedQuorumMaterial.supply.map WholePartyLift.request) ++ cycle,
  (preparation.map WholePartyLift.request) ++ cycle]
abbrev position : Repayment.Position Party Unit := ⟨(),producer,creditor⟩
variable (old : Emitter) (saved : Cursor old)
abbrev current := (EventStep.seed saved).current

def addresses : List Nat := (List.range (EventStep.seed saved).frame.sent.length).filter
  fun serial => decide (.deliver serial ∈ old.eventAlphabet)
def fees : Word := (addresses old saved).flatMap fun serial =>
  match (EventStep.seed saved).frame.sent[serial]? with
  | none => [] | some packet => old.deliveryCost packet.recipient
abbrev intermediate (front : Word) := (old.law.execute (current old saved) 0 front).final
def reserve (front : Word) : ℚ := max 0 (((old.law.rawItems (intermediate old saved front) (fees old saved)).map
  fun item => flowAt (old.law.debit item.before item.request) producer (old.law.settlementUnit ())).sum)
def quantity (front : Word) : ℚ := min (max 0 (Repayment.balance position (intermediate old saved front)))
  (max 0 (((intermediate old saved front).stock producer (old.law.settlementUnit ()) - reserve old saved front) /
    old.law.settlementRate ()))
def payment (front : Word) : Word := if 0 < quantity old saved front then
  [⟨producer,[],old.law.issuerPort (),[],.settle () producer creditor (quantity old saved front)⟩] else []
def assembled (front : Word) : Word := front ++ payment old saved front

def needed : Prop := (current old saved).stock producer .service <
  max 0 (Repayment.balance position (current old saved)) + reserve old saved []
instance : Decidable (needed old saved) := inferInstanceAs (Decidable (_ < _))

def admissible (front : Word) : Prop :=
  (∀ item ∈ old.law.rawItems (current old saved) (assembled old saved front),old.law.Valid item.before item.request) ∧
  (current old saved).stock producer .service < (intermediate old saved front).stock producer .service ∧
  Repayment.balance position (intermediate old saved front) = Repayment.balance position (current old saved) ∧
  (∀ item ∈ old.law.rawItems (old.law.next (current old saved) (assembled old saved front)) (fees old saved),
    old.law.Valid item.before item.request)
instance (front : Word) : Decidable (admissible old saved front) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def offer : Option Word := if needed old saved then recipes.find? (fun front => decide (admissible old saved front)) else none
def batch : Word := match offer old saved with | none => [] | some front => assembled old saved front
abbrev code := AtomicWorkSource.code old (batch old saved)
abbrev start := AtomicWorkSource.cursor old (batch old saved) saved
abbrev submit (enabled : Bool) := enabled && (offer old saved).isSome
abbrev work (enabled : Bool) := AtomicWorkSource.protocol old (batch old saved) (submit old saved enabled)
abbrev row (enabled : Bool) (rival : Opponent (code old saved)) :=
  AtomicWorkSource.row old (batch old saved) saved (submit old saved enabled) rival
abbrev next (enabled : Bool) (rival : Opponent (code old saved)) :=
  AtomicWorkSource.next old (batch old saved) saved (submit old saved enabled) rival
abbrev assess (enabled : Bool) (rival : Opponent (code old saved)) :=
  AtomicWorkSource.assess old (batch old saved) saved (submit old saved enabled) rival

inductive Selection where
  | idle | unavailable | withheld | offered
  deriving DecidableEq

def selection (enabled : Bool) : Selection := if needed old saved then
  match offer old saved with
  | none => .unavailable
  | some _ => if enabled then .offered else .withheld
  else .idle

theorem selected_is_generated_from_the_actual_source (front : Word) (found : offer old saved = some front) :
    needed old saved ∧ front ∈ recipes ∧ admissible old saved front := by
  unfold offer at found
  split at found
  · rename_i demand
    exact ⟨demand,List.mem_of_find?_eq_some found,of_decide_eq_true (List.find?_some (p := fun candidate => decide (admissible old saved candidate)) found)⟩
  · contradiction

-- Each stage retains its actual cursor, including refusals and external intervention.
structure Snapshot where
  emitter : Emitter
  cursor : Cursor emitter
abbrev nextCode (state : Snapshot) := code state.emitter state.cursor
structure Command (state : Snapshot) where
  enabled : Bool
  rival : Opponent (nextCode state)
def step (state : Snapshot) (command : Command state) : Snapshot :=
  ⟨nextCode state,next state.emitter state.cursor command.enabled command.rival⟩
abbrev Controller := (state : Snapshot) → Command state
def run (initial : Snapshot) (controller : Controller) : Nat → Snapshot :=
  Nat.rec initial fun _ state => step state (controller state)
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveExternalSupplySource
