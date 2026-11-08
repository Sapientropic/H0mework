import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AtomicWorkConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveSupplySynthesisSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RecycledQuorumMaterial (Current Action)
noncomputable section
abbrev Emitter := Code Delegation.Funded.Party Repayment.Recovery.Good Delegation.Funded.Port
  (Mandate.State Delegation.Funded.Party Bool) Unit
abbrev Word := List Action

-- These are original instructions and recipes. No post-state or successful
-- execution is supplied by the caller, including for the upstream cycle.
def donorCycle : Word := DonorRegenerationLaw.word ++ [FuelMandateLaw.give] ++ RenewedQuorumMaterial.word
def recipes : List Word := [RecycledQuorumMaterial.word,RenewedQuorumMaterial.word,
  FuelMandateLaw.word ++ RenewedQuorumMaterial.word,donorCycle]
def demand (current : Current) : Prop := current.stock 1 .service < max 0 (current.claims () 1 2)
instance (current : Current) : Decidable (demand current) := inferInstanceAs (Decidable (_ < _))
def productive (law : RawLaw Delegation.Funded.Party Repayment.Recovery.Good Delegation.Funded.Port
    (Mandate.State Delegation.Funded.Party Bool) Unit) (current : Current) (word : Word) : Prop :=
  word ≠ [] ∧ (∀ item ∈ law.rawItems current word,law.Valid item.before item.request) ∧
    current.stock 1 .service < (law.next current word).stock 1 .service
instance (law : RawLaw Delegation.Funded.Party Repayment.Recovery.Good Delegation.Funded.Port
    (Mandate.State Delegation.Funded.Party Bool) Unit) (current : Current) (word : Word) :
    Decidable (productive law current word) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

variable (old : Emitter) (saved : Cursor old)
abbrev current := (EventStep.seed saved).current
def offer : Option Word := if demand (current old saved) then
  recipes.find? (fun word => decide (productive old.law (current old saved) word)) else none
abbrev batch : Word := (offer old saved).getD []
abbrev code := AtomicWorkSource.code old (batch old saved)
abbrev start := AtomicWorkSource.cursor old (batch old saved) saved
abbrev submit (enabled : Bool) := enabled && (offer old saved).isSome
abbrev row (enabled : Bool) (rival : Opponent (code old saved)) :=
  AtomicWorkSource.row old (batch old saved) saved (submit old saved enabled) rival
abbrev next (enabled : Bool) (rival : Opponent (code old saved)) :=
  AtomicWorkSource.next old (batch old saved) saved (submit old saved enabled) rival
abbrev assess (enabled : Bool) (rival : Opponent (code old saved)) :=
  AtomicWorkSource.assess old (batch old saved) saved (submit old saved enabled) rival

theorem offered_word_is_original_legal_and_productive (word : Word) (found : offer old saved = some word) :
    demand (current old saved) ∧ word ∈ recipes ∧ productive old.law (current old saved) word := by
  unfold offer at found
  split at found
  · rename_i needed
    have paid : decide (productive old.law (current old saved) word) = true :=
      List.find?_some (p := fun candidate => decide (productive old.law (current old saved) candidate)) found
    exact ⟨needed,List.mem_of_find?_eq_some found,of_decide_eq_true paid⟩
  · contradiction

theorem seed_is_the_same_actual_current (original : saved.side = .original) :
    (EventStep.seed (start old saved)).current = current old saved :=
  congrArg (fun state => state.current)
    (CatalogueHandoffSource.seed old (AtomicWorkSource.catalogue old (batch old saved)) saved original)

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
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveSupplySynthesisSource
