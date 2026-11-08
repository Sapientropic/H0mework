import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveSupplySynthesisConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveRepaymentSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open LiveSupplySynthesisSource (Emitter Word current)
noncomputable section
abbrev position : Repayment.Position Delegation.Funded.Party Unit := ⟨(),1,2⟩
variable (old : Emitter) (saved : Cursor old)
def prefixes : List Word := if LiveSupplySynthesisSource.demand (current old saved) then
  LiveSupplySynthesisSource.recipes ++ [[]] else [[]]
-- The repayment compiler consumes the raw front endpoint. A separate next
-- would add a clock/round that this single actual batch never incurred.
abbrev intermediate (front : Word) := (old.law.execute (current old saved) 0 front).final
def assembled (front : Word) : Word := front ++
  Repayment.candidate old.law position (intermediate old saved front)
def admissible (front : Word) : Prop :=
  Repayment.Ready old.law position (intermediate old saved front) ∧
    Repayment.balance position (intermediate old saved front) = Repayment.balance position (current old saved) ∧
      ∀ item ∈ old.law.rawItems (current old saved) (assembled old saved front),old.law.Valid item.before item.request
instance (front : Word) : Decidable (admissible old saved front) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def offer : Option Word := (prefixes old saved).find? fun front => decide (admissible old saved front)
def batch : Word := match offer old saved with | none => [] | some front => assembled old saved front
abbrev code := AtomicWorkSource.code old (batch old saved)
abbrev start := AtomicWorkSource.cursor old (batch old saved) saved
abbrev submit (enabled : Bool) := enabled && (offer old saved).isSome
abbrev row (enabled : Bool) (rival : Opponent (code old saved)) :=
  AtomicWorkSource.row old (batch old saved) saved (submit old saved enabled) rival
abbrev next (enabled : Bool) (rival : Opponent (code old saved)) :=
  AtomicWorkSource.next old (batch old saved) saved (submit old saved enabled) rival
abbrev assess (enabled : Bool) (rival : Opponent (code old saved)) :=
  AtomicWorkSource.assess old (batch old saved) saved (submit old saved enabled) rival

theorem the_source_offer_is_an_original_repayment_compilation (front : Word)
    (found : offer old saved = some front) : front ∈ prefixes old saved ∧ admissible old saved front := by
  have paid : decide (admissible old saved front) = true :=
    List.find?_some (p := fun word => decide (admissible old saved word)) found
  exact ⟨List.mem_of_find?_eq_some found,of_decide_eq_true paid⟩

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
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveRepaymentSource
