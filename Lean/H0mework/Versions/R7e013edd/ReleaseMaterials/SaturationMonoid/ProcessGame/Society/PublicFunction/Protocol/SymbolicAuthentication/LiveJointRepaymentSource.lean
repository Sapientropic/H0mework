import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveRepaymentConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveJointRepaymentSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open LiveSupplySynthesisSource (Emitter Word current)
open LiveRepaymentSource (position)
noncomputable section
variable (old : Emitter) (saved : Cursor old)

-- Reserve one original transport attempt for every stored, admitted address.
-- A transport reserve neither asserts freshness nor mints a receipt.
def addresses : List Nat := (List.range (EventStep.seed saved).frame.sent.length).filter
  fun serial => decide (.deliver serial ∈ old.eventAlphabet)
def fees : Word := (addresses old saved).flatMap fun serial =>
  match (EventStep.seed saved).frame.sent[serial]? with
  | none => []
  | some packet => old.deliveryCost packet.recipient
abbrev prepared (front : Word) : Word := front ++ Repayment.preparation old.law position
  (LiveRepaymentSource.intermediate old saved front)
abbrev beforePayment (front : Word) := (old.law.execute (current old saved) 0 (prepared old saved front)).final
def reserve (front : Word) : ℚ := max 0 (((old.law.rawItems (beforePayment old saved front) (fees old saved)).map
  fun item => flowAt (old.law.debit item.before item.request) 1 (old.law.settlementUnit ()) ).sum)
def quantity (front : Word) : ℚ := min (Repayment.balance position (beforePayment old saved front))
  (max 0 (((beforePayment old saved front).stock 1 (old.law.settlementUnit ()) - reserve old saved front) /
    old.law.settlementRate ()))
def payment (front : Word) : RecycledQuorumMaterial.Action :=
  ⟨1,[],old.law.issuerPort (),[],.settle () 1 2 (quantity old saved front)⟩
def assembled (front : Word) : Word := prepared old saved front ++ [payment old saved front]
def admissible (front : Word) : Prop :=
  0 < quantity old saved front ∧
    Repayment.balance position (beforePayment old saved front) = Repayment.balance position (current old saved) ∧
    old.law.Valid (beforePayment old saved front) (payment old saved front) ∧
    (∀ item ∈ old.law.rawItems (current old saved) (assembled old saved front),old.law.Valid item.before item.request) ∧
    (∀ item ∈ old.law.rawItems (old.law.next (current old saved) (assembled old saved front)) (fees old saved),
      old.law.Valid item.before item.request)
instance (front : Word) : Decidable (admissible old saved front) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))
def offer : Option Word := (LiveRepaymentSource.prefixes old saved).find? fun front => decide (admissible old saved front)
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

theorem selected_is_computed_from_the_original_supply_and_delivery_words (front : Word)
    (found : offer old saved = some front) :
    front ∈ LiveRepaymentSource.prefixes old saved ∧ admissible old saved front := by
  have paid : decide (admissible old saved front) = true :=
    List.find?_some (p := fun word => decide (admissible old saved word)) found
  exact ⟨List.mem_of_find?_eq_some found,of_decide_eq_true paid⟩

theorem seed_is_the_same_actual_current (original : saved.side = .original) :
    (EventStep.seed (start old saved)).current = current old saved :=
  congrArg (fun state => state.current)
    (CatalogueHandoffSource.seed old (AtomicWorkSource.catalogue old (batch old saved)) saved original)
end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveJointRepaymentSource
