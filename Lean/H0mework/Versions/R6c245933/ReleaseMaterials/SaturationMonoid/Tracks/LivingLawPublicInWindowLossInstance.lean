import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.Tracks.LivingLawPublicInWindowLossInstance
open ProcessGame.Society.PublicFunction Mandate Mandate.Financed Mandate.Financed.Continuing
open Mandate.Financed.Continuing.Closure Objection Objection.Followup Objection.Opening ScopeRevision.Pending.Joint.Handoff
open ScopeRevision ScopeRevision.Pending.Joint
open ProcessGame.Society.Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
noncomputable section
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs) (original : List Action) (count : Nat)

abbrev publicInWindowLossFacade := Registered.Loss.Runtime.facade authority inventory fresh original count

theorem the_original_source_consumes_the_dynamic_book_all_native_states_and_its_own_next :
    (Registered.Loss.Runtime.fromRoot authority inventory fresh original count).initial =
      Registered.Finance.Runtime.fromRoot authority inventory fresh original ∧
    (Registered.Loss.Runtime.fromRoot authority inventory fresh original count).cursor =
      Registered.Loss.cursorAt authority inventory fresh original count ∧
    (Registered.Loss.Runtime.fromRoot authority inventory fresh original count).continuation =
      Registered.Loss.Source.runFinancial (Registered.Loss.initial authority inventory fresh original) count ∧
    (∀ actor good, (Registered.Loss.Runtime.fromRoot authority inventory fresh original count).unpaid actor good +
      (Registered.Loss.Runtime.fromRoot authority inventory fresh original count).allocated actor good =
      (Registered.Loss.Runtime.fromRoot authority inventory fresh original count).originalQuantity actor good) ∧
    (Registered.Loss.Runtime.root authority inventory fresh original count).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (Registered.Loss.I authority inventory fresh original count)).toAuthoritativeRoot.toRoot ∧
    HEq (publicInWindowLossFacade authority inventory fresh original count |>.readoutAt
      (Registered.Loss.Runtime.activated authority inventory fresh original count (Registered.Loss.ordinal authority inventory fresh original count)) .lossAccount)
      ((Registered.Loss.Runtime.activated authority inventory fresh original count (Registered.Loss.ordinal authority inventory fresh original count)).tick.generated.projectionOutcome (.component ())) ∧
    HEq (Registered.Loss.Runtime.activated authority inventory fresh original count (Registered.Loss.ordinal authority inventory fresh original count)).tick.generated.wholeLedgerWriteBack
      ((Registered.Loss.Runtime.activated authority inventory fresh original count (Registered.Loss.ordinal authority inventory fresh original count)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (Registered.Loss.Runtime.activated authority inventory fresh original count (Registered.Loss.ordinal authority inventory fresh original count)).current.visit.current) ∧
    (Registered.Loss.Runtime.activated authority inventory fresh original count (Registered.Loss.ordinal authority inventory fresh original count)).tick.nextCurrent =
      (Registered.Loss.Runtime.process authority inventory fresh original count).stateAt
        ((Registered.Loss.Runtime.process authority inventory fresh original count).successor
          (Registered.Loss.Runtime.activated authority inventory fresh original count (Registered.Loss.ordinal authority inventory fresh original count)).state) := by
  have factor := (Registered.Loss.Runtime.facade authority inventory fresh original count).readoutAt_factorizes
    (Registered.Loss.Runtime.activated authority inventory fresh original count (Registered.Loss.ordinal authority inventory fresh original count)) .lossAccount
  refine ⟨rfl,rfl,rfl,?_,rfl,factor.2.2.2.1,factor.2.2.1,factor.2.2.2.2⟩
  intro actor good
  exact Registered.Loss.the_complete_dynamic_book_has_one_original_quantity _ actor good

variable {authority inventory fresh original}
private theorem nextOrigins (cursor : Registered.Loss.Cursor authority inventory fresh original) :
    cursor.book.map Registered.Loss.Entry.visit <+: cursor.next.book.map Registered.Loss.Entry.visit := by
  rw [show cursor.next.book.map Registered.Loss.Entry.visit =
    cursor.book.map Registered.Loss.Entry.visit ++ [Registered.Loss.visit cursor.state cursor.word] from
      cursor.every_actual_input_keeps_all_prior_origins_and_adds_its_own cursor.word]
  exact List.prefix_append _ _

private theorem reactionOrigins (cursor : Registered.Loss.Cursor authority inventory fresh original) (actor : Bool) :
    cursor.book.map Registered.Loss.Entry.visit <+:
      (Registered.Loss.Source.reaction cursor actor).book.map Registered.Loss.Entry.visit := by
  unfold Registered.Loss.Source.reaction
  split
  · exact List.prefix_rfl
  · rw [cursor.every_actual_input_keeps_all_prior_origins_and_adds_its_own]
    exact List.prefix_append _ _

private theorem advanceOrigins (cursor : Registered.Loss.Cursor authority inventory fresh original) :
    cursor.book.map Registered.Loss.Entry.visit <+:
      (Registered.Loss.Source.advance cursor).book.map Registered.Loss.Entry.visit := by
  unfold Registered.Loss.Source.advance
  split
  · exact (nextOrigins cursor).trans (reactionOrigins cursor.next _)
  · exact nextOrigins cursor
  · exact nextOrigins cursor

theorem every_finite_actual_repair_and_refusal_reaction_preserves_all_original_occurrences
    (cursor : Registered.Loss.Cursor authority inventory fresh original) (count : Nat) :
    cursor.book.map Registered.Loss.Entry.visit <+:
      (Registered.Loss.Source.run cursor count).book.map Registered.Loss.Entry.visit := by
  induction count with
  | zero => exact List.prefix_rfl
  | succ count ih => exact ih.trans (advanceOrigins _)

variable (authority inventory fresh original)
theorem the_original_paid_input_is_never_replayed_or_replaced_in_the_tail (count : Nat) :
    Registered.inputs authority inventory fresh original <+:
      (Registered.Loss.Runtime.fromRoot authority inventory fresh original count).cursor.state.inputs :=
  (Registered.Loss.cursorAt authority inventory fresh original count).state.paidPast

namespace Actual
open Registered.Loss.Regression

theorem the_public_source_book_really_generates_and_materially_reduces_the_original_positive_cell :
    ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Raw.quantity originalEntry.original (false,.service) = 3 ∧
    cell afterPayment.book = some (3,0) :=
  ⟨the_original_public_history_generates_its_own_positive_loss.1,
    the_actual_source_reparation_pays_all_three.1⟩
end Actual
end
end SaturationMonoid.Tracks.LivingLawPublicInWindowLossInstance
