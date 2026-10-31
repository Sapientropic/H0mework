import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.Reachable

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)

structure ReceivedEvent (depth : Nat) where
  private mk ::
  incoming : IncomingWord source.seed.law (source.currentAt (depth + 1))
  generated : source.incoming? (source.currentAt (depth + 1)) = some incoming
  actual_word : (source.actualExecution depth).submitted = incoming.word
  actual_report : (source.writtenReceipt depth).val =
    .original (source.currentAt (depth + 1)) incoming.word

def receivedAt (depth : Nat) : Option (source.ReceivedEvent depth) :=
  if started : 2 ≤ depth + 1 then
    match generated : source.incoming? (source.currentAt (depth + 1)) with
      | none => none
      | some incoming => some {
          incoming := incoming
          generated := generated
          actual_word := by
            rw [source.actual_execution_word]
            unfold frameWord
            rw [if_neg (by omega), if_neg (by omega), ← (source.canonical_frame (depth + 1)).1]
            unfold decideAt
            rw [generated]
            rfl
          actual_report := by
            rw [source.written_report_exact]
            unfold reportAt
            rw [source.ordinal_exact, if_neg (by omega)]
            unfold decideAt
            rw [generated]
            rfl }
  else none

theorem admitted_input_is_received (depth : Nat) (started : 2 ≤ depth + 1)
    (incoming : IncomingWord source.seed.law (source.currentAt (depth + 1)))
    (generated : source.incoming? (source.currentAt (depth + 1)) = some incoming) :
    ∃ event, source.receivedAt depth = some event := by
  unfold receivedAt
  rw [dif_pos started]
  split
  · rename_i absent
    rw [absent] at generated
    cases generated
  · exact ⟨_, rfl⟩

theorem ReceivedEvent.actual_word_is_nonempty {depth : Nat} (event : source.ReceivedEvent depth) :
    (source.actualExecution depth).submitted ≠ [] := by
  rw [event.actual_word]
  exact event.incoming.nonempty

theorem ReceivedEvent.actual_items_are_accepted {depth : Nat} (event : source.ReceivedEvent depth) :
    ∀ item ∈ (source.actualExecution depth).interpreted.items,
      source.seed.law.Valid item.before item.request := by
  change ∀ item ∈ source.seed.law.rawItems (source.currentAt (depth + 1))
    (source.actualExecution depth).submitted, _
  rw [event.actual_word]
  exact event.incoming.accepted

theorem ReceivedEvent.preserves_original_archive {depth : Nat} (event : source.ReceivedEvent depth)
    (index : source.Slot) (paid : Nat)
    (recorded : (source.frameAt (depth + 1)).payments index = some paid) :
    (source.frameAt (depth + 2)).payments index = some paid := by
  rw [source.next_payments_are_actual_update, event.actual_word]
  exact source.payment_preserved _ _ _ _ index paid recorded

end SaturationMonoid.ProcessGame.Society.PublicFunction.OutstandingSource
