import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Effects

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation

open Institutions.Capitalism.Universal.Source.Program

def registerBefore (shared : Bool) (ordinal : Nat) (item : Born.Item) : Register :=
  ((itemsAt shared ordinal).take item.index).foldl update (frameAt shared ordinal).register

structure Message (shared : Bool) where
  ordinal : Nat
  item : Born.Item
  original : item ∈ itemsAt shared ordinal
  actor : Party
  command : Command
  decoded : decode item.request = some (actor, command)
  member : actor ∈ ([1, 2] : List Party)
  permitted : CanRun (registerBefore shared ordinal item actor) command
  later : 11 ≤ ordinal

def messagesAt (shared : Bool) (ordinal : Nat) : List (Message shared) :=
  (itemsAt shared ordinal).attach.filterMap fun item =>
    match decoded : decode item.val.request with
    | none => none
    | some (actor, command) =>
      if checked : actor ∈ ([1, 2] : List Party) ∧
          CanRun (registerBefore shared ordinal item.val actor) command ∧ 11 ≤ ordinal then
        some ⟨ordinal, item.val, item.property, actor, command, decoded, checked.1, checked.2.1, checked.2.2⟩
      else none

theorem joining_message_exists : ∀ shared : Bool, (messagesAt shared 12).isEmpty = false := by
  decide +kernel

def joining (shared : Bool) : Message shared :=
  (messagesAt shared 12).head (List.isEmpty_eq_false_iff.mp (joining_message_exists shared))

theorem joining_is_an_actual_paid_choice : ∀ shared : Bool,
    (joining shared).ordinal = 12 ∧ (joining shared).actor = 1 ∧
      (joining shared).command = .accept ∧ law.Valid (joining shared).item.before (joining shared).item.request ∧
      flowAt (law.actualDebit (joining shared).item.before (joining shared).item.request) 1 .labor = 1 := by
  decide +kernel

theorem accepted_message_updates_its_owner (shared : Bool) (message : Message shared)
    (paid : law.Valid message.item.before message.item.request) :
    update (registerBefore shared message.ordinal message.item) message.item message.actor =
      advance (registerBefore shared message.ordinal message.item message.actor) message.command := by
  simp [update, message.decoded, message.member, message.permitted, paid]

theorem message_is_the_original_root_item (shared : Bool) (message : Message shared) :
    message.item ∈ law.rawItems ((source shared).currentAt message.ordinal)
      (Institutions.Capitalism.Universal.Root.ProgrammeSource.rawEvent (source shared).input
        (Institutions.Capitalism.Universal.Root.ProgrammeHistory.visitAt (source shared).input message.ordinal).current) := by
  rw [← items_are_original]
  exact message.original

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation
