import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Accounting
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.Native

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority

def messageOrigin (shared : Bool) (message : Message shared) : Financial.InstructionOrigin (source shared).input :=
  RootFace.original (source shared).input (ProgrammeHistory.visitAt (source shared).input message.ordinal)
    ⟨message.item, message_is_the_original_root_item shared message⟩

theorem message_origin_decodes_exactly (shared : Bool) (message : Message shared) :
    (messageOrigin shared message).instruction? (source shared).input = some message.item :=
  RootFace.original_decodes_exact_item (source shared).input
    (ProgrammeHistory.visitAt (source shared).input message.ordinal) _

/-- The roots retain their own reports and provenance. This equality is
only the actual material prefix, before the new participation input. -/
theorem old_birth_items_are_the_same_executed_prefix (ordinal : Nat) (before_cut : ordinal < 11) :
    itemsAt true ordinal = Born.itemsAt ordinal := by
  rw [common_original_items true ordinal before_cut]
  change law.rawItems (SharedAudit.source.frameAt ordinal).raw
    (SharedAudit.source.frameWord ordinal (SharedAudit.source.frameAt ordinal)) = _
  rw [← (SharedAudit.source.canonical_frame ordinal).1,
    ← (SharedAudit.source.canonical_frame ordinal).2,
    SharedAudit.current_is_generated_machine, SharedAudit.actual_word_is_machine]
  rfl

theorem old_birth_has_an_own_actual_item (index : Fin 4) :
    (Born.born index).item ∈ itemsAt true (Born.born index).ordinal := by
  have member : Born.born index ∈ Born.births 11 := List.getElem_mem _
  have before_cut := Born.every_generated_birth_is_in_the_prefix 11 _ member
  rw [old_birth_items_are_the_same_executed_prefix _ before_cut]
  exact (Born.born index).original

def carriedBirthOrigin (index : Fin 4) : Financial.InstructionOrigin (source true).input :=
  RootFace.original (source true).input (ProgrammeHistory.visitAt (source true).input (Born.born index).ordinal)
    ⟨(Born.born index).item, by
      change (Born.born index).item ∈ law.rawItems ((source true).currentAt (Born.born index).ordinal)
        (ProgrammeSource.rawEvent (source true).input (ProgrammeHistory.visitAt (source true).input (Born.born index).ordinal).current)
      rw [← items_are_original]
      exact old_birth_has_an_own_actual_item index⟩

theorem carried_birth_origin_decodes_exactly (index : Fin 4) :
    (carriedBirthOrigin index).instruction? (source true).input = some (Born.born index).item :=
  RootFace.original_decodes_exact_item (source true).input
    (ProgrammeHistory.visitAt (source true).input (Born.born index).ordinal) _

structure CarriedService (index : Fin 4) (kind : Born.Kind) where
  original : Born.Native.Prefix (Born.born index) kind (11 - (Born.born index).ordinal)
  generated : original = Born.allNewbornServices index kind
  terminal : original.state.TerminalAt 0
  payment_visit : Nat
  before_cut : payment_visit < 11
  item : Born.Item
  own_item : item ∈ itemsAt true payment_visit
  accepted : law.Valid item.before item.request
  use : Institutions.Capitalism.Universal.Exit.Necessity.UseMatches item.request.operation
    (Born.born index).child kind.goods kind.purpose
  old_archive : ∃ (offset : Nat) (paid : Born.Paid (Born.born index) kind ((Born.born index).ordinal + offset)),
    payment_visit = (Born.born index).ordinal + offset ∧
      original.state.slots = [.terminal (Born.Native.paidArchive (Born.born index) kind offset paid)]

def carriedService (index : Fin 4) (kind : Born.Kind) : CarriedService index kind := by
  let offset := Born.firstVisit index - (Born.born index).ordinal
  have same : (Born.born index).ordinal + offset = Born.firstVisit index :=
    Nat.add_sub_of_le (Born.actual_births_precede_their_first_service index).1
  have paid : Born.Paid (Born.born index) kind ((Born.born index).ordinal + offset) := by
    rw [same]
    exact (Born.actual_first_service_payments index kind).1
  let receipt := Born.payment (Born.born index) kind ((Born.born index).ordinal + offset) paid
  have before_cut : (Born.born index).ordinal + offset < 11 := by
    rw [same]
    exact (Born.actual_births_precede_their_first_service index).2
  exact {
    original := Born.allNewbornServices index kind
    generated := rfl
    terminal := Born.actual_newborn_service_is_terminal index kind
    payment_visit := (Born.born index).ordinal + offset
    before_cut := before_cut
    item := receipt.item
    own_item := by
      rw [old_birth_items_are_the_same_executed_prefix _ before_cut]
      exact receipt.original
    accepted := receipt.accepted
    use := receipt.use
    old_archive := by
      obtain ⟨oldOffset, oldPaid, exact_visit, slots⟩ := Born.actual_archive_is_from_the_first_service index kind
      exact ⟨oldOffset, oldPaid, same.trans exact_visit.symm, slots⟩ }

theorem old_capability_transport_after_all_dialogue_costs (word : List RequestAt)
    (accepted : ∀ item ∈ law.rawItems ((source false).currentAt 25) word, law.Valid item.before item.request) :
    (∀ item ∈ law.rawItems ((source true).currentAt 25) word, law.Valid item.before item.request) ∧
      (law.execute ((source true).currentAt 25) 0 word).final =
        withLabor (law.execute ((source false).currentAt 25) 0 word).final 1 := by
  rw [full_carrier_has_exactly_the_same_dividend]
  exact every_legal_word_keeps_the_same_extra_labor _ 1 (by norm_num) word 0 accepted

theorem original_service_archives_survive (shared : Bool) (index : (source shared).Slot) (later : Nat) :
    (OutstandingSource.NativeService.historyAt (source shared) index (1 + later)).state =
      (OutstandingSource.NativeService.historyAt (source shared) index 1).state := by
  apply OutstandingSource.NativeService.terminal_state_is_preserved (source shared) index 1 later
  apply (OutstandingSource.NativeService.native_terminal_iff_recorded (source shared) index 1).mpr
  refine ⟨1, ?_⟩
  rcases index with ⟨value, bound⟩
  change value < 6 at bound
  interval_cases value <;> cases shared <;> decide +kernel +revert

theorem every_later_current_is_open (shared : Bool) (later : Nat) :
    ((source shared).currentAt (3 + later)).technology.1 = true := by
  induction later with
  | zero => rw [actual_current_is_the_machine]; cases shared <;> decide +kernel
  | succ later ih =>
    rw [actual_current_is_the_machine] at *
    exact Cell.next_preserves_open _ _ ih

theorem every_later_word_keeps_public_production (shared : Bool) (later : Nat) (word : List RequestAt) :
    ¬ Nonempty (Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.CapitalRelationKernel law
      ((source shared).currentAt (3 + later)) word) :=
  Cell.no_capital_kernel _ _ (every_later_current_is_open shared later)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation
