import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Continuation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Openness
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Cuts

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open OutstandingSource.NativeService

private def floor (current : Current) (actor : Party) : Prop :=
  (actor < 3 ∨ 0 < current.stock actor .seed) →
    1 ≤ current.stock actor .life ∧ 1 ≤ current.stock actor .spare

private instance (current : Current) (actor : Party) : Decidable (floor current actor) := by
  unfold floor
  infer_instance

private theorem finite_cuts_have_the_floor : ∀ item ∈ receipts source 11, ∀ actor : Fin 6,
    floor item.before actor ∧ floor (law.step item.before item.request) actor := by
  rw [receipts_are_the_generated_machine]
  decide +kernel

theorem every_actual_cut_keeps_all_original_and_seeded_bearers :
    ∀ item ∈ receipts source 11, ∀ actor : Party,
      ((actor < 3 ∨ 0 < item.before.stock actor .seed) →
        1 ≤ item.before.stock actor .life ∧ 1 ≤ item.before.stock actor .spare) ∧
      ((actor < 3 ∨ 0 < (law.step item.before item.request).stock actor .seed) →
        1 ≤ (law.step item.before item.request).stock actor .life ∧
          1 ≤ (law.step item.before item.request).stock actor .spare) := by
  intro item member actor
  by_cases inside : actor < 6
  · exact finite_cuts_have_the_floor item member ⟨actor, inside⟩
  · have outside : 6 ≤ actor := Nat.le_of_not_gt inside
    have zero := outside_at_every_cut true actor outside item member .seed
    constructor
    · rintro (original | seeded)
      · exact False.elim ((Nat.not_lt_of_ge (Nat.le_trans (by decide) outside)) original)
      · rw [zero.1] at seeded; exact False.elim (lt_irrefl _ seeded)
    · rintro (original | seeded)
      · exact False.elim ((Nat.not_lt_of_ge (Nat.le_trans (by decide) outside)) original)
      · rw [zero.2] at seeded; exact False.elim (lt_irrefl _ seeded)

theorem native_original_archives_survive (index : source.Slot) (later : Nat) :
    (historyAt source index (1 + later)).state = (historyAt source index 1).state := by
  apply terminal_state_is_preserved source index 1 later
  apply (native_terminal_iff_recorded source index 1).mpr
  refine ⟨1, ?_⟩
  rcases index with ⟨value, bound⟩
  change value < 6 at bound
  interval_cases value <;> decide +kernel +revert

def financialAccount (ordinal : Nat) := Financial.accountAt source.input ordinal

theorem native_financial_matrix (ordinal : Nat) :
    Financial.BalanceConservation.ledgerClaims source.input (financialAccount ordinal).current =
      (source.currentAt ordinal).claims :=
  Financial.BalanceConservation.generated_prefix_claims source.input rfl ordinal

def financialRun := Financial.BalanceConservation.fromActualCut source.input 0 11

theorem original_native_principal_is_paid :
    ((financialAccount 2).current.slots.map fun slot => Financial.total source.input (Financial.slotBalance source.input slot)) = [1] ∧
      ((financialAccount 4).current.slots.map fun slot => Financial.total source.input (Financial.slotBalance source.input slot)) = [0] := by
  decide +kernel

theorem every_later_actual_current_is_open (later : Nat) :
    (source.currentAt (3 + later)).technology.1 = true := by
  induction later with
  | zero => rw [current_is_generated_machine]; decide +kernel
  | succ later ih =>
    rw [raw_current_frame]
    change (law.next (source.frameAt (3 + later)).raw _).technology.1 = true
    apply Cell.next_preserves_open
    rwa [← raw_current_frame]

theorem every_later_word_has_no_capital_relation (later : Nat) (word : List RequestAt) :
    ¬ Nonempty (Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.CapitalRelationKernel law
      (source.currentAt (3 + later)) word) :=
  Cell.no_capital_kernel _ word (every_later_actual_current_is_open later)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit
