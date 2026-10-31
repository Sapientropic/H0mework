import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born.Native

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born

open ResponsibilityLifecycle
open Institutions.Capitalism.Universal.Source.Program

def firstVisit (index : Fin 4) : Nat :=
  if index.val = 0 then 6 else if index.val = 1 then 8 else if index.val = 2 then 9 else 10

theorem actual_births_precede_their_first_service : ∀ index : Fin 4,
    (born index).ordinal ≤ firstVisit index ∧ firstVisit index < 11 := by
  decide +kernel

theorem actual_first_service_payments : ∀ index : Fin 4, ∀ kind : Kind,
    Paid (born index) kind (firstVisit index) ∧
      ∀ earlier : Fin (firstVisit index - (born index).ordinal),
        ¬ Paid (born index) kind ((born index).ordinal + earlier.val) := by
  decide +kernel

theorem all_four_cells_have_actual_first_production : ∀ index : Fin 4,
    (productionsAt (born index) (firstVisit index)).isEmpty = false := by
  decide +kernel

def firstProduction (index : Fin 4) : ProductionData (born index) (firstVisit index) :=
  (productionsAt (born index) (firstVisit index)).head
    (List.isEmpty_eq_false_iff.mp (all_four_cells_have_actual_first_production index))

theorem production_uses_the_original_seed (index : Fin 4) :
    (firstProduction index).item ∈ itemsAt (firstVisit index) ∧
      law.Valid (firstProduction index).item.before (firstProduction index).item.request ∧
      (firstProduction index).item.request.operation = .produce (born index).child ∧
      0 < (firstProduction index).item.before.stock (born index).child .seed :=
  ⟨(firstProduction index).original, (firstProduction index).accepted,
    (firstProduction index).operation, (firstProduction index).seed⟩

theorem newborn_obligation_is_initially_live (index : Fin 4) (kind : Kind) :
    (Native.historyAt (born index) kind 0).state.LiveAt 0 := by
  exact ⟨Native.obligation (born index) kind, rfl⟩

theorem actual_newborn_service_is_terminal (index : Fin 4) (kind : Kind) :
    (Native.historyAt (born index) kind (11 - (born index).ordinal)).state.TerminalAt 0 := by
  apply (Native.native_terminal_iff_paid _ _ _).mpr
  have limits := actual_births_precede_their_first_service index
  refine ⟨firstVisit index - (born index).ordinal, by omega, ?_⟩
  simpa only [Nat.add_sub_of_le limits.1] using (actual_first_service_payments index kind).1

theorem actual_archive_is_from_the_first_service (index : Fin 4) (kind : Kind) :
    ∃ (offset : Nat) (paid : Paid (born index) kind ((born index).ordinal + offset)),
      (born index).ordinal + offset = firstVisit index ∧
      (Native.historyAt (born index) kind (11 - (born index).ordinal)).state.slots =
        [.terminal (Native.paidArchive (born index) kind offset paid)] := by
  obtain ⟨offset, bound, paid, earliest, slots⟩ :=
    Native.terminal_has_the_first_original_payment (born index) kind _ (actual_newborn_service_is_terminal index kind)
  have limits := actual_births_precede_their_first_service index
  have known := (actual_first_service_payments index kind).1
  have noEarlier := (actual_first_service_payments index kind).2
  have offset_eq : offset = firstVisit index - (born index).ordinal := by
    by_contra different
    by_cases small : offset < firstVisit index - (born index).ordinal
    · exact noEarlier ⟨offset, small⟩ paid
    · have past : firstVisit index - (born index).ordinal < offset := by omega
      have absent := earliest (firstVisit index - (born index).ordinal) past
      rw [Nat.add_sub_of_le limits.1] at absent
      exact absent known
  exact ⟨offset, paid, by omega, slots⟩

theorem every_finite_successor_keeps_the_first_newborn_archive (index : Fin 4) (kind : Kind) (later : Nat) :
    (Native.historyAt (born index) kind (11 - (born index).ordinal + later)).state =
      (Native.historyAt (born index) kind (11 - (born index).ordinal)).state :=
  Native.terminal_state_is_preserved _ _ _ later (actual_newborn_service_is_terminal index kind)

def allNewbornServices : (index : Fin 4) → (kind : Kind) →
    Native.Prefix (born index) kind (11 - (born index).ordinal) :=
  fun index kind => Native.historyAt (born index) kind (11 - (born index).ordinal)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Born
