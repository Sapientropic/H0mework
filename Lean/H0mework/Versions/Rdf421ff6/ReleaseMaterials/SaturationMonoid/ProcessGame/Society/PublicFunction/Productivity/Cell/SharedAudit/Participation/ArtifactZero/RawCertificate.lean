import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Raw
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Scope

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Raw

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

theorem task_is_registered (index : productionSource.Slot) : Row.originalService index ∈ rows := by
  have member : Row.originalService index ∈ (List.finRange productionSource.seed.task.slots.length).map Row.originalService :=
    List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩
  simp only [rows, List.mem_append]
  tauto

theorem newborn_is_registered (index : Fin 4) (kind : Kind) : Row.bornService index kind ∈ rows := by
  have member : Row.bornService index kind ∈
      (List.finRange 4).flatMap (fun index => [Row.bornService index .life, Row.bornService index .maintenance, Row.firstProduction index]) :=
    List.mem_flatMap.mpr ⟨index, List.mem_finRange index, by cases kind <;> simp⟩
  simp only [rows, List.mem_append]
  tauto

theorem cut_is_registered (event : Observation) (actor : Fin 6) : Row.cut event actor ∈ rows := by
  have member : Row.cut event actor ∈ ((occurrences 25).attach.flatMap fun event => (List.finRange 6).map (Row.cut event)) :=
    List.mem_flatMap.mpr ⟨event, List.mem_attach _ _, List.mem_map.mpr ⟨actor, List.mem_finRange actor, rfl⟩⟩
  simp only [rows, List.mem_append]
  tauto

theorem cost_is_registered (actor : Fin 6) (good : Good) : Row.cost actor good ∈ rows := by
  have member : Row.cost actor good ∈ (List.finRange 6).flatMap (fun actor => goods.map (Row.cost actor)) :=
    List.mem_flatMap.mpr ⟨actor, List.mem_finRange actor, List.mem_map.mpr ⟨good, every_good_is_listed good, rfl⟩⟩
  simp only [rows, List.mem_append]
  tauto

def completion (checked : Check.Accepted rows Holds) : Completion stockFromItems where
  exact_inventory := by
    intro actor good
    have balance := raw_balance actor good
    rw [Participation.actual_current_is_the_machine]
    unfold stockFromItems
    linarith
  every_cut_floor := by
    intro event actor
    by_cases bounded : actor < 6
    · exact checked.checked (.cut event ⟨actor, bounded⟩) (cut_is_registered event ⟨actor, bounded⟩)
    · have outside := Nat.le_of_not_gt bounded
      have zero := observation_outside_inventory event actor outside .seed
      constructor
      · rintro (original | seeded)
        · exact False.elim ((Nat.not_lt_of_ge (Nat.le_trans (by decide) outside)) original)
        · rw [zero.1] at seeded; linarith
      · rintro (original | seeded)
        · exact False.elim ((Nat.not_lt_of_ge (Nat.le_trans (by decide) outside)) original)
        · rw [zero.2] at seeded; linarith
  full_cost := by
    intro actor good
    by_cases bounded : actor < 6
    · have paid := checked.checked (.cost ⟨actor, bounded⟩ good) (cost_is_registered ⟨actor, bounded⟩ good)
      change law.totalCredit ((occurrences 25).map Occurrence.item) actor good =
          law.totalCredit ((List.range 25).flatMap (Participation.itemsAt false)) actor good ∧
        law.totalDebit ((occurrences 25).map Occurrence.item) actor good + (if actor = 0 ∧ good = .labor then 1 else 0) =
          law.totalDebit ((List.range 25).flatMap (Participation.itemsAt false)) actor good at paid
      rw [occurrence_items_are_original, ← Participation.receipt_machine false 25] at paid
      exact paid
    · have outside := Nat.le_of_not_gt bounded
      have t := Participation.outside_totals true actor outside good
      have f := Participation.outside_totals false actor outside good
      constructor
      · exact t.2.trans f.2.symm
      · rw [t.1, f.1, if_neg (by rintro ⟨zero, _⟩; subst actor; omega)]
        norm_num
  exact_origin := occurrence_origin_decodes_exactly
  own_resources := fun _event valid => Cell.valid_debits_only_the_signer _ _ valid
  full_claims := Participation.financial_matrix true
  finance := by simpa only [Nat.zero_add] using Financial.BalanceConservation.fromActualCut productionSource.input 0 25
  no_capital := Participation.every_later_word_keeps_public_production true
  original_rows := productionSource.receipt_is_in_original_task_write
  own_next := (productionSource.actualExecution 23).root_next_exact

structure Certificate where
  checked : Check.Accepted rows Holds
  task_payment : (index : productionSource.Slot) → Payment (occurrences 25) (task index)
  task_generated : ∀ index, task_payment index = (payments (occurrences 25) (task index)).head
    (List.isEmpty_eq_false_iff.mp (checked.checked (.originalService index) (task_is_registered index)))
  newborn_payment : (index : Fin 4) → (kind : Kind) → Payment (occurrences 25) (newborn (born index) kind)
  newborn_generated : ∀ index kind, newborn_payment index kind = (payments (occurrences 25) (newborn (born index) kind)).head
    (List.isEmpty_eq_false_iff.mp (checked.checked (.bornService index kind) (newborn_is_registered index kind)))
  production : (index : Fin 4) → ProductionData (born index) (firstVisit index)
  complete : Completion stockFromItems
  amount_positive : amount = 1 ∧ 0 < amount

def certify (checked : Check.Accepted rows Holds) : Certificate where
  checked := checked
  task_payment := fun index => (payments (occurrences 25) (task index)).head
    (List.isEmpty_eq_false_iff.mp (checked.checked (.originalService index) (task_is_registered index)))
  task_generated := fun _ => rfl
  newborn_payment := fun index kind => (payments (occurrences 25) (newborn (born index) kind)).head
    (List.isEmpty_eq_false_iff.mp (checked.checked (.bornService index kind) (newborn_is_registered index kind)))
  newborn_generated := fun _ _ => rfl
  production := ArtifactZero.firstProduction
  complete := completion checked
  amount_positive := checked.checked .nonPositiveDividend (by simp [rows])

inductive Result
  | verified (certificate : Certificate)
  | rejected (failure : Check.Rejected rows Holds)

def run : Result := match verify with
  | .accepted checked => .verified (certify checked)
  | .rejected failure => .rejected failure

theorem actual_raw_certificate_is_generated : run = .verified (certify ⟨fun row _ => actual_raw_rows_hold row⟩) := by
  unfold run
  rw [actual_raw_verifier_accepts]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Raw
