import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Scope

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger

open ResponsibilityLifecycle
open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

theorem task_is_registered (index : productionSource.Slot) : Row.originalService index ∈ rows := by
  have member : Row.originalService index ∈ (List.finRange productionSource.seed.task.slots.length).map Row.originalService :=
    List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩
  simp only [rows, List.mem_append]
  tauto

theorem newborn_is_registered (index : Fin 4) (kind : Kind) : Row.bornService index kind ∈ rows := by
  have member : Row.bornService index kind ∈
      (List.finRange 4).flatMap (fun index => [Row.bornService index .life, Row.bornService index .maintenance]) :=
    List.mem_flatMap.mpr ⟨index, List.mem_finRange index, by cases kind <;> simp⟩
  simp only [rows, List.mem_append]
  tauto

theorem cut_is_registered (event : Observation) (actor : Fin 6) : Row.cut actor event ∈ rows := by
  have member : Row.cut actor event ∈ ((List.finRange 6).flatMap fun actor => (occurrences 25).attach.map (Row.cut actor)) :=
    List.mem_flatMap.mpr ⟨actor, List.mem_finRange actor, List.mem_map.mpr ⟨event, List.mem_attach _ _, rfl⟩⟩
  simp only [rows, List.mem_append]
  tauto

theorem cost_is_registered (actor : Fin 6) (good : Good) : Row.cost actor good ∈ rows := by
  have member : Row.cost actor good ∈ (List.finRange 6).flatMap (fun actor => goods.map (Row.cost actor)) :=
    List.mem_flatMap.mpr ⟨actor, List.mem_finRange actor, List.mem_map.mpr ⟨good, every_good_is_listed good, rfl⟩⟩
  simp only [rows, List.mem_append]
  tauto

theorem ordered_flow (measure : Item → Flow Party Good) (items : List Item)
    (stock : Party → Good → ℚ) (actor : Party) (good : Good) :
    (items.foldl (addFlow measure) stock) actor good = stock actor good +
      (items.map (fun item => flowAt (measure item) actor good)).sum := by
  induction items generalizing stock with
  | nil => simp
  | cons item rest ih =>
    rw [List.foldl_cons, ih]
    simp only [addFlow, List.map_cons, List.sum_cons]
    ring

theorem debit_is_actual_sum (shared : Bool) (actor : Party) (good : Good) :
    debit shared actor good = law.totalDebit (Participation.receipts shared 25) actor good := by
  unfold debit
  rw [ordered_flow]
  simp only [zero_add]
  rw [Participation.receipt_machine]
  rfl

theorem credit_is_actual_sum (shared : Bool) (actor : Party) (good : Good) :
    credit shared actor good = law.totalCredit (Participation.receipts shared 25) actor good := by
  unfold credit
  rw [ordered_flow]
  simp only [zero_add]
  rw [Participation.receipt_machine]
  rfl

theorem ordered_balance (items : List Item) (stock : Party → Good → ℚ) (actor : Party) (good : Good) :
    (items.foldl post stock) actor good + law.totalDebit items actor good =
      stock actor good + law.totalCredit items actor good := by
  induction items generalizing stock with
  | nil => simp [RawLaw.totalDebit, RawLaw.totalCredit]
  | cons item rest ih =>
    have tail := ih (post stock item)
    rw [show post stock item actor good = stock actor good -
      flowAt (law.actualDebit item.before item.request) actor good +
      flowAt (law.actualCredit item.before item.request) actor good from rfl] at tail
    simp only [List.foldl_cons, RawLaw.totalDebit, RawLaw.totalCredit, List.map_cons, List.sum_cons] at *
    linarith

def completion (checked : Check.Accepted rows Holds) : Completion inventory where
  exact_inventory := by
    intro actor good
    have physical := raw_balance actor good
    have ledger := ordered_balance ((occurrences 25).map Occurrence.item) initial.stock actor good
    rw [Participation.actual_current_is_the_machine]
    change inventory actor good = (rawFrame 25).raw.stock actor good
    unfold inventory
    linarith
  every_cut_floor := by
    intro event actor
    by_cases bounded : actor < 6
    · exact checked.checked (.cut ⟨actor, bounded⟩ event) (cut_is_registered event ⟨actor, bounded⟩)
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
      change credit true actor good = credit false actor good ∧
        debit true actor good + (if actor = 0 ∧ good = .labor then 1 else 0) = debit false actor good at paid
      rw [credit_is_actual_sum, credit_is_actual_sum, debit_is_actual_sum, debit_is_actual_sum] at paid
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
  services : (index : productionSource.Slot) → OutstandingSource.NativeService.Prefix productionSource index 24
  services_generated : services = fun index => OutstandingSource.NativeService.historyAt productionSource index 24
  services_terminal : ∀ index, (services index).state.TerminalAt 0
  newborn : (index : Fin 4) → (kind : Kind) → Newborn.Prefix (born index) kind (25 - (born index).ordinal)
  newborn_generated : newborn = fun index kind => Newborn.historyAt (born index) kind (25 - (born index).ordinal)
  newborn_terminal : ∀ index kind, (newborn index kind).state.TerminalAt 0
  newborn_exact : ∀ index kind, (newborn index kind).state.history = (newborn index kind).run.events
  dialogue : Participation.Native.History true
  dialogue_generated : dialogue = Participation.Native.historyAt true 12
  responsibility_kept : dialogue.state.slots = [.live (Participation.Native.obligation true)]
  production : (index : Fin 4) → ProductionData (born index)
    (if index.val = 0 then 6 else if index.val = 1 then 8 else if index.val = 2 then 9 else 10)
  complete : Completion inventory
  amount_positive : amount = 1 ∧ 0 < amount

def certify (checked : Check.Accepted rows Holds) : Certificate where
  checked := checked
  services := fun index => OutstandingSource.NativeService.historyAt productionSource index 24
  services_generated := rfl
  services_terminal := fun index => (terminal_flag_iff _).mp
    (checked.checked (.originalService index) (task_is_registered index))
  newborn := fun index kind => Newborn.historyAt (born index) kind (25 - (born index).ordinal)
  newborn_generated := rfl
  newborn_terminal := fun index kind => (terminal_flag_iff _).mp
    (checked.checked (.bornService index kind) (newborn_is_registered index kind))
  newborn_exact := fun index kind => Newborn.exact_native_history _ _ _
  dialogue := Participation.Native.historyAt true 12
  dialogue_generated := rfl
  responsibility_kept := Participation.Native.original_admission_and_residue_are_retained true 12
  production := ArtifactZero.firstProduction
  complete := completion checked
  amount_positive := ⟨(checked.checked .dividend (by simp [rows])).1, (checked.checked .dividend (by simp [rows])).2.1⟩

inductive Result
  | verified (certificate : Certificate)
  | rejected (failure : Check.Rejected rows Holds)

def run : Result := match verify with
  | .accepted checked => .verified (certify checked)
  | .rejected failure => .rejected failure

theorem actual_ledger_certificate_is_generated : run = .verified (certify ⟨fun row _ => actual_ledger_rows_hold row⟩) := by
  unfold run
  rw [actual_ledger_verifier_accepts]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Ledger
