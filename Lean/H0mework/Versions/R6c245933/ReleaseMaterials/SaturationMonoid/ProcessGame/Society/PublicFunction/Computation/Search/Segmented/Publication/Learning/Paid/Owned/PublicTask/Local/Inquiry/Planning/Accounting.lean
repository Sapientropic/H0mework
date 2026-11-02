import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Whole.Counting
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.Accounting
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (task : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev Action := Institutions.Capitalism.Universal.Source.Program.Request Party Good Port (Mandate.State Party Technology) Instrument

def personal (request : Action (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) : Prop :=
  let actor := task.model.source.code.siteParty task.reader
  request.signer = actor ∧ (∀ consent ∈ request.consents, consent = actor) ∧
  ¬ Mandate.TaskUse task.model.scope request ∧
  match request.operation with
  | .use bearer bundle .external => bearer = actor ∧ NonnegativeBundle Good bundle
  | _ => False

instance (request : Action (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) : Decidable (personal task request) := by
  unfold personal
  cases request.operation <;> try infer_instance
  rename_i bearer bundle purpose
  cases purpose <;> infer_instance

def quantity (request : Action (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (good : Good) : ℚ :=
  match request.operation with
  | .use _ bundle .external => amount Good bundle good
  | _ => 0

def debit (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) (good : Good) : ℚ :=
  (word.map fun request => quantity request good).sum

def covers (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
    (rate : Action (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (units : Nat) : Prop :=
  (∀ request ∈ word, personal task request) ∧
    ∀ good ∈ task.model.source.code.goods, (units : ℚ) * quantity rate good ≤ debit word good

instance (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
    (rate : Action (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (units : Nat) : Decidable (covers task word rate units) := by
  unfold covers; infer_instance

/-- The tariff reserves source schema positions, rather than treating an
arbitrarily long registered word as one free atomic check. -/
def wordUnits (alphabet : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)) : Nat :=
  (alphabet.map fun word => 1 + word.length).sum

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument] in
theorem every_registered_word_position_is_in_the_bill
    (alphabet : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument))
    (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument) (inside : word ∈ alphabet) :
    1 + word.length ≤ wordUnits alphabet := by
  induction alphabet with
  | nil => cases inside
  | cons head tail ih =>
      rcases List.mem_cons.mp inside with same | later
      · subst word
        simp only [wordUnits,List.map_cons,List.sum_cons]
        omega
      · have reserved := ih later
        simp only [wordUnits,List.map_cons,List.sum_cons] at *
        omega

def worldInputUnits : Nat :=
  (task.worldInput.map Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskInput.units).getD 0

/-- A published service schedule: candidate and directory positions, both
strict-comparison directions, full control/request slots and four views of
registered future positions. Each World input position is reserved for every
scheduled interpretation. These declared schema-service units do not assert
an instruction count for the underlying evaluators or a CPU-time bound. -/
def selectionUnits : Nat :=
  let candidates := (programs task.model.source.code (horizon task.domain)).length
  let controlSlots := 1 + horizon task.domain * (1 + task.model.source.code.actionLimit)
  let cells := ((Selection.Restoration.rows task.model task.domain).map fun _ =>
    let positions := 2 * controlSlots + 4 * wordUnits (task.model.source.code.historyAlphabet ++ task.futureRequests)
    positions + positions * worldInputUnits task).sum
  1 + candidates + worldInputUnits task + candidates * (1 + 2*candidates) * cells

theorem supplied_world_is_reserved_before_interpretation
    (input : WorldInput task.model.base task.model.scope) (supplied : task.worldInput = some input) :
    input.units ≤ selectionUnits task := by
  unfold selectionUnits
  simp only [worldInputUnits,supplied,Option.map_some,Option.getD_some]
  omega

theorem every_supplied_request_position_is_in_the_bill
    (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
    (supplied : word ∈ task.futureRequests) :
    1 + word.length ≤ wordUnits (task.model.source.code.historyAlphabet ++ task.futureRequests) :=
  every_registered_word_position_is_in_the_bill _ _ (List.mem_append_right _ supplied)


def suitable (rate : Fin task.model.source.code.actions.length) : Prop :=
  personal task task.model.source.code.actions[rate] ∧
    ∃ good ∈ task.model.source.code.goods, 0 < quantity task.model.source.code.actions[rate] good

instance (rate : Fin task.model.source.code.actions.length) : Decidable (suitable task rate) := by
  unfold suitable; infer_instance

inductive Result where
  | legacy (absent : task.accountingRate = none) (empty : task.futureRequests = [])
      (noWorld : task.worldInput.isNone = true)
  | unpricedRequests (absent : task.accountingRate = none) (nonempty : task.futureRequests ≠ [])
  | unpricedWorld (absent : task.accountingRate = none) (empty : task.futureRequests = [])
      (present : task.worldInput.isNone = false)
  | invalid (rate : Fin task.model.source.code.actions.length)
      (declared : task.accountingRate = some rate) (bad : ¬ suitable task rate)
  | constructionShort (rate : Fin task.model.source.code.actions.length)
      (declared : task.accountingRate = some rate) (valid : suitable task rate)
      (short : ¬ covers task (Charge.fee task.quote) task.model.source.code.actions[rate] 1)
  | selectionShort (rate : Fin task.model.source.code.actions.length)
      (declared : task.accountingRate = some rate) (valid : suitable task rate)
      (built : covers task (Charge.fee task.quote) task.model.source.code.actions[rate] 1)
      (short : ¬ covers task (Charge.fee task.quote) task.model.source.code.actions[rate] (1 + selectionUnits task))
  | reserved (rate : Fin task.model.source.code.actions.length)
      (declared : task.accountingRate = some rate) (valid : suitable task rate)
      (built : covers task (Charge.fee task.quote) task.model.source.code.actions[rate] 1)
      (compared : covers task (Charge.fee task.quote) task.model.source.code.actions[rate] (1 + selectionUnits task))

namespace Result
variable {task}
def Released : Result task → Prop
  | .legacy .. | .reserved .. => True
  | _ => False
instance (made : Result task) : Decidable made.Released := by cases made <;> unfold Released <;> infer_instance
end Result

/-- Called only after the original charge succeeds. Descriptor generation has
its own construction allocation; no full-policy check is needed to quote it. -/
def run : Result task :=
  match declared : task.accountingRate with
  | none => if empty : task.futureRequests = [] then
      if noWorld : task.worldInput.isNone = true then .legacy declared empty noWorld
      else .unpricedWorld declared empty (Bool.eq_false_iff.mpr noWorld)
    else .unpricedRequests declared empty
  | some rate =>
      if valid : suitable task rate then
        if built : covers task (Charge.fee task.quote) task.model.source.code.actions[rate] 1 then
          if compared : covers task (Charge.fee task.quote) task.model.source.code.actions[rate] (1 + selectionUnits task) then
            .reserved rate declared valid built compared
          else .selectionShort rate declared valid built compared
        else .constructionShort rate declared valid built
      else .invalid rate declared valid

theorem every_released_nonempty_inventory_has_its_source_rate
    (made : Result task) (released : made.Released) (nonempty : task.futureRequests ≠ []) :
    ∃ rate : Fin task.model.source.code.actions.length, task.accountingRate = some rate := by
  cases made with
  | legacy absent empty _ => exact (nonempty empty).elim
  | unpricedRequests | unpricedWorld | invalid | constructionShort | selectionShort => cases released
  | reserved rate declared valid built compared => exact ⟨rate,declared⟩


theorem every_released_declared_bill_is_covered_in_each_original_good
    (made : Result task) (released : made.Released)
    (rate : Fin task.model.source.code.actions.length) (declared : task.accountingRate = some rate) :
    suitable task rate ∧ ∀ good : Good,
      quantity task.model.source.code.actions[rate] good ≤ debit (Charge.fee task.quote) good ∧
      ((1 + selectionUnits task : Nat) : ℚ) * quantity task.model.source.code.actions[rate] good ≤ debit (Charge.fee task.quote) good := by
  cases made with
  | legacy absent _ _ | unpricedRequests absent _ | unpricedWorld absent _ _ => rw [absent] at declared; cases declared
  | invalid | constructionShort | selectionShort => cases released
  | reserved chosen found valid built compared =>
      have same := Option.some.inj (found.symm.trans declared)
      subst chosen
      refine ⟨valid,fun good => ⟨?_,compared.2 good (task.model.source.code.goods_cover good)⟩⟩
      simpa only [Nat.cast_one,one_mul] using built.2 good (task.model.source.code.goods_cover good)

theorem every_released_world_input_has_its_covered_source_rate
    (made : Result task) (released : made.Released)
    (input : WorldInput task.model.base task.model.scope) (supplied : task.worldInput = some input) :
    ∃ rate : Fin task.model.source.code.actions.length, task.accountingRate = some rate ∧
      suitable task rate ∧ covers task (Charge.fee task.quote) task.model.source.code.actions[rate]
        (1 + selectionUnits task) := by
  cases made with
  | legacy absent empty noWorld => simp only [supplied,Option.isNone_some,Bool.false_eq_true] at noWorld
  | unpricedRequests | unpricedWorld | invalid | constructionShort | selectionShort => cases released
  | reserved rate declared valid built compared => exact ⟨rate,declared,valid,compared⟩


theorem personal_quantity_nonnegative
    (request : Action (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (valid : personal task request) (good : Good) : 0 ≤ quantity request good := by
  have shape := valid.2.2.2
  cases operation : request.operation <;> simp only [quantity,operation] <;> try exact le_rfl
  rename_i bearer bundle purpose
  cases purpose <;> try exact le_rfl
  rw [operation] at shape
  exact amount_nonnegative bundle shape.2 good

theorem covers_smaller_units
    (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
    (rate : Action (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (valid : personal task rate) {lower upper : Nat} (bounded : lower ≤ upper)
    (covered : covers task word rate upper) : covers task word rate lower := by
  refine ⟨covered.1,fun good member => ?_⟩
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast bounded)
    (personal_quantity_nonnegative task rate valid good)).trans (covered.2 good member)

def selectionLowerUnits : Nat :=
  2 + Distributed.Recall.Information.Agency.Protocol.Continuation.Whole.Counting.programCount
    task.model.source.code (horizon task.domain)

theorem selection_lower_is_in_the_original_bill :
    selectionLowerUnits task ≤ 1 + selectionUnits task := by
  unfold selectionLowerUnits selectionUnits
  rw [Distributed.Recall.Information.Agency.Protocol.Continuation.Whole.Counting.programCount_exact]
  dsimp only [Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.programs]
  omega

/-- A failed source-counted lower bill proves the same full-bill refusal.
The original implementation stays as the fallback before its compiler equation is registered. -/
def runCounted : Result task :=
  match declared : task.accountingRate with
  | none => run task
  | some rate =>
      if valid : suitable task rate then
        if built : covers task (Charge.fee task.quote) task.model.source.code.actions[rate] 1 then
          if lower : covers task (Charge.fee task.quote) task.model.source.code.actions[rate]
              (selectionLowerUnits task) then
            run task
          else .selectionShort rate declared valid built (fun full => lower
            (covers_smaller_units task _ _ valid.1 (selection_lower_is_in_the_original_bill task) full))
        else run task
      else run task

@[csimp] theorem run_eq_counted : @run = @runCounted := by
  funext Party Good Port Technology Instrument _ _ _ _ _ task
  unfold runCounted
  split
  · rfl
  · rename_i rate declared
    split
    · rename_i valid
      split
      · rename_i built
        split
        · rfl
        · rename_i lower
          have bad : ¬ covers task (Charge.fee task.quote) task.model.source.code.actions[rate]
              (1 + selectionUnits task) := fun full => lower
            (covers_smaller_units task _ _ valid.1 (selection_lower_is_in_the_original_bill task) full)
          unfold run
          split
          · rename_i absent
            rw [declared] at absent
            cases absent
          · rename_i other found
            have same : other = rate := Option.some.inj (found.symm.trans declared)
            subst other
            simp only [dif_pos valid,dif_pos built,dif_neg bad]
      · rfl
    · rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Planning.Accounting
