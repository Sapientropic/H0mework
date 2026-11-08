import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueBirthConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.BirthWindow
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev family := ActualInventoryPrefix.family model
abbrev inputs (cursor : Cursor model.source.code) := ActualInventoryPrefix.inputs model cursor
def births (cursor : Cursor model.source.code) (stages : JointResponse.Stages model) :=
  InventoryBirthBudget.arrivals (family model) (inputs model (EventHistory.execute cursor stages))
    (EventStep.boundary cursor) stages.length

theorem arrivals_add (cursor : Cursor model.source.code) (first left right : Nat) :
    InventoryBirthBudget.arrivals (family model) (inputs model cursor) first (left + right) =
      InventoryBirthBudget.arrivals (family model) (inputs model cursor) first left +
        InventoryBirthBudget.arrivals (family model) (inputs model cursor) (first + left) right := by
  induction right with
  | zero => simp only [Nat.add_zero, InventoryBirthBudget.arrivals]
  | succ right ih =>
    rw [Nat.add_succ, InventoryBirthBudget.arrivals, InventoryBirthBudget.arrivals, ih, Nat.add_assoc, Nat.add_assoc]

theorem completed_arrivals_survive_actual_extension (cursor : Cursor model.source.code)
    (tail : JointResponse.Stages model) (first count : Nat) (inside : first + count ≤ EventStep.boundary cursor) :
    InventoryBirthBudget.arrivals (family model) (inputs model (EventHistory.execute cursor tail)) first count =
      InventoryBirthBudget.arrivals (family model) (inputs model cursor) first count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [InventoryBirthBudget.arrivals, InventoryBirthBudget.arrivals, ih (by omega)]
    rw [(ActualInventoryPrefix.one_actual_extension_preserves_the_complete_inventory_slices model cursor tail
      (first + count) (by omega)).2.2.1]

theorem actual_append_has_exact_additive_births (cursor : Cursor model.source.code)
    (first second : JointResponse.Stages model) :
    births model cursor (first ++ second) = births model cursor first +
      births model (EventHistory.execute cursor first) second := by
  unfold births
  rw [List.length_append, OriginQueue.execute_append, arrivals_add]
  rw [completed_arrivals_survive_actual_extension model (EventHistory.execute cursor first) second
    (EventStep.boundary cursor) first.length (by
      rw [IncidentChallenge.execution_advances_the_actual_boundary])]
  rw [IncidentChallenge.execution_advances_the_actual_boundary]

theorem an_empty_window_has_no_births (cursor : Cursor model.source.code) : births model cursor [] = 0 := rfl

theorem a_single_actual_visit_has_its_exact_birth_slice (cursor : Cursor model.source.code)
    (protocol : Rule model.source.code) (rival : Opponent model.source.code) :
    births model cursor [(protocol, rival)] =
      CompletedInventory.openBorn (family model) (inputs model (cursor.after protocol rival)) (EventStep.boundary cursor) := by
  change 0 + CompletedInventory.openBorn _ _ (EventStep.boundary cursor + 0) = _
  simp only [Nat.zero_add, Nat.add_zero]
  rfl

theorem actual_single_visit_births_are_paid_by_its_original_word (cursor : Cursor model.source.code)
    (protocol : Rule model.source.code) (rival : Opponent model.source.code) :
    births model cursor [(protocol, rival)] ≤ (StageTrace.material cursor protocol rival).submitted.length := by
  rw [a_single_actual_visit_has_its_exact_birth_slice]
  exact NativeBirthWord.every_actual_open_birth_is_funded_by_its_submitted_request_word model cursor
    [(protocol, rival)] (StageTrace.material cursor protocol rival) List.mem_cons_self

theorem an_actual_empty_word_has_no_births (cursor : Cursor model.source.code)
    (protocol : Rule model.source.code) (rival : Opponent model.source.code)
    (empty : (StageTrace.material cursor protocol rival).submitted = []) :
    births model cursor [(protocol, rival)] = 0 := by
  have paid := actual_single_visit_births_are_paid_by_its_original_word model cursor protocol rival
  rw [empty, List.length_nil] at paid
  omega

theorem an_actual_unsigned_visit_has_no_births (cursor : Cursor model.source.code)
    (protocol : Rule model.source.code) (rival : Opponent model.source.code)
    (unsigned : ∀ item ∈ StageTrace.items (StageTrace.material cursor protocol rival),
      ¬ Mandate.Challenge.Submission (scope := model.scope) item.request) :
    births model cursor [(protocol, rival)] = 0 := by
  rw [a_single_actual_visit_has_its_exact_birth_slice]
  have trace := IncidentChallenge.actual_trace_items model cursor [(protocol, rival)]
    (StageTrace.material cursor protocol rival) List.mem_cons_self
  have noClaims : Mandate.Challenge.claimsAt (family model) (inputs model (cursor.after protocol rival))
      (EventStep.boundary cursor) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro position inside
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp inside
    have denied : ¬ Mandate.Challenge.Submission (scope := model.scope)
        ((⟨EventStep.boundary cursor, index⟩ : Mandate.Challenge.Position (family model)
          (inputs model (cursor.after protocol rival))).item _ _).request := by
      apply unsigned
      have actual : Institutions.Capitalism.Universal.Source.ProgrammeFace.Registered.traceItems
          (Mandate.Challenge.I (family model) (inputs model (cursor.after protocol rival)))
          (ProgrammeHistory.visitAt (Mandate.Challenge.I (family model) (inputs model (cursor.after protocol rival)))
            (EventStep.boundary cursor)).current = StageTrace.items (StageTrace.material cursor protocol rival) := trace
      rw [← actual]
      exact List.get_mem _ _
    simp only [Mandate.Challenge.read, dif_neg denied]
  simp only [CompletedInventory.openBorn, noClaims, List.filter_nil, List.length_nil]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.BirthWindow
