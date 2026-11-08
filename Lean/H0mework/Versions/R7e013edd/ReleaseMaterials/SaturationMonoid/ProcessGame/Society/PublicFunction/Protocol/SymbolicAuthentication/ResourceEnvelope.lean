import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueMemoryDeadline
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Material.Flows

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResourceEnvelope
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

def demand (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (party : Party) (good : Good) : ℚ :=
  max 0 (flowAt (law.debit item.before item.request) party good)

def bill (law : RawLaw Party Good Port Technology Instrument)
    (items : List (ExecutionItem Party Good Port Technology Instrument)) (party : Party) (good : Good) : ℚ :=
  (items.map fun item => demand law item party good).sum

omit [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
theorem actual_debit_is_bounded_by_the_original_requested_amount
    (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (party : Party) (good : Good) :
    flowAt (law.actualDebit item.before item.request) party good ≤ demand law item party good := by
  by_cases valid : law.Valid item.before item.request
  · simp only [RawLaw.actualDebit, if_pos valid, demand]
    exact le_max_right _ _
  · simp only [RawLaw.actualDebit, if_neg valid, flowAt, amount, List.map_nil, List.sum_nil, demand]
    exact le_max_left _ _

omit [DecidableEq Port] [DecidableEq Technology] in
theorem requested_reserve_generates_affordability_and_the_remaining_stock
    (law : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument) (index : Nat) (party : Party) (good : Good)
    (reserve : bill law (law.execute current index word).items party good ≤ current.stock party good) :
    (∀ item ∈ (law.execute current index word).items,
      flowAt (law.debit item.before item.request) party good ≤ item.before.stock party good) ∧
    current.stock party good - bill law (law.execute current index word).items party good ≤
      (law.execute current index word).final.stock party good := by
  induction word generalizing current index with
  | nil => simp only [RawLaw.execute, bill, List.map_nil, List.sum_nil, sub_zero, List.not_mem_nil, false_implies, implies_true, le_refl, and_self]
  | cons request tail ih =>
    let first : ExecutionItem Party Good Port Technology Instrument := ⟨index, current, request⟩
    have debit := actual_debit_is_bounded_by_the_original_requested_amount law first party good
    have credit := Institutions.Capitalism.Universal.Source.Material.acquired_nonnegative law first party good
    have balance := law.material_step_balance current request party good
    change 0 ≤ flowAt (law.actualCredit current request) party good at credit
    change flowAt (law.actualDebit current request) party good ≤ demand law first party good at debit
    change demand law first party good + bill law (law.execute (law.step current request) (index + 1) tail).items party good ≤ current.stock party good at reserve
    have laterReserve : bill law (law.execute (law.step current request) (index + 1) tail).items party good ≤
        (law.step current request).stock party good := by linarith
    obtain ⟨affordable, remaining⟩ := ih (law.step current request) (index + 1) laterReserve
    constructor
    · intro item member
      rcases List.mem_cons.mp member with same | later
      · subst item
        have nominal := le_max_right 0 (flowAt (law.debit current request) party good)
        have tailNonnegative : 0 ≤ bill law (law.execute (law.step current request) (index + 1) tail).items party good :=
          List.sum_nonneg (fun value inside => by
            obtain ⟨entry, _, rfl⟩ := List.mem_map.mp inside
            exact le_max_left _ _)
        change flowAt (law.debit current request) party good ≤ current.stock party good
        change flowAt (law.debit current request) party good ≤ demand law first party good at nominal
        linarith
      · exact affordable item later
    · change current.stock party good - (demand law first party good +
        bill law (law.execute (law.step current request) (index + 1) tail).items party good) ≤
          (law.execute (law.step current request) (index + 1) tail).final.stock party good
      linarith

variable {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def total (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (party : Party) (good : Good) : ℚ :=
  ((StageTrace.records cursor stages).map fun row => bill code.law (StageTrace.items row) party good).sum

theorem the_original_schedule_reserve_pays_every_actual_requested_debit
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) (party : Party) (good : Good)
    (reserve : total cursor stages party good ≤ (EventStep.seed cursor).current.stock party good) :
    (∀ row ∈ StageTrace.records cursor stages, ∀ item ∈ StageTrace.items row,
      flowAt (code.law.debit item.before item.request) party good ≤ item.before.stock party good) ∧
    (EventStep.seed cursor).current.stock party good - total cursor stages party good ≤
      (EventStep.seed (EventHistory.execute cursor stages)).current.stock party good := by
  induction stages generalizing cursor with
  | nil => simp [total, StageTrace.records, EventHistory.execute]
  | cons stage tail ih =>
    let row := StageTrace.material cursor stage.1 stage.2
    have nonnegative : 0 ≤ total (cursor.after stage.1 stage.2) tail party good :=
      List.sum_nonneg (fun value inside => by
        obtain ⟨entry, _, rfl⟩ := List.mem_map.mp inside
        exact List.sum_nonneg (fun value inside => by
          obtain ⟨item, _, rfl⟩ := List.mem_map.mp inside
          exact le_max_left _ _))
    change bill code.law (StageTrace.items row) party good + total (cursor.after stage.1 stage.2) tail party good ≤
      (EventStep.seed cursor).current.stock party good at reserve
    have front := requested_reserve_generates_affordability_and_the_remaining_stock code.law row.submitted
      row.before.current 0 party good (le_trans (by linarith : bill code.law (StageTrace.items row) party good ≤ _ ) reserve)
    have actual := (StageTrace.every_record_is_a_completed_occurrence_of_the_final_source cursor [stage] row List.mem_cons_self).2.2.2
    change row.after.current = code.law.next row.before.current row.submitted at actual
    have state := congrArg (fun state : Feedback.State code => state.current.stock party good)
      (StageTrace.material_is_the_actual_step cursor stage.1 stage.2).1
    have nextStock : (code.law.execute row.before.current 0 row.submitted).final.stock party good =
        (EventStep.seed (cursor.after stage.1 stage.2)).current.stock party good := by
      change (code.law.next row.before.current row.submitted).stock party good = _
      rw [← actual]
      exact state
    rw [nextStock] at front
    change (∀ item ∈ StageTrace.items row,
      flowAt (code.law.debit item.before item.request) party good ≤ item.before.stock party good) ∧
      (EventStep.seed cursor).current.stock party good - bill code.law (StageTrace.items row) party good ≤
        (EventStep.seed (cursor.after stage.1 stage.2)).current.stock party good at front
    obtain ⟨later, remaining⟩ := ih (cursor.after stage.1 stage.2) (by linarith [front.2])
    constructor
    · intro entry member
      rcases List.mem_cons.mp member with same | member
      · subst entry; exact front.1
      · exact later entry member
    · change (EventStep.seed cursor).current.stock party good - (bill code.law (StageTrace.items row) party good +
        total (cursor.after stage.1 stage.2) tail party good) ≤
          (EventStep.seed (EventHistory.execute (cursor.after stage.1 stage.2) tail)).current.stock party good
      linarith [front.2]

def check (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code))) : Bool :=
  code.parties.all fun party => code.goods.all fun good =>
    decide (total cursor stages party good ≤ (EventStep.seed cursor).current.stock party good)

theorem source_bill_and_initial_stock_generate_all_actual_affordability
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (funded : check cursor stages = true) (row : StageTrace.Record (code := code))
    (inside : row ∈ StageTrace.records cursor stages) (item : _) (member : item ∈ StageTrace.items row)
    (party : Party) (good : Good) :
    flowAt (code.law.debit item.before item.request) party good ≤ item.before.stock party good := by
  have reserve := of_decide_eq_true ((List.all_eq_true.mp
    ((List.all_eq_true.mp funded) party (code.parties_cover party))) good (code.goods_cover good))
  exact (the_original_schedule_reserve_pays_every_actual_requested_debit cursor stages party good reserve).1 row inside item member

theorem a_failed_source_reserve_exhibits_an_actual_account_gap
    (cursor : Cursor code) (stages : List (EventHistory.Stage (code := code)))
    (failed : check cursor stages = false) :
    ∃ party ∈ code.parties, ∃ good ∈ code.goods,
      (EventStep.seed cursor).current.stock party good < total cursor stages party good := by
  by_contra missing
  push Not at missing
  have accepted : check cursor stages = true := List.all_eq_true.mpr (by
    intro party member
    exact List.all_eq_true.mpr (by
      intro good inside
      exact decide_eq_true (missing party member good inside)))
  rw [accepted] at failed
  contradiction

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResourceEnvelope
