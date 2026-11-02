import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Work

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

abbrev Allocation := Nat × Nat
def globalQuotas (allocation : List Allocation) := allocation.map Prod.fst

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (announcements : List (Rule model.source.code)) (point : View (code := model.source.code))

def ownerSlots : List Nat := (List.range (Cut.horizon point.point.source point.point.entry point.point.cut)).filter
  (fun index => decide (Focused.clock point.point index = some worker))

structure ClockPlan where
  first : Nat
  second : Nat
  rest : List Nat
  generated : ownerSlots model worker point = first::second::rest
  earlier : first < second

def clockPlan : Option (ClockPlan model worker point) :=
  match generated : ownerSlots model worker point with
  | first::second::rest => some ⟨first,second,rest,generated,by
      have ordered := (List.pairwise_lt_range (n := Cut.horizon point.point.source point.point.entry point.point.cut)).filter
        (fun index => decide (Focused.clock point.point index = some worker))
      change (ownerSlots model worker point).Pairwise (· < ·) at ordered
      rw [generated] at ordered
      exact (List.pairwise_cons.mp ordered).1 second List.mem_cons_self⟩
  | _ => none

def allocation (plan : ClockPlan model worker point) : List Allocation :=
  let width := plan.second+1
  let nominal := List.replicate width 0
  let globalCount := (Sparse.tails domain (Segmented.reserved model original worker quote nominal)).length
  let eligibleCount := (Guarded.eligibleTails model domain original worker receiver quote nominal announcements).length
  (List.range width).map fun index =>
    if index = plan.first then (globalCount,0) else if index = plan.second then (0,eligibleCount) else (0,0)

theorem the_allocation_length_is_its_second_source_slot (plan : ClockPlan model worker point) :
    (allocation model domain original worker receiver quote announcements point plan).length = plan.second+1 := by
  simp only [allocation,List.length_map,List.length_range]

theorem both_selected_slots_are_actual_available_worker_slots (plan : ClockPlan model worker point) :
    plan.first < plan.second ∧ plan.second < Cut.horizon point.point.source point.point.entry point.point.cut ∧
    Focused.clock point.point plan.first = some worker ∧ Focused.clock point.point plan.second = some worker := by
  have first : plan.first ∈ ownerSlots model worker point := by rw [plan.generated];simp
  have second : plan.second ∈ ownerSlots model worker point := by rw [plan.generated];simp
  obtain ⟨_,firstOwn⟩ := List.mem_filter.mp first
  obtain ⟨secondBound,secondOwn⟩ := List.mem_filter.mp second
  exact ⟨plan.earlier,List.mem_range.mp secondBound,of_decide_eq_true firstOwn,of_decide_eq_true secondOwn⟩

theorem the_source_allocation_never_assigns_both_queues_to_one_slot
    (plan : ClockPlan model worker point) (assignment : Allocation)
    (inside : assignment ∈ allocation model domain original worker receiver quote announcements point plan) :
    assignment.1 = 0 ∨ assignment.2 = 0 := by
  obtain ⟨index,_,same⟩ := List.mem_map.mp inside
  subst assignment
  split
  · exact .inr rfl
  · split
    · exact .inl rfl
    · exact .inl rfl

theorem a_missing_clock_plan_has_fewer_than_two_available_source_slots
    (absent : clockPlan model worker point = none) : (ownerSlots model worker point).length < 2 := by
  unfold clockPlan at absent
  split at absent
  · cases absent
  · rename_i cannotTwo
    cases slots : ownerSlots model worker point with
    | nil => decide
    | cons first tail =>
      cases tail with
      | nil => exact Nat.lt_succ_self 1
      | cons second rest => exact False.elim (cannotTwo first second rest slots)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified
