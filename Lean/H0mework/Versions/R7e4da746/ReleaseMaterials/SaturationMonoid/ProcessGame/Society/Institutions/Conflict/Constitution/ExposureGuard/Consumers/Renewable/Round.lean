import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable.Authority
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand.Primitive

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable

open Capitalism.Universal.Source.Program Capitalism.Universal.Abolition Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence
open Installed (Port Tech)
open Quantities

open private use_part from H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Demand.Primitive

noncomputable section

abbrev W := Window Bool Bool Port Tech Unit

def serviceWindow (n : Nat) : W :=
  (Window.at (run n)).run (Execution.drain (run n))

theorem service_window_origin (n : Nat) :
    serviceWindow n = (⟨run n, Execution.drain (run n)⟩ : W) :=
  Native.the_native_drain_keeps_the_actual_open_window (run n)

theorem service_window_cut (n : Nat) : (serviceWindow n).current = readyCut (run n) :=
  Window.run_current (Window.at (run n)) (Execution.drain (run n))

theorem service_window_next (n : Nat) : (serviceWindow n).nextCut service = run (n + 1) := by
  unfold Window.nextCut
  rw [service_window_cut]
  change Execution.endAt (readyCut (run n)) [service] = Execution.endAt (run n) (wordAt (run n))
  unfold wordAt
  rw [Execution.endAt_append]
  rfl

theorem one_real_hour (n : Nat) : (run (n + 1)).raw.clock = (run n).raw.clock + 1 := by
  rw [actual_clock, actual_clock, Nat.cast_add, Nat.cast_one]
  exact (add_assoc _ _ _).symm

theorem service_window_deadline (n : Nat) :
    (serviceWindow n).deadline = ((serviceWindow n).nextCut service).raw.clock := by
  rw [service_window_next]
  unfold Window.deadline
  rw [show (serviceWindow n).opened = run n from congrArg Window.opened (service_window_origin n)]
  unfold Boundary.Actual.materialLaw
  rw [(stage n).input]
  change (run n).raw.clock + max 0 (1 : ℚ) = (run (n + 1)).raw.clock
  rw [max_eq_right zero_le_one, one_real_hour]

theorem crossing (n : Nat) : (serviceWindow n).crosses service := by
  have raw : (readyCut (run n)).raw = (run n).raw :=
    (Execution.the_first_exhausted_native_cut_is_the_original_paid_drain (run n)).2.1
  unfold Window.crosses
  rw [service_window_cut, service_window_next, raw, one_real_hour]
  exact lt_add_of_pos_right _ zero_lt_one

theorem original_requirement (cut : C) (same : cut.native.input = input) (cell : Cell)
    (listed : cell ∈ Demand.requirements cut) : ∃ person, cell = (person, .necessity, true, (1 : ℚ)) := by
  unfold Demand.requirements at listed
  rw [same] at listed
  exact native_cell _ _ cell listed

theorem original_renewal_pays_each_person (n : Nat) (person : Bool) :
    (1 : ℚ) ≤ (serviceWindow n).timely [] service (person, .necessity, true, 1) := by
  have passed (item : Item) (listed : item ∈ Boundary.Actual.items (readyCut (run n)) service) :
      decide (OwnMaterial (readyCut (run n)) [] item) = true :=
    decide_eq_true (each_item_is_self_paid n item listed)
  have opened : (serviceWindow n).opened = run n := congrArg Window.opened (service_window_origin n)
  have pending : (serviceWindow n).pending = Native.nativePrefix (run n) (Execution.remainingNative (run n)) :=
    congrArg Window.pending (service_window_origin n)
  unfold Window.timely
  rw [opened, pending, Native.timely_after_native_prefix (run n) (Execution.remainingNative (run n)) le_rfl]
  change (1 : ℚ) ≤
    (if (Execution.next (readyCut (run n)) service).raw.clock ≤ (serviceWindow n).deadline then
      (((Boundary.Actual.items (readyCut (run n)) service).filter
        (fun item => decide (OwnMaterial (readyCut (run n)) [] item))).map
        (fun item => flowAt (Optimality.Cost.actualPart (readyCut (run n)).native.handlerFace.rootRead
          item.before item.request (.use .necessity)) person true)).sum else 0) + 0
  have onTime : (Execution.next (readyCut (run n)) service).raw.clock ≤ (serviceWindow n).deadline := by
    rw [service_window_deadline n, ← service_window_cut n]
    exact le_rfl
  rw [if_pos onTime, add_zero, List.filter_eq_self.mpr passed, (body_paid (run n) n (stage n)).2]
  have lawExact : (readyCut (run n)).native.handlerFace.rootRead = material :=
    congrArg Physical.Public.interpreter (ready_stage (run n) n (stage n)).input
  rw [lawExact]
  have readback : ((material.rawItems (materialAt n) period).map fun item =>
      flowAt (Optimality.Cost.actualPart material item.before item.request (.use .necessity)) person true).sum =
      Material.actualUse checkInput (materialAt n) period person .necessity true := by
    unfold Material.actualUse
    apply congrArg List.sum
    apply List.map_congr_left
    intro item _
    exact use_part material item person .necessity true
  rw [readback]
  exact material_pays_each_necessity n person

private theorem every_due_row_has_the_original_address (n : Nat) (cell : Cell)
    (listed : cell ∈ (serviceWindow n).cells start []) :
    ∃ person, cell = (person, .necessity, true, (1 : ℚ)) := by
  let people := (serviceWindow n).residents start []
  have original := List.mem_dedup.mp listed
  change cell ∈ Boundary.floorCells start people ++ Boundary.floorCells (serviceWindow n).opened people ++
    Boundary.floorCells (serviceWindow n).current people at original
  rw [show (serviceWindow n).opened = run n from congrArg Window.opened (service_window_origin n),
    service_window_cut] at original
  rcases List.mem_append.mp original with first | latest
  · rcases List.mem_append.mp first with origin | opening
    · exact original_requirement start start_input cell (List.mem_filter.mp origin).1
    · exact original_requirement (run n) (stage n).input cell (List.mem_filter.mp opening).1
  · exact original_requirement (readyCut (run n)) (ready_stage (run n) n (stage n)).input cell
      (List.mem_filter.mp latest).1

private theorem service_paid (n : Nat) : StepGood start [] id true (serviceWindow n) service := by
  refine ⟨?_, ?_, ?_, ?_, fun _ => (service_window_deadline n).symm.le, ?_⟩
  · rw [service_window_cut]
    exact material_has_no_foreign_damage n
  · intro person _
    rw [service_window_next]
    exact standing_after n (wordAt (run n)) person
  · intro _ request listed
    rw [service_window_cut]
    exact ⟨standing_after n (Execution.drain (run n)) _, List.not_mem_nil,
      original_consents_empty _ listed⟩
  · intro _
    rw [service_window_cut]
    exact each_item_is_self_paid n
  · intro _ cell listed
    obtain ⟨person, rfl⟩ := every_due_row_has_the_original_address n cell listed
    exact original_renewal_pays_each_person n person

private theorem drain_checked (n : Nat) :
    Checked start [] id true (Window.at (run n)) (Execution.drain (run n)) := by
  let cut := run n
  suffices bounded : ∀ (m : Nat), m ≤ Execution.remainingNative cut →
      Checked start [] id true (Window.at cut) (Native.nativePrefix cut m) from bounded _ le_rfl
  intro m
  induction m with
  | zero => intro _; trivial
  | succ m prior =>
    intro within
    let window := (Window.at cut).run (Native.nativePrefix cut m)
    let here := Execution.endAt cut (Native.nativePrefix cut m)
    have current : window.current = here := Window.run_current (Window.at cut) (Native.nativePrefix cut m)
    have suffix : Native.nativePrefix cut (m + 1) = Native.nativePrefix cut m ++ [none] :=
      List.replicate_succ'
    have next : window.nextCut none = Execution.endAt cut (Native.nativePrefix cut (m + 1)) := by
      unfold Window.nextCut
      rw [current, suffix, Execution.endAt_append]
      rfl
    have first := Execution.an_original_native_prefix_preserves_material_and_pays_exactly_its_length cut m
      (by omega : m ≤ Execution.remainingNative cut)
    have last := Execution.an_original_native_prefix_preserves_material_and_pays_exactly_its_length cut (m + 1) within
    have remaining : Execution.remainingNative here + m = Execution.remainingNative cut := first.1
    have items : Boundary.Actual.items here none = [] :=
      (Execution.an_original_native_prefix_preserves_material_and_pays_exactly_its_length here 1 (by omega)).2.2
    have noCross : ¬ window.crosses none := by
      unfold Window.crosses
      rw [current, next, last.2.1]
      change ¬ (Execution.endAt cut (Native.nativePrefix cut m)).raw.clock < cut.raw.clock
      rw [first.2.1]
      exact lt_irrefl _
    rw [suffix, checked_append]
    refine ⟨prior (by omega), ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, trivial⟩⟩
    · intro damage
      have inventory := (congrArg (fun source => Boundary.Actual.items source none) current).trans items
      exact List.not_mem_nil ((congrArg (fun rows => damage.item ∈ rows) inventory).mp damage.source_item)
    · intro person _
      change person ∈ (window.nextCut none).members
      rw [next]
      exact standing_after n (Native.nativePrefix cut (m + 1)) person
    · intro _ request listed
      exact (List.not_mem_nil listed).elim
    · intro _ item listed
      rw [current, items] at listed
      exact (List.not_mem_nil listed).elim
    · exact fun crossed => (noCross crossed).elim
    · exact fun crossed => (noCross crossed).elim

theorem paid_round (n : Nat) : RoundGood start [] id (Window.at (run n)) (wordAt (run n)) [] := by
  refine ⟨?_, ?_, ?_, trivial⟩
  · intro empty
    have original : false ∈ Civil.protectedMembers (Window.at (run n)).current [] :=
      List.mem_filter.mpr ⟨standing_after n [] false, rfl⟩
    exact List.not_mem_nil (empty ▸ Window.includes_current_resident start [] (Window.at (run n)) original)
  · unfold wordAt
    rw [checked_append]
    exact ⟨drain_checked n, service_paid n, trivial⟩
  · rw [Window.run_current]
    change (run n).raw.clock < (run (n + 1)).raw.clock
    rw [one_real_hour]
    exact lt_add_of_pos_right _ zero_lt_one

theorem the_paid_cycle_opens_the_actual_next_window (n : Nat) :
    (Window.at (run n)).run (wordAt (run n)) = Window.at (run (n + 1)) := by
  unfold wordAt
  rw [Window.run_append]
  change (serviceWindow n).run [service] = _
  simp only [Window.run, Window.write, if_pos (crossing n), service_window_next]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable
