import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Dynamic.Cost
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Joint

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Dynamic

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (fallback : Rule model.source.code)
  (reference : Program model.source.code)

def initialTechnologies : List (Mandate.State Party Technology) :=
  domain.map fun point => (Residual.seed point.source point.entry point.cut).current.technology

def menu := technologies model.source.code (initialTechnologies model domain)

def countReadings := Cost.generate model.source.code (menu model domain)

theorem every_public_seed_has_its_own_original_technology (world : Replanning.Point model domain) :
    (Residual.seed world.val.source world.val.entry world.val.cut).current.technology ∈ menu model domain :=
  List.mem_append_left _ (List.mem_map.mpr ⟨world.val,world.property,rfl⟩)

variable (readings : Cost.Coverage model.source.code (menu model domain))

def cap : Nat := Cost.cap model.source.code readings.readings (Bounds.upper model domain fallback reference)

abbrev representative (program : Program model.source.code) :=
  normalized (cap model domain fallback reference readings) (Whole.Complete.horizon domain) fallback program

abbrev catalogue : List (Program model.source.code) :=
  programs model.source.code (cap model domain fallback reference readings) (Whole.Complete.horizon domain)

variable (program : Program model.source.code)
  (supported : Open.Supported model domain fallback program)
  (accepted : Bounds.Accepted model domain fallback reference program)

include supported accepted in
theorem actual_dynamic_requests_generate_their_own_local_work_bounds
    (world : Replanning.Point model domain) (rival : Opponent model.source.code) :
    ∀ n < remaining world.val,
      Normalization.WorkBound model.source.code (cap model domain fallback reference readings)
        (Residual.scheduleAt world.val.source world.val.cut (schedule world.val fallback program) n)
        ⟨controller world.val fallback program rival,world.val.entry.budget⟩
        (Residual.run model.source.code
          (Residual.scheduleAt world.val.source world.val.cut (schedule world.val fallback program))
          ⟨controller world.val fallback program rival,world.val.entry.budget⟩
          (Residual.seed world.val.source world.val.entry world.val.cut) n) := by
  let point := world.val
  let code := model.source.code
  let raw := Residual.scheduleAt point.source point.cut (schedule point fallback program)
  let input : Input code := ⟨controller point fallback program rival,point.entry.budget⟩
  let seed := Residual.seed point.source point.entry point.cut
  let horizon := remaining point
  have enough := Whole.Complete.each_remaining_horizon_is_generated domain world.val world.property
  have supportedSchedule := supported_schedule point fallback program
    (fun n inside => supported n (inside.trans_le enough))
  have legal := Normalization.original_final_legality_generates_every_local_work_obligation code raw input seed horizon
    supportedSchedule (accepted world rival).1
  intro n inside
  let state := Residual.run code raw input seed n
  have known := every_actual_raw_run_stays_in_the_source_technology_menu code (initialTechnologies model domain)
    raw input seed (every_public_seed_has_its_own_original_technology model domain world) horizon supportedSchedule n inside.le
  have lawful := legal n inside
  change Normalization.WorkBound code (cap model domain fallback reference readings) (raw n) input state
  change Normalization.LawfulWork code (raw n) input state at lawful
  cases control : raw n with
  | none => simp only [Normalization.WorkBound]
  | some policy =>
    cases chosen : decision code input state with
    | none => simp only [Normalization.WorkBound,chosen]
    | some event =>
      rcases event with ⟨event,member⟩
      cases event with
      | adversary => simp only [Normalization.WorkBound,chosen]
      | send => simp only [Normalization.WorkBound,chosen]
      | deliver => simp only [Normalization.WorkBound,chosen]
      | activate site =>
        have original : word code (raw n) input state = code.action policy site (state.frame.inbox site) := by
          simp only [word,control,chosen,stepLocal,Code.step,List.nil_append]
        simp only [Normalization.WorkBound,chosen]
        change (code.action policy site (state.frame.inbox site)).length ≤ _
        have paid : (∀ request ∈ code.action policy site (state.frame.inbox site),request ∈ code.actions) ∧
            (∀ item ∈ code.law.rawItems state.current (code.action policy site (state.frame.inbox site)),
              code.law.Valid item.before item.request) := by
          simpa only [Normalization.LawfulWork,control,chosen] using lawful
        have primitive : ∀ request ∈ code.action policy site (state.frame.inbox site),request ∈ requests code := by
          intro request occurs
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (paid.1 request occurs)))
        have reachable := (each_executed_source_word_keeps_all_intermediate_technologies code
          (initialTechnologies model domain) state.current known _ primitive 0).2
        have affordable : ∀ reading ∈ readings.readings,
            code.law.totalDebit (code.law.rawItems state.current (code.action policy site (state.frame.inbox site)))
              reading.axis.1 reading.axis.2 ≤ Bounds.upper model domain fallback reference reading.axis := by
          intro reading source
          have current := Normalization.each_actual_debit_is_in_the_original_total code raw input seed horizon
            reading.axis.1 reading.axis.2 n inside
          have upper := Bounds.every_full_responsibility_accepted_evaluation_fits_the_generated_upper model domain fallback reference
            world rival _ (accepted world rival) reading.axis
          rw [Normalization.the_original_gross_cost_is_the_full_evaluations_material_reading
            (Replanning.native model point) point.entry point.cut rfl rfl (schedule point fallback program)
            (controller point fallback program rival) reading.axis.1 reading.axis.2] at current
          change code.law.totalDebit (code.law.rawItems state.current (word code (raw n) input state))
            reading.axis.1 reading.axis.2 ≤ _ at current
          rw [original] at current
          exact current.trans upper
        exact ((mem_words_iff _ _ _).mp
          (Cost.every_original_dynamically_bounded_word_is_enumerated code (menu model domain) readings
            (Bounds.upper model domain fallback reference) state.current _ paid.1 reachable paid.2 affordable)).1

include supported accepted in
theorem every_accepted_dynamic_raw_program_has_a_complete_representative
    (world : Replanning.Point model domain) (rival : Opponent model.source.code) :
    Finite.actualEvaluation model world.val fallback (representative model domain fallback reference readings program) rival =
      Finite.actualEvaluation model world.val fallback program rival := by
  let point := world.val
  have enough := Whole.Complete.each_remaining_horizon_is_generated domain world.val world.property
  have bounds := actual_dynamic_requests_generate_their_own_local_work_bounds model domain fallback reference readings
    program supported accepted world rival
  have runs := generated_work_bounds_preserve_every_actual_state point fallback program
    (cap model domain fallback reference readings) (Whole.Complete.horizon domain) enough rival bounds
  exact Transport.full_evaluation_congr (Replanning.native model point) point.entry point.cut
    (schedule point fallback program) (schedule point fallback (representative model domain fallback reference readings program))
    (controller point fallback program rival)
    (controller point fallback (representative model domain fallback reference readings program) rival)
    (fun ordinal _ => Replay.source_events point.source point.entry point.cut
      (schedule point fallback program) (schedule point fallback (representative model domain fallback reference readings program))
      (controller point fallback program rival)
      (controller point fallback (representative model domain fallback reference readings program) rival)
      runs rfl rfl ordinal)
    (runs _) rfl

include supported in
theorem every_supported_dynamic_representative_is_source_generated :
    representative model domain fallback reference readings program ∈ catalogue model domain fallback reference readings :=
  every_supported_normalization_is_generated model.source.code fallback program
    (cap model domain fallback reference readings) (Whole.Complete.horizon domain) supported

include supported accepted in
theorem every_raw_improvement_occurs_within_the_source_generated_dynamic_cap
    (better : Open.improves model domain fallback reference program) :
    Open.Within model domain fallback reference (cap model domain fallback reference readings) := by
  let candidate := representative model domain fallback reference readings program
  have evaluations := every_accepted_dynamic_raw_program_has_a_complete_representative model domain fallback reference
    readings program supported accepted
  have acceptedCandidate : Bounds.Accepted model domain fallback reference candidate := by
    intro world rival
    change Synthesis.accepts _ _ (Finite.actualEvaluation model world.val fallback candidate rival) _
    rw [evaluations world rival]
    exact accepted world rival
  have forward : Open.noWorse model domain fallback candidate reference := by
    intro world rival
    simpa only [candidate,evaluations world rival] using better.1 world rival
  have strict : ¬ Open.noWorse model domain fallback reference candidate := by
    intro reverse
    apply better.2
    intro world rival
    simpa only [candidate,evaluations world rival] using reverse world rival
  refine ⟨candidate,?_,(Open.checked_exact model domain fallback reference candidate).mpr
    ⟨acceptedCandidate,forward,strict⟩⟩
  apply List.mem_filter.mpr
  exact ⟨every_supported_dynamic_representative_is_source_generated model domain fallback reference readings program supported,
    by simp only [candidate,normalized,List.length_map,List.length_range,beq_self_eq_true]⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Dynamic
