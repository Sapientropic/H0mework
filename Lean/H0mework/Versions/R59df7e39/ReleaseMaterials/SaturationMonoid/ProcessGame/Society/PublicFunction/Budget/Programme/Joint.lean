import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Gross.Joint
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Bounds

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

/-- Summation combines request counts; every debit keeps its original material coordinate. -/
theorem original_joint_cost_generates_only_local_work_bounds
    (axes : List (Party × Good)) (readings : Gross.Joint.Coverage code.law axes code.actions)
    (raw : Residual.Schedule code) (input : Input code) (seed : State code) (horizon : Nat)
    (budget : Party × Good → ℚ)
    (affordable : ∀ ticket ∈ readings.tickets,
      cost code raw input seed horizon ticket.axis.1 ticket.axis.2 ≤ budget ticket.axis)
    (legal : ∀ n < horizon, LawfulWork code (raw n) input (Residual.run code raw input seed n)) :
    ∀ n < horizon, WorkBound code (Gross.Joint.cap code.law axes readings.tickets budget)
      (raw n) input (Residual.run code raw input seed n) := by
  intro n inside
  let state := Residual.run code raw input seed n
  have lawful := legal n inside
  change WorkBound code (Gross.Joint.cap code.law axes readings.tickets budget) (raw n) input state
  change LawfulWork code (raw n) input state at lawful
  cases control : raw n with
  | none => simp only [WorkBound]
  | some rawPolicy =>
    cases chosen : decision code input state with
    | none => simp only [WorkBound,chosen]
    | some event =>
      rcases event with ⟨event,member⟩
      cases event with
      | adversary => simp only [WorkBound,chosen]
      | send => simp only [WorkBound,chosen]
      | deliver => simp only [WorkBound,chosen]
      | activate site =>
        have original : word code (raw n) input state = code.action rawPolicy site (state.frame.inbox site) := by
          simp only [word,control,chosen,stepLocal,Code.step,List.nil_append]
        simp only [WorkBound,chosen]
        change (code.action rawPolicy site (state.frame.inbox site)).length ≤ _
        have paid : (∀ request ∈ code.action rawPolicy site (state.frame.inbox site), request ∈ code.actions) ∧
            (∀ item ∈ code.law.rawItems state.current (code.action rawPolicy site (state.frame.inbox site)),
              code.law.Valid item.before item.request) := by
          simpa only [LawfulWork,control,chosen] using lawful
        have actualCosts : ∀ ticket ∈ readings.tickets,
            Gross.debit code.law ticket.axis.1 ticket.axis.2
              (code.law.rawItems state.current (code.action rawPolicy site (state.frame.inbox site))) ≤ budget ticket.axis := by
          intro ticket source
          have current := (each_actual_debit_is_in_the_original_total code raw input seed horizon
            ticket.axis.1 ticket.axis.2 n inside).trans (affordable ticket source)
          change code.law.totalDebit (code.law.rawItems state.current (word code (raw n) input state))
            ticket.axis.1 ticket.axis.2 ≤ budget ticket.axis at current
          rw [original] at current
          exact current
        exact ((mem_words_iff _ _ _).mp
          (Gross.Joint.every_joint_bounded_raw_word_is_enumerated readings.tickets code.actions budget
            state.current _ readings.covered paid.1 paid.2 actualCosts)).1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Normalization

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency Distributed.Recall.Information.Agency.Protocol
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (point : Continuation.Cursor code) (fallback : Rule code) (program : Program code)

theorem generated_work_bounds_preserve_every_actual_state
    (cap horizon : Nat) (enough : remaining point ≤ horizon) (rival : Opponent code)
    (localBounds : ∀ n < remaining point,
      Normalization.WorkBound code cap (Residual.scheduleAt point.source point.cut (schedule point fallback program) n)
        ⟨controller point fallback program rival,point.entry.budget⟩
        (Residual.run code (Residual.scheduleAt point.source point.cut (schedule point fallback program))
          ⟨controller point fallback program rival,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) n))
    (n : Nat) :
    Residual.run code (Residual.scheduleAt point.source point.cut (schedule point fallback (normalized cap horizon fallback program)))
      ⟨controller point fallback (normalized cap horizon fallback program) rival,point.entry.budget⟩
      (Residual.seed point.source point.entry point.cut) n =
    Residual.run code (Residual.scheduleAt point.source point.cut (schedule point fallback program))
      ⟨controller point fallback program rival,point.entry.budget⟩
      (Residual.seed point.source point.entry point.cut) n := by
  let old := Residual.scheduleAt point.source point.cut (schedule point fallback program)
  let new := Residual.scheduleAt point.source point.cut (schedule point fallback (normalized cap horizon fallback program))
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Residual.run]
    rw [ih]
    let actual := Residual.run code old ⟨controller point fallback program rival,point.entry.budget⟩
      (Residual.seed point.source point.entry point.cut) n
    change advance code (new n) ⟨controller point fallback (normalized cap horizon fallback program) rival,point.entry.budget⟩ actual =
      advance code (old n) ⟨controller point fallback program rival,point.entry.budget⟩ actual
    by_cases exhausted : actual.remaining = 0
    · cases new n <;> cases old n <;> simp only [advance,word,decision,exhausted,if_pos]
    · have inside : n < remaining point := by
        have left := Residual.remaining_is_the_seed_budget code old
          ⟨controller point fallback program rival,point.entry.budget⟩ (Residual.seed point.source point.entry point.cut) n
        change actual.remaining = remaining point-n at left
        omega
      have length := Replay.history_length point.source point.entry point.cut (schedule point fallback program)
        (controller point fallback program rival) n
      have decisions := normalized_controller_keeps_each_consumed_decision point fallback program cap horizon n
        (inside.trans_le enough) rival actual.history actual.past actual.frame length
      have work : new n = (old n).map (Normalization.policy code cap) := by
        dsimp only [new,old]
        simp only [Residual.scheduleAt,schedule,List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some]
        rw [normalized_at fallback program cap horizon n (inside.trans_le enough)]
        rfl
      calc
        _ = advance code (new n) ⟨controller point fallback program rival,point.entry.budget⟩ actual := by
          rw [Residual.advance_is_its_actual_choice,Residual.advance_is_its_actual_choice]
          exact congrArg (fun move => Residual.forced code (new n) move actual) decisions
        _ = advance code (old n) ⟨controller point fallback program rival,point.entry.budget⟩ actual := by
          rw [work]
          exact Normalization.one_step_preserves_all_external_attempts code cap (old n)
            ⟨controller point fallback program rival,point.entry.budget⟩ actual (localBounds n inside)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Joint

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (fallback : Rule model.source.code)
  (reference : Program model.source.code)

def sourceAxes : List (Party × Good) := model.source.code.parties.flatMap fun party =>
  model.source.code.goods.map fun good => (party,good)

def countReadings : Gross.Joint.Outcome model.source.code.law (sourceAxes model) model.source.code.actions :=
  Gross.Joint.generate model.source.code.actions

variable (readings : Gross.Joint.Coverage model.source.code.law (sourceAxes model) model.source.code.actions)

def cap : Nat := Gross.Joint.cap model.source.code.law (sourceAxes model) readings.tickets
  (Bounds.upper model domain fallback reference)

abbrev representative (program : Program model.source.code) :=
  normalized (cap model domain fallback reference readings) (Whole.Complete.horizon domain) fallback program

abbrev catalogue : List (Program model.source.code) :=
  programs model.source.code (cap model domain fallback reference readings) (Whole.Complete.horizon domain)

variable (program : Program model.source.code)
  (supported : ∀ n < Whole.Complete.horizon domain, (stage model.source.code fallback program n).supported)
  (accepted : Bounds.Accepted model domain fallback reference program)

include supported accepted in
theorem every_accepted_raw_program_has_a_joint_complete_representative
    (world : Replanning.Point model domain) (rival : Opponent model.source.code) :
    Finite.actualEvaluation model world.val fallback (representative model domain fallback reference readings program) rival =
      Finite.actualEvaluation model world.val fallback program rival := by
  let point := world.val
  let raw := Residual.scheduleAt point.source point.cut (schedule point fallback program)
  let input : Input model.source.code := ⟨controller point fallback program rival,point.entry.budget⟩
  let seed := Residual.seed point.source point.entry point.cut
  let horizon := remaining point
  have enough := Whole.Complete.each_remaining_horizon_is_generated domain world.val world.property
  have supportedSchedule := supported_schedule point fallback program (fun n inside => supported n (inside.trans_le enough))
  have legal := Normalization.original_final_legality_generates_every_local_work_obligation model.source.code raw input seed horizon
    supportedSchedule (accepted world rival).1
  have affordable : ∀ ticket ∈ readings.tickets,
      Normalization.cost model.source.code raw input seed horizon ticket.axis.1 ticket.axis.2 ≤
        Bounds.upper model domain fallback reference ticket.axis := by
    intro ticket _
    rw [Normalization.the_original_gross_cost_is_the_full_evaluations_material_reading
      (Replanning.native model point) point.entry point.cut rfl rfl (schedule point fallback program)
      (controller point fallback program rival) ticket.axis.1 ticket.axis.2]
    exact Bounds.every_full_responsibility_accepted_evaluation_fits_the_generated_upper model domain fallback reference
      world rival _ (accepted world rival) ticket.axis
  have bounds := Normalization.original_joint_cost_generates_only_local_work_bounds model.source.code (sourceAxes model)
    readings raw input seed horizon (Bounds.upper model domain fallback reference) affordable legal
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
theorem every_supported_joint_representative_is_source_generated :
    representative model domain fallback reference readings program ∈ catalogue model domain fallback reference readings :=
  every_supported_normalization_is_generated model.source.code fallback program
    (cap model domain fallback reference readings) (Whole.Complete.horizon domain) supported

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Joint
