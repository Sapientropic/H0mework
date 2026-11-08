import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DynamicCommandConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveDynamicCommandDomain
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (delay : Nat)

abbrev State := LocalCommandRun.State model start

theorem every_generated_external_choice_is_its_own_actual_intake
    (state : State model start) (event : Choice model.source.code)
    (chosen : some event ∈ InterferenceEnvelope.choices start state.stages delay) :
    Distributed.Recall.Information.Agency.externalChoice model.source.code (some event) = some event := by
  have fresh (member : event ∈ InterferenceEnvelope.fresh start (state.current model start)) :
      Distributed.Recall.Information.Agency.externalChoice model.source.code (some event) = some event := by
    obtain ⟨serial,kind,_,_,_⟩ := CompletionEnvelope.every_generated_delivery_has_a_real_fresh_admitted_packet
      start (state.current model start) event member
    rcases event with ⟨value,supported⟩
    dsimp only at kind
    cases kind
    rfl
  have extra (member : event ∈ InterferenceEnvelope.extras start state.stages) :
      Distributed.Recall.Information.Agency.externalChoice model.source.code (some event) = some event := by
    have kind := (InterferenceEnvelope.every_extra_event_has_source_admission_and_unspent_interface_capacity
      start state.stages event member).2.2.2
    rcases event with ⟨value,supported⟩
    cases value <;> first | contradiction | rfl
  by_cases owner : (LocalCommandSource.owner model (state.current model start)).isSome = true
  · simp [InterferenceEnvelope.choices,owner] at chosen
  · cases pending : InterferenceEnvelope.fresh start (state.current model start) with
    | nil =>
      apply extra
      simpa [InterferenceEnvelope.choices,owner,pending] using chosen
    | cons head tail =>
      by_cases room : InterferenceEnvelope.gap start (StageTrace.records start state.stages) < delay
      · have alternatives : event ∈ InterferenceEnvelope.fresh start (state.current model start) ++
            InterferenceEnvelope.extras start state.stages := by
          simpa [InterferenceEnvelope.choices,owner,pending,room] using chosen
        exact (List.mem_append.mp alternatives).elim fresh extra
      · apply fresh
        simpa [InterferenceEnvelope.choices,owner,pending,room] using chosen

theorem every_live_actual_state_generates_an_executable_dynamic_input
    (state : State model start) (live : 0 < (EventStep.seed (state.current model start)).remaining) :
    ∃ input ∈ CommandWindowSource.menu model, DynamicCommandSource.within model start delay state input = true := by
  have alive : (EventStep.seed (state.current model start)).remaining ≠ 0 := by omega
  have quiet : DynamicCommandSource.intake model start state .idle = none := by
    simp [DynamicCommandSource.intake,DynamicCommandSource.entry,
      LocalCommandSource.Entry.selected,LocalCommandSource.observe,LocalCommandSource.select,alive,
      LocalCommandSource.Selection.rival,CompletionEnvelope.intake,CompletionEnvelope.raw,EventStep.selected,EventStep.fixed,
      Distributed.Recall.Information.Agency.externalChoice]
  by_cases owned : (LocalCommandSource.owner model (state.current model start)).isSome = true
  · refine ⟨.idle,List.mem_cons_self,?_⟩
    simp [DynamicCommandSource.within,quiet,InterferenceEnvelope.choices,owned]
  · obtain ⟨move,chosen⟩ := List.exists_mem_of_ne_nil _
      (InterferenceEnvelope.the_generated_domain_is_nonempty start state.stages delay)
    cases move with
    | none => exact ⟨.idle,List.mem_cons_self,by simpa only [DynamicCommandSource.within,quiet,decide_eq_true_eq] using chosen⟩
    | some event =>
      obtain ⟨index,lookup⟩ := List.mem_iff_getElem?.mp event.property
      have bounded : index < model.source.code.eventAlphabet.length := (List.getElem?_eq_some_iff.mp lookup).1
      have raw : LocalCommandSource.Input.event index ∈ CommandWindowSource.menu model := by
        apply List.mem_cons_of_mem
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨index,List.mem_range.mpr (by omega),rfl⟩
      have owner : LocalCommandSource.owner model (state.current model start) = none := by
        cases actual : LocalCommandSource.owner model (state.current model start) with
        | none => rfl
        | some worker => simp [actual] at owned
      have selected : LocalCommandSource.select model (state.current model start) (.event index) = .external (some event) := by
        unfold LocalCommandSource.select
        dsimp only
        rw [dif_neg alive]
        split
        next absent => rw [lookup] at absent; contradiction
        next value found =>
          have same : value = event.val := Option.some.inj (found.symm.trans lookup)
          subst value
          split
          next outside => rfl
          next worker inside => rw [owner] at inside; contradiction
      have actual : DynamicCommandSource.intake model start state (.event index) =
          Distributed.Recall.Information.Agency.externalChoice model.source.code (some event) := by
        simp [DynamicCommandSource.intake,DynamicCommandSource.entry,
          LocalCommandSource.Entry.selected,LocalCommandSource.observe,selected,owner,
          LocalCommandSource.Selection.rival,CompletionEnvelope.intake,CompletionEnvelope.raw,EventStep.selected,EventStep.fixed]
      refine ⟨.event index,raw,?_⟩
      have normalized := every_generated_external_choice_is_its_own_actual_intake model start delay state event chosen
      simpa only [DynamicCommandSource.within,actual,normalized,decide_eq_true_eq] using chosen

theorem positive_actual_fuel_generates_a_nonempty_dynamic_domain
    (state : State model start) (live : 0 < (EventStep.seed (state.current model start)).remaining) :
    DynamicCommandSource.menu model start delay state ≠ [] := by
  obtain ⟨input,source,allowed⟩ := every_live_actual_state_generates_an_executable_dynamic_input model start delay state live
  exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨source,allowed⟩)

def nextInput (state : State model start) (live : 0 < (EventStep.seed (state.current model start)).remaining) :
    {input // input ∈ DynamicCommandSource.menu model start delay state} :=
  ⟨(DynamicCommandSource.menu model start delay state).head
      (positive_actual_fuel_generates_a_nonempty_dynamic_domain model start delay state live),
    List.head_mem (positive_actual_fuel_generates_a_nonempty_dynamic_domain model start delay state live)⟩

theorem the_generated_input_extends_its_original_timing_history
    (state : State model start) (live : 0 < (EventStep.seed (state.current model start)).remaining)
    (past : AdaptiveRejectionHistory.Compliant start delay state.stages) :
    AdaptiveRejectionHistory.Compliant start delay
      (LocalCommandRun.step model start state (nextInput model start delay state live).val).stages :=
  (DynamicCommandSource.actual_admission_is_exactly_the_original_prefix_timing_extension model start delay state _).mpr
    ⟨past,(List.mem_filter.mp (nextInput model start delay state live).property).2⟩

theorem a_missing_dynamic_continuation_has_exhausted_its_actual_source_fuel
    (state : State model start) (empty : DynamicCommandSource.menu model start delay state = []) :
    (EventStep.seed (state.current model start)).remaining = 0 := by
  by_contra live
  exact positive_actual_fuel_generates_a_nonempty_dynamic_domain model start delay state (by omega) empty

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LiveDynamicCommandDomain
