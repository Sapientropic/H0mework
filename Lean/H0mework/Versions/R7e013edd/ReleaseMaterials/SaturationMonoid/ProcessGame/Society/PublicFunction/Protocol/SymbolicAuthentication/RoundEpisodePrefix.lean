import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundEpisodeSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundEpisodePrefix
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open RoundEpisodeSource
open MaterialRoundSource (Bound)
abbrev ProgramInput := ProgrammeSource.Input Delegation.Funded.Party Repayment.Recovery.Good Delegation.Funded.Port
  (Mandate.State Delegation.Funded.Party Bool) Unit

structure Prefix (old new : ProgramInput) (limit : Nat) : Prop where
  law : new.law = old.law
  initial : new.initial = old.initial
  currents : ∀ n, n ≤ limit → (ProgrammeHistory.visitAt new n).current = (ProgrammeHistory.visitAt old n).current
  words : ∀ n, n < limit → ProgrammeSource.rawEvent new (ProgrammeHistory.visitAt new n).current =
    ProgrammeSource.rawEvent old (ProgrammeHistory.visitAt old n).current

theorem Prefix.weaken {old new : ProgramInput} {limit small : Nat} (prior : Prefix old new limit)
    (bounded : small ≤ limit) : Prefix old new small :=
  ⟨prior.law,prior.initial,fun n inside => prior.currents n (by omega),fun n inside => prior.words n (by omega)⟩
theorem Prefix.trans {one two three : ProgramInput} {limit : Nat} (first : Prefix one two limit)
    (second : Prefix two three limit) : Prefix one three limit :=
  ⟨second.law.trans first.law,second.initial.trans first.initial,
    fun n inside => (second.currents n inside).trans (first.currents n inside),
    fun n inside => (second.words n inside).trans (first.words n inside)⟩

theorem an_actual_continuation_keeps_the_complete_original_prefix
    (old : Bound) (count : Nat) (raw : List RecycledQuorumMaterial.Action) :
    Prefix old.source.input (Machine.Continuation.extend old.source count raw).input (MaterialRoundSource.depth old count+1) := by
  refine ⟨rfl,rfl,Machine.Continuation.prior_currents old.source count raw,?_⟩
  intro n inside
  exact (Native.Coupling.History.occurrences old.source.input (Machine.Continuation.extend old.source count raw).input
    rfl rfl (MaterialRoundSource.depth old count+1) (Machine.Continuation.prior_events old.source count raw) n inside).2

theorem preparation_keeps_the_original_prefix (state : State) (raw : List RecycledQuorumMaterial.Action) :
    Prefix state.model.source.input (residual state raw).source.input (boundary state) := by
  have first : Prefix state.model.source.input (rawSource state raw).source.input (boundary state) := by
    have size : MaterialRoundSource.depth state.model state.cut+1 = boundary state := by
      dsimp [MaterialRoundSource.depth,Machine.Continuation.depth,boundary];omega
    simpa only [size] using an_actual_continuation_keeps_the_complete_original_prefix state.model state.cut raw
  have second := an_actual_continuation_keeps_the_complete_original_prefix (rawSource state raw) (state.cut+1)
    (WorkerInputSource.incoming (rawSource state raw) (state.cut+1))
  have third := an_actual_continuation_keeps_the_complete_original_prefix (supplied state raw) (count state) (arrival state raw)
  have fourth := an_actual_continuation_keeps_the_complete_original_prefix
    (MaterialRoundSource.supplied (supplied state raw) (count state) (arrival state raw)) (count state+1)
    (MaterialRoundSource.recovery (supplied state raw) (count state) (arrival state raw))
  exact first.trans ((second.weaken (by dsimp [boundary,MaterialRoundSource.depth,Machine.Continuation.depth,Machine.Continuation.extend,Machine.withContinuation];omega)).trans
    ((third.weaken (by dsimp [boundary,MaterialRoundSource.depth,Machine.Continuation.depth,Machine.Continuation.extend,Machine.withContinuation,count];omega)).trans
      (fourth.weaken (by dsimp [boundary,MaterialRoundSource.depth,Machine.Continuation.depth,Machine.Continuation.extend,Machine.withContinuation,count];omega))))

theorem actual_new_execution_keeps_the_supplied_prefix (state : State) (command : Command state)
    (entry : RoundEpisodeSource.Entry state command.raw) :
    Prefix (MaterialRoundSource.supplied (supplied state command.raw) (count state) (arrival state command.raw)).source.input
      (actual state command entry).source.input
      (MaterialRoundSource.depth (supplied state command.raw) (count state)+2) := by
  let old := supplied state command.raw
  let k := count state
  let word := arrival state command.raw
  have size : (emitter state command.raw entry).history.length = MaterialRoundSource.depth old k+2 := by
    change (RoundArchive.history (MaterialRoundSource.supplied old k word).source (k+1) (MaterialRoundSource.recovery old k word)).length = _
    rw [RoundArchive.history_is_the_entire_actual_snapshot_and_new_arrival,List.length_append,RoundArchive.snapshot_length]
    rfl
  have prior : ∀ n, n < MaterialRoundSource.depth old k+2 →
      ProgrammeSource.rawEvent (actual state command entry).source.input
        (ProgrammeHistory.visitAt (MaterialRoundSource.supplied old k word).source.input n).current =
      ProgrammeSource.rawEvent (MaterialRoundSource.supplied old k word).source.input
        (ProgrammeHistory.visitAt (MaterialRoundSource.supplied old k word).source.input n).current := by
    intro n inside
    have raw := RoundArchive.prior_events (MaterialRoundSource.supplied old k word).source (k+1)
      (MaterialRoundSource.recovery old k word) MaterialRoundSource.payment MaterialRoundSource.fee entry.history n inside
    cases view : (ProgrammeHistory.visitAt (MaterialRoundSource.supplied old k word).source.input n).current with
    | bootstrap => rfl
    | running current past =>
      have rounds := ProgrammeHistory.visit_round (MaterialRoundSource.supplied old k word).source.input n
      rw [view] at rounds
      have bounded : current.round-(MaterialRoundSource.supplied old k word).source.code.initial.round-1 < (emitter state command.raw entry).history.length := by
        change current.round = (MaterialRoundSource.supplied old k word).source.code.initial.round+n at rounds
        rw [size];omega
      have same : (actual state command entry).source.body current = (emitter state command.raw entry).body current := by
        have sameHistory : (actual state command entry).source.history = (emitter state command.raw entry).history := rfl
        have sameInitial : (actual state command entry).source.code.initial = (MaterialRoundSource.supplied old k word).source.code.initial := rfl
        unfold Machine.body
        rw [sameHistory,sameInitial,show (emitter state command.raw entry).code.initial = (MaterialRoundSource.supplied old k word).source.code.initial from rfl]
        rw [List.getElem?_eq_getElem bounded]
      change (actual state command entry).source.body current = _
      rw [view] at raw
      exact same.trans raw
  refine ⟨rfl,rfl,?_,?_⟩
  · exact Machine.actual_prefix_from_events (MaterialRoundSource.supplied old k word).source.input
      (actual state command entry).source.input rfl rfl (MaterialRoundSource.depth old k+2) prior
  · intro n inside
    exact (Native.Coupling.History.occurrences (MaterialRoundSource.supplied old k word).source.input
      (actual state command entry).source.input rfl rfl (MaterialRoundSource.depth old k+2) prior n inside).2

theorem every_episode_keeps_the_complete_original_prefix (state : State) (command : Command state) :
    Prefix state.model.source.input (next state command).model.source.input (boundary state) := by
  cases generated : inspect state command.raw with
  | none =>
    simpa only [next,generated] using preparation_keeps_the_original_prefix state command.raw
  | some entry =>
    have one : Prefix state.model.source.input (rawSource state command.raw).source.input (boundary state) := by
      have size : MaterialRoundSource.depth state.model state.cut+1 = boundary state := by
        dsimp [MaterialRoundSource.depth,Machine.Continuation.depth,boundary];omega
      simpa only [size] using an_actual_continuation_keeps_the_complete_original_prefix state.model state.cut command.raw
    have two := an_actual_continuation_keeps_the_complete_original_prefix (rawSource state command.raw) (state.cut+1)
      (WorkerInputSource.incoming (rawSource state command.raw) (state.cut+1))
    have three := an_actual_continuation_keeps_the_complete_original_prefix (supplied state command.raw) (count state) (arrival state command.raw)
    have four := actual_new_execution_keeps_the_supplied_prefix state command entry
    simpa only [next,generated] using one.trans ((two.weaken (by dsimp [boundary,MaterialRoundSource.depth,Machine.Continuation.depth,Machine.Continuation.extend,Machine.withContinuation];omega)).trans
      ((three.weaken (by dsimp [boundary,MaterialRoundSource.depth,Machine.Continuation.depth,Machine.Continuation.extend,Machine.withContinuation,count];omega)).trans
        (four.weaken (by dsimp [boundary,MaterialRoundSource.depth,Machine.Continuation.depth,Machine.Continuation.extend,Machine.withContinuation,count];omega))))

theorem every_episode_advances_the_real_native_boundary (state : State) (command : Command state) :
    boundary state+4 ≤ boundary (next state command) := by
  cases generated : inspect state command.raw with
  | none => simp only [next,generated,boundary];change _ ≤ state.model.source.history.length+2+(state.cut+4);omega
  | some entry =>
    have size : (emitter state command.raw entry).history.length = MaterialRoundSource.depth (supplied state command.raw) (count state)+2 := by
      change (RoundArchive.history (MaterialRoundSource.supplied (supplied state command.raw) (count state) (arrival state command.raw)).source
        (count state+1) (MaterialRoundSource.recovery (supplied state command.raw) (count state) (arrival state command.raw))).length = _
      rw [RoundArchive.history_is_the_entire_actual_snapshot_and_new_arrival,List.length_append,RoundArchive.snapshot_length];rfl
    simp only [next,generated,boundary]
    change state.model.source.history.length+2+state.cut+4 ≤ (emitter state command.raw entry).history.length+2+6
    rw [size]
    change _ ≤ state.model.source.history.length+1+(state.cut+2)+2+2+6
    omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RoundEpisodePrefix
