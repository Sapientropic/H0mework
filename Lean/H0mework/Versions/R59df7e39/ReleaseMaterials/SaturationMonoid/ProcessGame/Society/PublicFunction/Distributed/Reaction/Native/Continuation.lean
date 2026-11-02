import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.HistoryCoupling

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Machine.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument) (count : Nat)
  (word : RawEvent Party Good Port Technology Instrument)

/-- Earlier continuation slots are read from actual emissions, not a proposed history. -/
def past : List (RawEvent Party Good Port Technology Instrument) :=
  List.ofFn fun index : Fin count => (source.actualExecution (source.history.length+1+index.val)).submitted

/-- Insert this actual event before the still-unexecuted declared continuation. -/
def extend := source.withContinuation (past source count ++ word :: source.continuation.drop count)
def depth := source.history.length+1+count

theorem past_length : (past source count).length = count := List.length_ofFn

theorem earlier_body (ordinal : Nat) (earlier : ordinal < depth source count) :
    (extend source count word).body (source.currentAt (ordinal+1)) =
      source.body (source.currentAt (ordinal+1)) := by
  have address : (source.currentAt (ordinal+1)).round-source.code.initial.round-1 = ordinal := by
    rw [source.current_round]; omega
  change (match source.history[(source.currentAt (ordinal+1)).round-source.code.initial.round-1]? with
    | some old => old
    | none => if source.history.length < (source.currentAt (ordinal+1)).round-source.code.initial.round-1 then
        match (past source count ++ word :: source.continuation.drop count)[(source.currentAt (ordinal+1)).round-source.code.initial.round-1-source.history.length-1]? with
        | some old => old
        | none => (extend source count word).laterResponse (source.currentAt (ordinal+1))
            ((source.currentAt (ordinal+1)).round-source.code.initial.round-1-source.history.length-1)
      else (extend source count word).response (source.currentAt (ordinal+1))) = _
  rw [address]
  by_cases old : ordinal < source.history.length
  · rw [List.getElem?_eq_getElem old]
    exact (source.history_word_is_actual ordinal old).symm.trans (source.actual_word ordinal)
  · rw [List.getElem?_eq_none (Nat.le_of_not_gt old)]
    by_cases later : source.history.length < ordinal
    · have inside : ordinal-source.history.length-1 < count := by dsimp only [depth] at earlier;omega
      rw [if_pos later,List.getElem?_append_left (by rw [past_length];exact inside)]
      simp only [past,List.getElem?_ofFn]
      rw [dif_pos inside]
      have index : source.history.length+1+(ordinal-source.history.length-1) = ordinal := by omega
      rw [index]
      exact source.actual_word ordinal
    · rw [if_neg later]
      have same : ordinal = source.history.length := by omega
      subst ordinal
      rw [Machine.body,address,List.getElem?_eq_none (le_refl _),if_neg (Nat.lt_irrefl _)]
      rfl

theorem prior_events (ordinal : Nat) (earlier : ordinal < depth source count+1) :
    ProgrammeSource.rawEvent (extend source count word).input (ProgrammeHistory.visitAt source.input ordinal).current =
      ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input ordinal).current := by
  cases ordinal with
  | zero => rfl
  | succ ordinal =>
      have view : ∃ current past, (ProgrammeHistory.visitAt source.input (ordinal+1)).current = .running current past := by
        cases state : (ProgrammeHistory.visitAt source.input ordinal).current <;>
          simp only [ProgrammeHistory.visitAt,ProgrammeSource.next,state] <;> exact ⟨_,_,rfl⟩
      obtain ⟨current,previous,view⟩ := view
      have body := earlier_body source count word ordinal (by omega)
      change (extend source count word).body (source.currentAt (ordinal+1)) =
        source.body (source.currentAt (ordinal+1)) at body
      change ProgrammeSource.rawEvent (extend source count word).input _ = _
      rw [view]
      change (extend source count word).body current = source.body current
      simpa only [Machine.currentAt,view,ProgrammeSource.rawCurrent] using body

theorem prior_currents (ordinal : Nat) (earlier : ordinal ≤ depth source count+1) :
    (ProgrammeHistory.visitAt (extend source count word).input ordinal).current =
      (ProgrammeHistory.visitAt source.input ordinal).current :=
  Machine.actual_prefix_from_events source.input (extend source count word).input rfl rfl
    (depth source count+1) (prior_events source count word) ordinal earlier

theorem arrival_current : (extend source count word).currentAt (depth source count+1) =
    source.currentAt (depth source count+1) := by
  unfold Machine.currentAt
  rw [prior_currents source count word _ (le_refl _)]
  cases (ProgrammeHistory.visitAt source.input (depth source count+1)).current <;> rfl

theorem submitted : ((extend source count word).actualExecution (depth source count)).submitted = word := by
  have inside : count < (past source count ++ word :: source.continuation.drop count).length := by
    rw [List.length_append,past_length];simp
  have actual := (extend source count word).continuation_word_is_actual count inside
  change _ = (past source count ++ word :: source.continuation.drop count)[count] at actual
  rw [List.getElem_append_right (by rw [past_length])] at actual
  simpa only [extend,Machine.withContinuation,past_length,Nat.sub_self,List.getElem_cons_zero,depth] using actual

theorem before : ((extend source count word).actualExecution (depth source count)).before =
    (source.actualExecution (depth source count)).before := arrival_current source count word

theorem pending_tail :
    (extend source count word).continuation.drop (count+1) = source.continuation.drop count := by
  simp [extend,Machine.withContinuation,List.drop_append,past_length]

theorem every_pending_word_is_actually_emitted_at_its_shifted_own_cut
    (index : Nat) (inside : index < (source.continuation.drop count).length) :
    ((extend source count word).actualExecution (depth source count+1+index)).submitted =
      (source.continuation.drop count)[index] := by
  have bounded : count+1+index < (extend source count word).continuation.length := by
    simp only [extend,Machine.withContinuation,List.length_append,past_length,List.length_cons]
    omega
  have emitted := (extend source count word).continuation_word_is_actual (count+1+index) bounded
  have address : (extend source count word).history.length+1+(count+1+index) = depth source count+1+index := by
    dsimp only [extend,Machine.withContinuation,depth]
    omega
  rw [address] at emitted
  change _ = (past source count ++ word :: source.continuation.drop count)[count+1+index] at emitted
  have directBound : count+1+index < (past source count ++ word :: source.continuation.drop count).length := by
    simpa only [extend,Machine.withContinuation] using bounded
  have same : (past source count ++ word :: source.continuation.drop count)[count+1+index]'directBound =
      (source.continuation.drop count)[index] := by
    rw [List.getElem_append_right (by rw [past_length];omega)]
    have offset : count+1+index-(past source count).length = index+1 := by rw [past_length];omega
    simp only [offset,List.getElem_cons_succ]
  exact emitted.trans same

theorem actual_next : (extend source count word).currentAt (depth source count+2) =
    source.code.law.next (source.currentAt (depth source count+1)) word := by
  rw [(extend source count word).next_is_actual,submitted,arrival_current]
  rfl

theorem complete_financial_prefix (ordinal : Nat) (earlier : ordinal ≤ depth source count+1) :
    Native.Coupling.Match source.code source.input (extend source count word).input
      (Financial.accountAt source.input ordinal) (Financial.accountAt (extend source count word).input ordinal) :=
  Native.Coupling.History.complete_accounts source.code source.input (extend source count word).input
    rfl rfl (depth source count+1) (prior_events source count word)
    source.body (extend source count word).body rfl rfl ordinal earlier

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Machine.Continuation
