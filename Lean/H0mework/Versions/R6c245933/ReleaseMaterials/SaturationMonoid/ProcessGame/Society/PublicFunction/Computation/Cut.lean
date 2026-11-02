import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Inspection
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay

set_option autoImplicit false
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Cut

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry

variable {Party Good Port Technology Instrument Row : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (worker : Fin code.sites)

def isActivation : Move code → Bool
  | some ⟨.activate site,_⟩ => decide (site = worker)
  | _ => false

abbrev seed (point : Cursor code) := point.source.feedbackState point.entry point.cut

def Active (point : View (code := code))
    (rule : Distributed.Recall.Information.Agency.Protocol.Rule code) (rival : Opponent code) : Prop :=
  (seed point.point).remaining ≠ 0 ∧ code.memoryReady ((seed point.point).frame.inbox worker) = true ∧
    isActivation worker (Cursor.controller point.point rule rival
      (seed point.point).history (seed point.point).past (seed point.point).frame) = true

instance (point : View (code := code)) (rule : Distributed.Recall.Information.Agency.Protocol.Rule code)
    (rival : Opponent code) : Decidable (Active worker point rule rival) := by unfold Active;infer_instance

def Ready {fee : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    {point : View (code := code)} {rival : Opponent code} : Replay.Attempt worker fee point rival → Prop
  | .paid supported _ _ => Active worker point (Replay.protocol worker fee supported) rival
  | _ => False

instance {fee : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    {point : View (code := code)} {rival : Opponent code} (attempt : Replay.Attempt worker fee point rival) :
    Decidable (Ready worker attempt) := by cases attempt <;> unfold Ready <;> infer_instance

variable (holds : Row → Prop) [DecidablePred holds]
  (tariff : Tariff (Party := Party) (Good := Good) (Port := Port)
    (Technology := Mandate.State Party Technology) (Instrument := Instrument) Row)
  (rival : Opponent code)

/-- Each next point is the original single-cut source update. Even a withheld
or refused attempt retains that update and every effect actually caused there. -/
inductive Trace : View (code := code) → List Row → Type where
  | empty (point) : Trace point []
  | exhausted (point row rest) (empty : (seed point.point).remaining = 0) : Trace point (row::rest)
  | waited (point row rest)
      (attempt : Replay.Attempt worker (tariff.word row (rest.length+1)) point rival)
      (active : attempt.rule.isSome = true) (unready : ¬ Ready worker attempt)
      (later : Trace attempt.next (row::rest)) : Trace point (row::rest)
  | stalled (point row rest)
      (attempt : Replay.Attempt worker (tariff.word row (rest.length+1)) point rival)
      (unready : ¬ Ready worker attempt) : Trace point (row::rest)
  | failed (point row rest)
      (attempt : Replay.Attempt worker (tariff.word row (rest.length+1)) point rival)
      (ready : Ready worker attempt) (broken : ¬ holds row) : Trace point (row::rest)
  | passed (point row rest)
      (attempt : Replay.Attempt worker (tariff.word row (rest.length+1)) point rival)
      (ready : Ready worker attempt) (checked : holds row)
      (later : Trace attempt.next rest) : Trace point (row::rest)

omit [DecidablePred holds] in
private theorem next_remaining (point : View (code := code))
    (rule : Distributed.Recall.Information.Agency.Protocol.Rule code) :
    (seed (Evidence.after point rule rival).point).remaining = (seed point.point).remaining-1 := by
  have actual := Future.the_whole_future_run_is_the_actual_state point.point.source point.point.entry point.point.cut
    (Cursor.controller point.point rule rival) (term point.point.source point.point.entry point.point.cut rule).val 1
  exact (congrArg State.remaining actual).trans (Residual.remaining_is_the_seed_budget _ _ _ _ _)

def inspect (point : View (code := code)) (rows : List Row) : Trace worker holds tariff rival point rows :=
  match rows with
  | [] => .empty point
  | row::rest =>
      if exhausted : (seed point.point).remaining = 0 then .exhausted point row rest exhausted
      else
        match attempt : Replay.inspect worker (tariff.word row (rest.length+1)) point rival with
        | .unsupported outside => .stalled point row rest (.unsupported outside) (by simp [Ready])
        | .refused supported emitted illegal =>
            .stalled point row rest (.refused supported emitted illegal) (by simp [Ready])
        | .withheld supported different =>
            let tried : Replay.Attempt worker (tariff.word row (rest.length+1)) point rival := .withheld supported different
            .waited point row rest tried rfl (by simp [Ready,tried]) (inspect tried.next (row::rest))
        | .paid supported emitted legal =>
            let tried : Replay.Attempt worker (tariff.word row (rest.length+1)) point rival := .paid supported emitted legal
            if ready : Ready worker tried then
              if checked : holds row then .passed point row rest tried ready checked (inspect tried.next rest)
              else .failed point row rest tried ready checked
            else .waited point row rest tried rfl ready (inspect tried.next (row::rest))
termination_by (seed point.point).remaining + rows.length
decreasing_by
  all_goals
    simp_wf
    have decrease := next_remaining rival point (Replay.protocol worker (tariff.word row (rest.length+1)) supported)
    simp only [Replay.Attempt.next,Replay.Attempt.rule] at *
    omega

namespace Trace
variable {worker holds tariff rival} {point : View (code := code)} {rows : List Row}

def rules : {point : View (code := code)} → {rows : List Row} → Trace worker holds tariff rival point rows →
    List (Distributed.Recall.Information.Agency.Protocol.Rule code)
  | _,_,.empty _ | _,_,.exhausted .. => []
  | _,_,.stalled _ _ _ attempt _ | _,_,.failed _ _ _ attempt _ _ => attempt.rule.toList
  | _,_,.passed _ _ _ attempt _ _ later | _,_,.waited _ _ _ attempt _ _ later => attempt.rule.toList ++ later.rules

def final : {point : View (code := code)} → {rows : List Row} → Trace worker holds tariff rival point rows → View (code := code)
  | _,_,.empty point | _,_,.exhausted point .. => point
  | _,_,.stalled _ _ _ attempt _ | _,_,.failed _ _ _ attempt _ _ => attempt.next
  | _,_,.passed _ _ _ _ _ _ later | _,_,.waited _ _ _ _ _ _ later => later.final

def result : {point : View (code := code)} → {rows : List Row} → Trace worker holds tariff rival point rows →
    Option (Inspection holds rows)
  | _,_,.empty _ => some (.accepted (by simp))
  | _,_,.stalled .. | _,_,.exhausted .. => none
  | _,_,.waited _ _ _ _ _ _ later => later.result
  | _,_,.failed _ row _ _ _ broken => some (.rejected row List.mem_cons_self broken)
  | _,_,.passed _ row _ _ _ checked later =>
      match later.result with
      | none => none
      | some (.accepted all) => some (.accepted (by
          intro other inside
          rcases List.mem_cons.mp inside with same | tail
          · exact same ▸ checked
          · exact all other tail))
      | some (.rejected other inside broken) => some (.rejected other (List.mem_cons_of_mem row inside) broken)

structure Blocker (rows : List Row) where
  row : Row
  original : row ∈ rows
  position : Nat
  point : View (code := code)
  fee : RawEvent Party Good Port (Mandate.State Party Technology) Instrument
  attempt : Option (Replay.Attempt worker fee point rival)
  reason : match attempt with
    | none => (seed point.point).remaining = 0
    | some tried => ¬ Ready worker tried

def blocker : {point : View (code := code)} → {rows : List Row} → Trace worker holds tariff rival point rows →
    Option (Blocker (worker := worker) (rival := rival) rows)
  | _,_,.empty _ | _,_,.failed .. => none
  | _,_,.stalled point row _ attempt unready => some ⟨row,List.mem_cons_self,0,point,_,some attempt,unready⟩
  | _,_,.exhausted point row rest noBudget => some ⟨row,List.mem_cons_self,0,point,tariff.word row (rest.length+1),none,noBudget⟩
  | _,_,.waited _ _ _ attempt _ _ later => later.blocker.map fun stopped =>
      ⟨stopped.row,stopped.original,attempt.rule.toList.length+stopped.position,
        stopped.point,stopped.fee,stopped.attempt,stopped.reason⟩
  | _,_,.passed _ row _ attempt _ _ later => later.blocker.map fun stopped =>
      ⟨stopped.row,List.mem_cons_of_mem row stopped.original,attempt.rule.toList.length+stopped.position,
        stopped.point,stopped.fee,stopped.attempt,stopped.reason⟩

def allRowsActivatedAndPaid : {point : View (code := code)} → {rows : List Row} → Trace worker holds tariff rival point rows → Prop
  | _,_,.empty _ | _,_,.failed .. => True
  | _,_,.stalled .. | _,_,.exhausted .. => False
  | _,_,.waited _ _ _ _ _ _ later => later.allRowsActivatedAndPaid
  | _,_,.passed _ _ _ _ _ _ later => later.allRowsActivatedAndPaid

omit [DecidablePred holds] in
theorem a_released_inspection_has_only_actual_paid_activations
    (trace : Trace worker holds tariff rival point rows) (inspection : Inspection holds rows)
    (finished : trace.result = some inspection) : trace.allRowsActivatedAndPaid := by
  induction trace with
  | empty | failed | stalled | exhausted => simp_all only [result,allRowsActivatedAndPaid,reduceCtorEq]
  | waited _ _ _ _ _ _ _ ih => exact ih inspection finished
  | passed _ _ _ _ _ _ later ih =>
      simp only [result] at finished
      cases produced : later.result with
      | none => simp only [produced] at finished;cases finished
      | some inspection => exact ih inspection produced

omit [DecidablePred holds] in
theorem every_trace_produces_a_row_decision_or_an_exact_actual_cut_blocker
    (trace : Trace worker holds tariff rival point rows) :
    (∃ inspection, trace.result = some inspection) ∨ (∃ stopped, trace.blocker = some stopped) := by
  induction trace with
  | empty | failed => exact .inl ⟨_,rfl⟩
  | stalled | exhausted => exact .inr ⟨_,rfl⟩
  | waited _ _ _ attempt _ _ later ih =>
      rcases ih with ⟨inspection,finished⟩ | ⟨stopped,blocked⟩
      · exact .inl ⟨inspection,finished⟩
      · exact .inr ⟨⟨stopped.row,stopped.original,attempt.rule.toList.length+stopped.position,
          stopped.point,stopped.fee,stopped.attempt,stopped.reason⟩,by simp only [blocker,blocked,Option.map_some]⟩
  | passed before head tail attempt ready checked later ih =>
      rcases ih with ⟨inspection,finished⟩ | ⟨stopped,blocked⟩
      · cases inspection with
        | accepted all =>
            refine .inl ⟨.accepted ?_,?_⟩
            · intro row inside
              rcases List.mem_cons.mp inside with same | rest
              · exact same ▸ checked
              · exact all row rest
            · simp only [result,finished]
        | rejected row inside broken =>
            exact .inl ⟨.rejected row (List.mem_cons_of_mem head inside) broken,by simp only [result,finished]⟩
      · exact .inr ⟨⟨stopped.row,List.mem_cons_of_mem head stopped.original,attempt.rule.toList.length+stopped.position,
          stopped.point,stopped.fee,stopped.attempt,stopped.reason⟩,by simp only [blocker,blocked,Option.map_some]⟩

omit [DecidablePred holds] in
theorem final_is_generated_only_by_its_actual_single_cut_rules
    (trace : Trace worker holds tariff rival point rows) :
    trace.final.point = trace.rules.foldl (fun current rule => current.after rule rival) point.point := by
  induction trace with
  | empty | exhausted => rfl
  | stalled _ _ _ attempt | failed _ _ _ attempt => cases attempt <;> rfl
  | passed _ _ _ attempt _ _ _ ih | waited _ _ _ attempt _ _ _ ih =>
      simp only [rules,final,List.foldl_append]
      rw [ih]
      congr 1
      cases attempt <;> rfl


omit [DecidablePred holds] in
theorem every_blocker_is_located_at_its_actual_rule_prefix
    (trace : Trace worker holds tariff rival point rows)
    (stopped : Blocker (worker := worker) (rival := rival) rows)
    (found : trace.blocker = some stopped) :
    stopped.position ≤ trace.rules.length ∧
      stopped.point.point = (trace.rules.take stopped.position).foldl
        (fun current rule => current.after rule rival) point.point := by
  induction trace with
  | empty | failed => simp only [blocker] at found;cases found
  | stalled | exhausted =>
      cases Option.some.inj found
      exact ⟨Nat.zero_le _,rfl⟩
  | waited before row rest attempt active unready later ih
  | passed before row rest attempt ready checked later ih =>
      simp only [blocker] at found
      cases present : later.blocker with
      | none => simp only [present,Option.map_none] at found;cases found
      | some previous =>
          simp only [present,Option.map_some] at found
          cases Option.some.inj found
          obtain ⟨bounded,located⟩ := ih previous present
          refine ⟨by simpa only [rules,List.length_append] using Nat.add_le_add_left bounded attempt.rule.toList.length,?_⟩
          have next : attempt.next.point = attempt.rule.toList.foldl
              (fun current rule => current.after rule rival) before.point := by cases attempt <;> rfl
          simpa only [rules,List.take_append,Nat.add_sub_cancel_left,
            List.take_of_length_le (Nat.le_add_right _ _),List.foldl_append,←next] using located

end Trace
end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Cut
