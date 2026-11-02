import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Splice

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

abbrev Rule := @Distributed.Recall.Information.Agency.Protocol.Rule

def word (controls : List (Rule code)) : Program code controls.length := ⟨controls,Nat.le_refl _⟩
def install (point : Cursor code) (rival : Opponent code) (controls : List (Rule code)) : Cursor code :=
  controls.foldl (fun current rule => current.after rule rival) point

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem singleton_stage (head reference : Rule code) (offset : Nat) :
    (word [head]).at reference offset = head := by
  cases offset <;> simp [word,Continuation.Whole.Program.at]

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem first_stage (head reference : Rule code) (tail : List (Rule code)) :
    (word (head::tail)).at reference 0 = head := rfl

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem tail_stage (head reference : Rule code) (tail : List (Rule code))
    (nonempty : tail ≠ []) (offset : Nat) :
    (word (head::tail)).at reference (offset+1) = (word tail).at reference offset := by
  cases tail with
  | nil => exact False.elim (nonempty rfl)
  | cons next rest => simp only [word,Continuation.Whole.Program.at,List.getElem?_cons_succ,List.getLast?_cons_cons]

/-- Repeated takeovers assemble the same entire decision function. The original
    owner clock is retained, and the last installed stage persists. -/
theorem entry_assembly (point : Cursor code) (rival : Opponent code) (reference : Rule code)
    (controls : List (Rule code)) (nonempty : controls ≠ []) :
    (install point rival controls).entry = entry point reference (word controls) rival := by
  induction controls generalizing point with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail ih =>
      cases tail with
      | nil =>
          apply congrArg (fun response => (⟨response,point.entry.budget⟩ : Input code))
          funext history past frame
          change (if history.length < point.history.length+1+point.cut then point.entry.opponent history past frame
            else Distributed.Recall.Information.Agency.Protocol.driver code point.ownerStart head rival history past frame) = _
          simp only [Continuation.Whole.controller,singleton_stage]
      | cons next rest =>
          change (install (point.after head rival) rival (next::rest)).entry = _
          rw [ih (point.after head rival) (by simp)]
          apply congrArg (fun response => (⟨response,point.entry.budget⟩ : Input code))
          funext history past frame
          change (if history.length < point.history.length+1+(point.cut+1) then
              (if history.length < point.history.length+1+point.cut then point.entry.opponent history past frame
                else Distributed.Recall.Information.Agency.Protocol.driver code point.ownerStart head rival history past frame)
            else Distributed.Recall.Information.Agency.Protocol.driver code point.ownerStart ((word (next::rest)).at reference
              (history.length-(point.history.length+1+(point.cut+1)))) rival history past frame) =
            (if history.length < point.history.length+1+point.cut then point.entry.opponent history past frame
            else Distributed.Recall.Information.Agency.Protocol.driver code point.ownerStart ((word (head::next::rest)).at reference
              (history.length-(point.history.length+1+point.cut))) rival history past frame)
          by_cases earlier : history.length < point.history.length+1+point.cut
          · simp only [if_pos earlier,if_pos (show history.length < point.history.length+1+(point.cut+1) by omega)]
          · by_cases first : history.length = point.history.length+1+point.cut
            · rw [if_pos (by omega),if_neg earlier,if_neg earlier,
                show history.length-(point.history.length+1+point.cut) = 0 by omega,first_stage]
            · rw [if_neg (by omega),if_neg earlier,
                show history.length-(point.history.length+1+point.cut) =
                  (history.length-(point.history.length+1+(point.cut+1)))+1 by omega,
                tail_stage head reference (next::rest) (by simp)]


theorem source_shape (point : Cursor code) (rival : Opponent code) (controls : List (Rule code)) :
    (install point rival controls).source =
      {point.source with
        feedback? := some (install point rival controls).entry
        feedbackOverrides := (install point rival controls).overrides} := by
  induction controls generalizing point with
  | nil => rfl
  | cons head tail ih =>
      change (install (point.after head rival) rival tail).source = _
      rw [ih]
      rfl

private theorem preserves_old_policy (point : Cursor code) (rival : Opponent code)
    (controls : List (Rule code)) (index : Nat) (earlier : index < point.cut) :
    (install point rival controls).source.feedbackPolicy index = point.source.feedbackPolicy index := by
  induction controls generalizing point with
  | nil => rfl
  | cons head tail ih =>
      change (install (point.after head rival) rival tail).source.feedbackPolicy index = _
      exact (ih (point.after head rival) (by change index < point.cut+1;omega)).trans
        (Execution.policy_before {point.source with feedback? := some (point.targetInput head rival)}
          point.cut (term point.source point.entry point.cut head).val index earlier)

private theorem whole_policy (point : Cursor code) (rival : Opponent code) (reference : Rule code)
    (controls : List (Rule code)) (offset : Nat) :
    (source point reference (word controls) rival).feedbackPolicy (point.cut+offset) =
      if offset < Cut.horizon point.source point.entry point.cut then
        some ((word controls).at reference offset).work.val
      else point.source.feedbackPolicy (point.cut+offset) := by
  rw [Execution.policy_at]
  by_cases inside : offset < Cut.horizon point.source point.entry point.cut
  · simp only [if_pos inside,Residual.scheduleAt,Continuation.Whole.schedule,
      List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some]
  · simp only [if_neg inside,Residual.scheduleAt]
    rw [List.getElem?_eq_none (by simpa only [Continuation.Whole.schedule,List.length_map,List.length_range] using Nat.le_of_not_gt inside)]
    rfl

private theorem head_policy (point : Cursor code) (rival : Opponent code) (head : Rule code)
    (offset : Nat) : (point.after head rival).source.feedbackPolicy (point.cut+offset) =
      if offset < Cut.horizon point.source point.entry point.cut then some head.work.val
      else point.source.feedbackPolicy (point.cut+offset) := by
  change (Execution.target {point.source with feedback? := some (point.targetInput head rival)} point.cut
    (term point.source point.entry point.cut head).val).feedbackPolicy (point.cut+offset) = _
  rw [Execution.policy_at]
  simp only [Residual.scheduleAt,term,List.getElem?_replicate]
  split <;> rfl

private theorem remaining_after (point : Cursor code) (rival : Opponent code) (head : Rule code) :
    Cut.horizon (point.after head rival).source (point.after head rival).entry (point.after head rival).cut =
      Cut.horizon point.source point.entry point.cut-1 := by
  have actual := Future.the_whole_future_run_is_the_actual_state point.source point.entry point.cut
    (Cursor.controller point head rival) (term point.source point.entry point.cut head).val 1
  exact (congrArg State.remaining actual).trans (Residual.remaining_is_the_seed_budget _ _ _ _ _)

theorem policy_assembly (point : Cursor code) (rival : Opponent code) (reference : Rule code)
    (controls : List (Rule code)) (nonempty : controls ≠ []) :
    (install point rival controls).source.feedbackPolicy = (source point reference (word controls) rival).feedbackPolicy := by
  induction controls generalizing point with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail ih =>
      funext index
      by_cases earlier : index < point.cut
      · rw [preserves_old_policy point rival (head::tail) index earlier]
        exact (Execution.policy_before {point.source with feedback? := some (entry point reference (word (head::tail)) rival)}
          point.cut (schedule point reference (word (head::tail))).val index earlier).symm
      · let offset := index-point.cut
        have address : index = point.cut+offset := by dsimp only [offset];omega
        cases tail with
        | nil =>
            rw [address,show install point rival [head] = point.after head rival from rfl,head_policy,whole_policy]
            simp only [singleton_stage]
        | cons next rest =>
            change (install (point.after head rival) rival (next::rest)).source.feedbackPolicy index = _
            rw [ih (point.after head rival) (by simp)]
            by_cases first : offset = 0
            · have beforeNext : index < (point.after head rival).cut := by change index < point.cut+1;omega
              rw [Execution.policy_before _ (point.after head rival).cut _ index beforeNext]
              change (point.after head rival).source.feedbackPolicy index = _
              rw [address,first,head_policy,whole_policy,first_stage]
            · let later := offset-1
              have shift : offset = later+1 := by dsimp only [later];omega
              have nextAddress : index = (point.after head rival).cut+later := by change index = point.cut+1+later;omega
              have wholeIndex : index = point.cut+(later+1) := by omega
              have left := whole_policy (point.after head rival) rival reference (next::rest) later
              rw [←nextAddress,remaining_after] at left
              have right := whole_policy point rival reference (head::next::rest) (later+1)
              rw [←wholeIndex,tail_stage head reference (next::rest) (by simp)] at right
              have old := head_policy point rival head (later+1)
              rw [←wholeIndex] at old
              rw [left,right,old]
              have equivalent : (later < Cut.horizon point.source point.entry point.cut-1) ↔
                  (later+1 < Cut.horizon point.source point.entry point.cut) := by omega
              by_cases used : later+1 < Cut.horizon point.source point.entry point.cut
              · simp only [if_pos used,if_pos (equivalent.mpr used)]
              · simp only [if_neg used,if_neg (fun lt => used (equivalent.mp lt))]


private theorem states_of_policies (point : Cursor code) (input : Input code)
    (left right : List (Nat × Option code.Policy))
    (policies : ({point.source with feedback? := some input,feedbackOverrides := left}).feedbackPolicy =
      ({point.source with feedback? := some input,feedbackOverrides := right}).feedbackPolicy) :
    ({point.source with feedback? := some input,feedbackOverrides := left}).feedbackState input =
      ({point.source with feedback? := some input,feedbackOverrides := right}).feedbackState input := by
  funext count
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Machine.feedbackState,Machine.feedbackState,policies,ih]

private theorem body_of_policies (point : Cursor code) (input : Input code)
    (left right : List (Nat × Option code.Policy))
    (policies : ({point.source with feedback? := some input,feedbackOverrides := left}).feedbackPolicy =
      ({point.source with feedback? := some input,feedbackOverrides := right}).feedbackPolicy) :
    ({point.source with feedback? := some input,feedbackOverrides := left}).body =
      ({point.source with feedback? := some input,feedbackOverrides := right}).body := by
  have states := states_of_policies point input left right policies
  funext current
  unfold Machine.body Machine.laterResponse
  dsimp only
  rw [policies,states]
  rfl

private theorem original_policy_kept (point : Cursor code) (rival : Opponent code) (controls : List (Rule code)) :
    (install point rival controls).source.policy? = point.source.policy? := by
  induction controls generalizing point with
  | nil => rfl
  | cons head tail ih => exact ih (point.after head rival)

private theorem initial_kept (point : Cursor code) (rival : Opponent code) (controls : List (Rule code))
    (input : Input code) : (install point rival controls).source.feedbackInitial input = point.source.feedbackInitial input := by
  induction controls generalizing point with
  | nil => rfl
  | cons head tail ih => exact ih (point.after head rival)

theorem body_assembly (point : Cursor code) (rival : Opponent code) (reference : Rule code)
    (controls : List (Rule code)) (nonempty : controls ≠ []) :
    (install point rival controls).source.body = (source point reference (word controls) rival).body := by
  have policies := policy_assembly point rival reference controls nonempty
  rw [source_shape,entry_assembly point rival reference controls nonempty]
  apply body_of_policies point (entry point reference (word controls) rival)
    (install point rival controls).overrides
    (point.overrides ++ Execution.entries
      {point.source with feedback? := some (entry point reference (word controls) rival)} point.cut
      (schedule point reference (word controls)).val)
  unfold Machine.feedbackPolicy at policies ⊢
  rw [original_policy_kept] at policies
  exact policies

theorem input_assembly (point : Cursor code) (rival : Opponent code) (reference : Rule code)
    (controls : List (Rule code)) (nonempty : controls ≠ []) :
    (install point rival controls).source.input = (source point reference (word controls) rival).input := by
  have bodies := body_assembly point rival reference controls nonempty
  have reports : (install point rival controls).source.report = (source point reference (word controls) rival).report := by
    funext current
    exact congrArg (ProgrammeSource.ProgrammeReport.original current) (congrFun bodies current)
  simp only [Machine.input,bodies,reports]

theorem every_actual_raw_submission_is_the_assembled_whole_occurrence
    (point : Cursor code) (rival : Opponent code) (reference : Rule code)
    (controls : List (Rule code)) (nonempty : controls ≠ []) (ordinal : Nat) :
    let left := (install point rival controls).source.actualExecution ordinal
    let right := (source point reference (word controls) rival).actualExecution ordinal
    left.before = right.before ∧ left.submitted = right.submitted := by
  have inputs := input_assembly point rival reference controls nonempty
  constructor <;> (unfold Machine.actualExecution;rw [inputs])

theorem states_assembly (point : Cursor code) (rival : Opponent code) (reference : Rule code)
    (controls : List (Rule code)) (nonempty : controls ≠ []) :
    (install point rival controls).source.feedbackState (install point rival controls).entry =
      (source point reference (word controls) rival).feedbackState (entry point reference (word controls) rival) := by
  have policies := policy_assembly point rival reference controls nonempty
  have inputs := entry_assembly point rival reference controls nonempty
  funext count
  induction count with
  | zero =>
      rw [Machine.feedbackState,Machine.feedbackState,inputs]
      exact initial_kept point rival controls _
  | succ count ih =>
      rw [Machine.feedbackState,Machine.feedbackState,policies,ih,inputs]


omit [DecidableEq Technology] in
private theorem accounts_of_equal_inputs
    (first second : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Instrument)
    (same : first = second) (ordinal : Nat) :
    HEq (Financial.accountAt first ordinal) (Financial.accountAt second ordinal) := by
  cases same
  rfl

theorem every_native_financial_account_is_the_same_actual_account
    (point : Cursor code) (rival : Opponent code) (reference : Rule code)
    (controls : List (Rule code)) (nonempty : controls ≠ []) (ordinal : Nat) :
    HEq (Financial.accountAt (install point rival controls).source.input ordinal)
      (Financial.accountAt (source point reference (word controls) rival).input ordinal) :=
  accounts_of_equal_inputs _ _ (input_assembly point rival reference controls nonempty) ordinal

/-- The actual recursive selector supplies its own word. Stopping before any
    installation is an identity; a nonempty chain has the assembled source input. -/
theorem every_recursive_selection_chain_generates_its_identity_or_whole_occurrence
    (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    {fuel : Nat} {domain : List (Cursor model.source.code)}
    {reference : Rule model.source.code}
    (chain : Installation.Chain model fuel domain reference)
    (point : Cursor model.source.code) (rival : Opponent model.source.code) :
    (chain.rules = [] ∧ chain.realize point rival = point) ∨
      (chain.rules ≠ [] ∧ (chain.realize point rival).source.input =
        (source point reference (word chain.rules) rival).input) := by
  by_cases empty : chain.rules = []
  · left
    refine ⟨empty,?_⟩
    rw [chain.realization_is_the_actual_installed_rule_fold,Installation.Chain.fold,empty]
    rfl
  · right
    refine ⟨empty,?_⟩
    rw [chain.realization_is_the_actual_installed_rule_fold]
    exact input_assembly point rival reference chain.rules empty

section RootConsumer
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (point : Cursor model.source.code) (rival : Opponent model.source.code)
  (reference : Rule model.source.code) (controls : List (Rule model.source.code))

abbrev bound := Replanning.native model (install point rival controls)
abbrev facade := Native.AuthorityRuntime.facade (bound model point rival controls)
abbrev activated := Inquiry.Runtime.readState (bound model point rival controls) (depth (install point rival controls))
abbrev native := Inquiry.Runtime.read (bound model point rival controls) (depth (install point rival controls))

theorem the_actual_recursive_root_consumes_its_whole_word_occurrence_accounts_and_next
    (nonempty : controls ≠ []) :
    let current := activated model point rival controls
    (install point rival controls).source.input = (source point reference (word controls) rival).input ∧
      (∀ ordinal,let left := (install point rival controls).source.actualExecution ordinal
        let right := (source point reference (word controls) rival).actualExecution ordinal
        left.before = right.before ∧ left.submitted = right.submitted) ∧
      (∀ ordinal,HEq (Financial.accountAt (install point rival controls).source.input ordinal)
        (Financial.accountAt (source point reference (word controls) rival).input ordinal)) ∧
      HEq (native model point rival controls).joint.finance
        (Financial.accountAt (source point reference (word controls) rival).input (arrival (install point rival controls)+1)) ∧
      HEq ((facade model point rival controls).readoutAt current .responsibilities)
        (current.tick.generated.projectionOutcome (.component ())) ∧
      HEq current.tick.generated.wholeLedgerWriteBack
        (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
      current.tick.nextCurrent = (facade model point rival controls).process.stateAt
        ((facade model point rival controls).process.successor current.state) := by
  let current := activated model point rival controls
  have rooted := (facade model point rival controls).readoutAt_factorizes current .responsibilities
  refine ⟨input_assembly point rival reference controls nonempty,
    every_actual_raw_submission_is_the_assembled_whole_occurrence point rival reference controls nonempty,
    every_native_financial_account_is_the_same_actual_account point rival reference controls nonempty,
    ?_,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
  have own : (native model point rival controls).joint.finance =
      Financial.accountAt (install point rival controls).source.input (arrival (install point rival controls)+1) := by
    rw [(native model point rival controls).joint_exact]
    have account := (Native.generate (install point rival controls).source (depth (install point rival controls))).finance_exact
    have address : depth (install point rival controls)+2 = arrival (install point rival controls)+1 := by
      dsimp only [depth,arrival]
      omega
    rw [address] at account
    exact account
  exact (heq_of_eq own).trans
    (every_native_financial_account_is_the_same_actual_account point rival reference controls nonempty _)

end RootConsumer

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Splice
