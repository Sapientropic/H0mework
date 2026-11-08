import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletOmissionSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletOmissionProgress
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource (Active State queued prepared delay strip ClockFree)
open InletOmissionSource
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
local notation "Word" => RawEvent Party Good Port (Mandate.State Party Technology) Instrument
local notation "Request" => Institutions.Capitalism.Universal.Source.Program.Request Party Good Port (Mandate.State Party Technology) Instrument
local notation "Current" => RawCurrent Party Good (Mandate.State Party Technology) Instrument
local notation "Command" => InletOmissionSource.Command (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
private theorem prepared_material (state : State old instructions) :
    strip (EventStep.seed (prepared old instructions state)).current = strip (EventStep.seed state.cursor).current := by
  have facts := SilentWindow.preserves_the_actual_state state.cursor (delay old instructions state)
  exact RawCurrent.ext _ _ _ _ facts.stock facts.claims facts.technology rfl rfl

private theorem delay_bound (state : State old instructions) : delay old instructions state ≤ 1 := by
  unfold delay
  split <;> omega

private theorem prepared_external (state : State old instructions)
    (aligned : state.cursor.ownerStart ≤ (EventStep.seed state.cursor).history.length) :
    Distributed.Recall.Information.Agency.ownerAt (Active old instructions)
      (prepared old instructions state).ownerStart (EventStep.seed (prepared old instructions state)).history.length = none := by
  have facts := SilentWindow.preserves_the_actual_state state.cursor (delay old instructions state)
  rw [facts.roster,facts.history]
  unfold delay
  split
  · rename_i outside
    simpa only [Nat.add_zero] using outside
  · rename_i inside
    unfold Distributed.Recall.Information.Agency.ownerAt at inside ⊢
    split at inside
    · rename_i positive
      rw [dif_pos positive]
      split at inside
      · rename_i even
        have odd : ((EventStep.seed state.cursor).history.length + 1 - state.cursor.ownerStart) % 2 ≠ 0 := by omega
        rw [if_neg odd]
      · exact False.elim (inside rfl)
    · exact False.elim (inside rfl)

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem admitted_event (request : Request) (admitted : request ∈ instructions) :
    Event.adversary request ∈ (Active old instructions).eventAlphabet := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨request,admitted,rfl⟩

private theorem external_success (state : State old instructions) (head : Request)
    (aligned : state.cursor.ownerStart ≤ (EventStep.seed state.cursor).history.length)
    (fuel : 2 ≤ (EventStep.seed state.cursor).remaining)
    (admitted : head ∈ instructions)
    (valid : old.law.Valid (EventStep.seed (prepared old instructions state)).current head) :
    LiveProductionInletSource.assess old instructions (prepared old instructions state) SilentWindow.quiet true head = .executed := by
  let chosen : Choice (Active old instructions) := ⟨.adversary head,admitted_event old instructions head admitted⟩
  have found : LiveProductionInletSource.request old instructions head = some chosen := by
    simp only [LiveProductionInletSource.request,dif_pos (admitted_event old instructions head admitted)]
    rfl
  have live : (EventStep.seed (prepared old instructions state)).remaining ≠ 0 := by
    have facts := SilentWindow.preserves_the_actual_state state.cursor (delay old instructions state)
    rw [facts.fuel]
    have := delay_bound old instructions state
    omega
  have call : (LiveProductionInletSource.row old instructions (prepared old instructions state) SilentWindow.quiet true head).call = .external (some chosen) := by
    change StageTrace.capture _ _ _ _ = _
    rw [StageTrace.capture,if_neg live,prepared_external old instructions state aligned]
    change (.external (LiveProductionInletSource.request old instructions head) : ControlExecution.Call (Active old instructions)) = _
    rw [found]
  have word := LiveProductionInletConsumer.actual_external_word old instructions (prepared old instructions state) SilentWindow.quiet true head chosen call found
  have paid : ∀ item ∈ StageTrace.items (LiveProductionInletSource.row old instructions (prepared old instructions state) SilentWindow.quiet true head), old.law.Valid item.before item.request := by
    change ∀ item ∈ old.law.rawItems (EventStep.seed (prepared old instructions state)).current
      (LiveProductionInletSource.row old instructions (prepared old instructions state) SilentWindow.quiet true head).submitted, _
    rw [word]
    simpa only [RawLaw.rawItems,RawLaw.execute,List.mem_singleton,forall_eq] using valid
  simp only [LiveProductionInletSource.assess,call,if_pos paid]


structure Timing (state : State old instructions) (command : Command) : Prop where
  aligned : (after old instructions state command).cursor.ownerStart ≤
    (EventStep.seed (after old instructions state command).cursor).history.length
  fuel : (EventStep.seed (after old instructions state command).cursor).remaining =
    (EventStep.seed state.cursor).remaining - (delay old instructions state + 1)
  length : (stages old instructions state command).length ≤ 2

private theorem timing (state : State old instructions) (command : Command)
    (aligned : state.cursor.ownerStart ≤ (EventStep.seed state.cursor).history.length) : Timing old instructions state command := by
  have preservation := SilentWindow.preserves_the_actual_state state.cursor (delay old instructions state)
  have history : (EventStep.seed (after old instructions state command).cursor).history.length =
      (EventStep.seed (prepared old instructions state)).history.length + 1 := by
    change (EventStep.seed ((prepared old instructions state).after _ _)).history.length = _
    rw [EventStep.actual_next_state]
    simp only [Reaction.Feedback.advance,List.length_append,List.length_singleton]
  have remaining : (EventStep.seed (after old instructions state command).cursor).remaining =
      (EventStep.seed (prepared old instructions state)).remaining - 1 := by
    change (EventStep.seed ((prepared old instructions state).after _ _)).remaining = _
    rw [EventStep.actual_next_state]
    rfl
  refine ⟨?_,?_,?_⟩
  · change (prepared old instructions state).ownerStart ≤ _
    rw [history,preservation.history,preservation.roster]
    omega
  · rw [remaining,preservation.fuel]
    exact Nat.sub_sub _ _ _
  · rw [stages,List.length_append,SilentWindow.stage_count,List.length_singleton]
    have := delay_bound old instructions state
    omega

structure Paid (state : State old instructions) (command : Command) (head : Request) (tail : Word) : Prop where
  observe : observe old instructions state command = some .executed
  pending : (after old instructions state command).pending = tail ++ command.incoming
  word : (row old instructions state command).submitted = [head]
  current : strip (EventStep.seed (after old instructions state command).cursor).current =
    old.law.step (strip (EventStep.seed state.cursor).current) head

private theorem paid (clockFree : ClockFree old instructions) (state : State old instructions) (command : Command)
    (head : Request) (tail : Word) (pending : state.pending = head :: tail)
    (aligned : state.cursor.ownerStart ≤ (EventStep.seed state.cursor).history.length)
    (fuel : 2 ≤ (EventStep.seed state.cursor).remaining)
    (admitted : head ∈ instructions)
    (valid : old.law.Valid (strip (EventStep.seed state.cursor).current) head)
    (enabled : command.enabled = true) : Paid old instructions state command head tail := by
  have resource : old.law.Valid (EventStep.seed (prepared old instructions state)).current head := by
    apply (clockFree _ head admitted).mpr
    rwa [prepared_material old instructions state]
  have success := external_success old instructions state head aligned fuel admitted resource
  have queue : (queued old instructions state command.incoming).pending ++
      (localCommand old instructions command).incoming = head :: (tail ++ command.incoming) := by
    simp only [queued,List.append_nil,pending,List.cons_append]
  have chosen : stage old instructions state command = (SilentWindow.quiet,LiveProductionInletSource.rival old instructions true head) := by
    unfold stage LiveProductionInletSource.stage
    rw [queue]
    simp only [enabled]
  have actual := LiveProductionInletConsumer.executed_keeps_the_actual_input_and_next old instructions
    (prepared old instructions state) SilentWindow.quiet true head success
  have prior := InletClockedProgress.funded_original_prefix_completes old instructions clockFree
    (fun _ => command.incoming) [head] tail state pending aligned (by simpa using fuel)
    (by intro request member;cases List.mem_singleton.mp member;exact admitted)
    (by
      intro item member
      simp only [RawLaw.rawItems,RawLaw.execute,List.mem_cons,List.not_mem_nil,or_false] at member
      cases member
      exact valid)
  refine ⟨?_,?_,?_,?_⟩
  · simp only [observe,pending,List.cons_append,enabled,success]
  · unfold after LiveProductionInletSource.step
    rw [queue]
    change (if LiveProductionInletSource.assess old instructions (prepared old instructions state) SilentWindow.quiet command.enabled head = .executed then tail ++ command.incoming else _) = _
    rw [enabled,if_pos success]
  · change (StageTrace.material _ _ (stage old instructions state command).2).submitted = _
    rw [chosen]
    exact actual.2.1
  · have same : after old instructions state command = InletClockedSource.after old instructions state command.incoming := by
      unfold after localCommand
      rw [enabled]
    rw [same]
    exact prior.current

structure Held (state : State old instructions) (command : Command) : Prop where
  observe : observe old instructions state command = some .withheld
  pending : (after old instructions state command).pending = state.pending ++ command.incoming
  word : (row old instructions state command).submitted = []
  current : strip (EventStep.seed (after old instructions state command).cursor).current =
    strip (EventStep.seed state.cursor).current

private theorem held (state : State old instructions) (command : Command) (head : Request) (tail : Word)
    (pending : state.pending = head :: tail)
    (aligned : state.cursor.ownerStart ≤ (EventStep.seed state.cursor).history.length)
    (fuel : 2 ≤ (EventStep.seed state.cursor).remaining) (disabled : command.enabled = false) :
    Held old instructions state command := by
  have live : (EventStep.seed (prepared old instructions state)).remaining ≠ 0 := by
    have preservation := SilentWindow.preserves_the_actual_state state.cursor (delay old instructions state)
    rw [preservation.fuel]
    have := delay_bound old instructions state
    omega
  have call : (LiveProductionInletSource.row old instructions (prepared old instructions state) SilentWindow.quiet false head).call = .external none := by
    change StageTrace.capture _ _ _ _ = _
    rw [StageTrace.capture,if_neg live,prepared_external old instructions state aligned]
    rfl
  have observation : observe old instructions state command = some .withheld := by
    simp only [observe,pending,List.cons_append,disabled,LiveProductionInletSource.assess,call]
    rfl
  have queue : (queued old instructions state command.incoming).pending ++
      (localCommand old instructions command).incoming = head :: (tail ++ command.incoming) := by
    simp only [queued,List.append_nil,pending,List.cons_append]
  have chosen : stage old instructions state command = (SilentWindow.quiet,SilentWindow.environment) := by
    unfold stage LiveProductionInletSource.stage
    rw [queue]
    simp only [disabled,LiveProductionInletSource.rival]
    rfl
  have cursor : (after old instructions state command).cursor =
      SilentWindow.cursorAt state.cursor (delay old instructions state + 1) := by
    change ((prepared old instructions state).after (stage old instructions state command).1 (stage old instructions state command).2) = _
    rw [chosen]
    rfl
  refine ⟨observation,?_,?_,?_⟩
  · unfold after LiveProductionInletSource.step
    rw [queue]
    change (if LiveProductionInletSource.assess old instructions (prepared old instructions state) SilentWindow.quiet command.enabled head = .executed then _ else _) = _
    rw [disabled]
    simp only [LiveProductionInletSource.assess,call]
    rw [pending]
    rfl
  · change (StageTrace.material _ _ (stage old instructions state command).2).submitted = _
    rw [chosen,(StageTrace.material_is_the_actual_step _ _ _).2]
    simp only [Feedback.word,SilentWindow.no_admitted_event]
  · rw [cursor]
    have preservation := SilentWindow.preserves_the_actual_state state.cursor (delay old instructions state + 1)
    exact RawCurrent.ext _ _ _ _ preservation.stock preservation.claims preservation.technology rfl rfl

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem execution_index (current : Current) (word : Word) (first second : Nat) :
    (old.law.execute current first word).final = (old.law.execute current second word).final ∧
      ((∀ item ∈ (old.law.execute current first word).items,old.law.Valid item.before item.request) ↔
        (∀ item ∈ (old.law.execute current second word).items,old.law.Valid item.before item.request)) := by
  induction word generalizing current first second with
  | nil => exact ⟨rfl,Iff.rfl⟩
  | cons head tail ih =>
    have rest := ih (old.law.step current head) (first + 1) (second + 1)
    refine ⟨rest.1,?_⟩
    simpa only [RawLaw.execute,List.forall_mem_cons] using and_congr Iff.rfl rest.2

structure Completes (control : Controller old instructions) (count : Nat)
    (state : State old instructions) (original tail : Word) : Prop where
  unserved : (InletOmissionSource.run old instructions control count original.length state).unserved = 0
  submitted : (InletOmissionSource.run old instructions control count original.length state).submitted = original
  pending : (InletOmissionSource.run old instructions control count original.length state).state.pending =
    tail ++ (InletOmissionSource.run old instructions control count original.length state).arrivals
  current : strip (EventStep.seed (InletOmissionSource.run old instructions control count original.length state).state.cursor).current =
    (old.law.execute (strip (EventStep.seed state.cursor).current) 0 original).final
  length : (InletOmissionSource.run old instructions control count original.length state).stages.length ≤ 2 * count

-- The only communication premise counts actual withheld calls of this run.
-- Initial validity is computed by the old law; no future successful step is a premise.
theorem funded_prefix_completes_under_actual_omission_bound (clockFree : ClockFree old instructions)
    (control : Controller old instructions) (count : Nat) (original tail : Word) (state : State old instructions)
    (allowance : Nat) (bound : original.length + allowance = count)
    (pending : state.pending = original ++ tail)
    (aligned : state.cursor.ownerStart ≤ (EventStep.seed state.cursor).history.length)
    (fuel : 2 * count ≤ (EventStep.seed state.cursor).remaining)
    (admitted : ∀ request ∈ original,request ∈ instructions)
    (resources : ∀ item ∈ old.law.rawItems (strip (EventStep.seed state.cursor).current) original,
      old.law.Valid item.before item.request)
    (within : (InletOmissionSource.run old instructions control count original.length state).withheld ≤ allowance) :
    Completes old instructions control count state original tail := by
  induction count generalizing original tail state allowance with
  | zero =>
    have empty : original = [] := List.length_eq_zero_iff.mp (by omega)
    subst original
    refine ⟨rfl,rfl,?_,rfl,by rfl⟩
    change state.pending = tail ++ []
    simpa only [List.nil_append,List.append_nil] using pending
  | succ count ih =>
    cases original with
    | nil =>
      have same : InletOmissionSource.run old instructions control (count+1) ([] : Word).length state =
          idle old instructions state 0 := stopped old instructions state control (count+1)
      refine ⟨?_,?_,?_,?_,?_⟩
      · rw [same];rfl
      · rw [same];rfl
      · rw [same]
        change state.pending = tail ++ []
        simpa only [List.nil_append,List.append_nil] using pending
      · rw [same];rfl
      · rw [same]
        change 0 ≤ _
        omega
    | cons head rest =>
      let command := control state
      have timing := timing old instructions state command aligned
      have nextFuel : 2 * count ≤ (EventStep.seed (after old instructions state command).cursor).remaining := by
        rw [timing.fuel]
        have := delay_bound old instructions state
        omega
      have originalHead : state.pending = head :: (rest ++ tail) := by
        simpa only [List.cons_append] using pending
      cases enabled : command.enabled with
      | true =>
        have phase := paid old instructions clockFree state command head (rest ++ tail) originalHead aligned
          (by omega) (admitted head (List.mem_cons_self))
          (resources ⟨0,_,head⟩ (List.mem_cons_self)) enabled
        have recursion := active old instructions state control count (head::rest).length (by simp)
        change InletOmissionSource.run old instructions control (count+1) (head::rest).length state =
          let observation := observe old instructions state command
          let later := InletOmissionSource.run old instructions control count ((head::rest).length - if observation = some .executed then 1 else 0)
            (after old instructions state command)
          ⟨later.unserved,later.state,stages old instructions state command ++ later.stages,
            (row old instructions state command).submitted ++ later.submitted,command.incoming ++ later.arrivals,
            (if observation = some .withheld then 1 else 0) + later.withheld,
            attempt old instructions state command :: later.attempts⟩ at recursion
        simp only [phase.observe,Option.some.injEq,reduceCtorEq,ite_true,ite_false,Nat.zero_add] at recursion
        rw [recursion] at within
        change (InletOmissionSource.run old instructions control count rest.length (after old instructions state command)).withheld ≤ allowance at within
        have restResources : ∀ item ∈ old.law.rawItems
            (strip (EventStep.seed (after old instructions state command).cursor).current) rest,
            old.law.Valid item.before item.request := by
          rw [phase.current]
          apply (execution_index old _ rest 1 0).2.mp
          intro item member
          exact resources item (List.mem_cons_of_mem _ member)
        have later := ih rest (tail ++ command.incoming) (after old instructions state command) allowance
          (by simp only [List.length_cons] at bound;omega)
          (by rw [phase.pending,List.append_assoc]) timing.aligned nextFuel
          (fun request member => admitted request (List.mem_cons_of_mem _ member)) restResources within
        refine ⟨?_,?_,?_,?_,?_⟩
        · rw [recursion];exact later.unserved
        · rw [recursion]
          change (row old instructions state command).submitted ++
            (InletOmissionSource.run old instructions control count rest.length (after old instructions state command)).submitted = _
          rw [phase.word,later.submitted]
          rfl
        · rw [recursion]
          change (InletOmissionSource.run old instructions control count rest.length (after old instructions state command)).state.pending =
            tail ++ (command.incoming ++ (InletOmissionSource.run old instructions control count rest.length (after old instructions state command)).arrivals)
          rw [later.pending,List.append_assoc]
        · rw [recursion]
          change strip (EventStep.seed (InletOmissionSource.run old instructions control count rest.length (after old instructions state command)).state.cursor).current = _
          rw [later.current,phase.current]
          exact (execution_index old _ rest 0 1).1
        · rw [recursion]
          change (stages old instructions state command ++ (InletOmissionSource.run old instructions control count rest.length (after old instructions state command)).stages).length ≤ _
          rw [List.length_append]
          have := timing.length
          have := later.length
          omega
      | false =>
        have phase := held old instructions state command head (rest ++ tail) originalHead aligned (by omega) enabled
        have recursion := active old instructions state control count (head::rest).length (by simp)
        change InletOmissionSource.run old instructions control (count+1) (head::rest).length state =
          let observation := observe old instructions state command
          let later := InletOmissionSource.run old instructions control count ((head::rest).length - if observation = some .executed then 1 else 0)
            (after old instructions state command)
          ⟨later.unserved,later.state,stages old instructions state command ++ later.stages,
            (row old instructions state command).submitted ++ later.submitted,command.incoming ++ later.arrivals,
            (if observation = some .withheld then 1 else 0) + later.withheld,
            attempt old instructions state command :: later.attempts⟩ at recursion
        simp only [phase.observe,Option.some.injEq,reduceCtorEq,ite_true,ite_false,Nat.sub_zero] at recursion
        rw [recursion] at within
        change 1 + (InletOmissionSource.run old instructions control count (head::rest).length (after old instructions state command)).withheld ≤ allowance at within
        cases allowance with
        | zero => omega
        | succ allowance =>
          have later := ih (head::rest) (tail ++ command.incoming) (after old instructions state command) allowance
            (by omega)
            (by rw [phase.pending,pending,List.append_assoc]) timing.aligned nextFuel admitted
            (by rwa [phase.current]) (by omega)
          refine ⟨?_,?_,?_,?_,?_⟩
          · rw [recursion];exact later.unserved
          · rw [recursion]
            change (row old instructions state command).submitted ++ _ = _
            rw [phase.word,List.nil_append]
            exact later.submitted
          · rw [recursion]
            change (InletOmissionSource.run old instructions control count (head::rest).length (after old instructions state command)).state.pending = _
            rw [later.pending,List.append_assoc]
          · rw [recursion]
            change strip (EventStep.seed (InletOmissionSource.run old instructions control count (head::rest).length (after old instructions state command)).state.cursor).current = _
            rw [later.current,phase.current]
          · rw [recursion]
            change (stages old instructions state command ++ (InletOmissionSource.run old instructions control count (head::rest).length (after old instructions state command)).stages).length ≤ _
            rw [List.length_append]
            have := timing.length
            have := later.length
            omega

theorem every_generated_record_is_native_financial (control : Controller old instructions)
    (count remaining : Nat) (state : State old instructions) (record : StageTrace.Record (code := Active old instructions))
    (inside : record ∈ StageTrace.records state.cursor (InletOmissionSource.run old instructions control count remaining state).stages) :
    (Financial.inventoryAt (InletOmissionSource.run old instructions control count remaining state).state.cursor.source.input
      (ProgrammeHistory.visitAt (InletOmissionSource.run old instructions control count remaining state).state.cursor.source.input
        (EventStep.boundary record.cursor))).filterMap
      (Financial.InstructionOrigin.instruction? (InletOmissionSource.run old instructions control count remaining state).state.cursor.source.input) =
        StageTrace.items record := by
  rw [every_run_is_the_original_execution]
  exact StageTrace.final_financial_inventory_is_the_original_record_items _ _ _ inside

theorem checked_production_completes (clockFree : ClockFree old instructions)
    (control : Controller old instructions) (state : State old instructions) (allowance : Nat)
    (checks : funded old instructions state allowance = true)
    (within : (InletOmissionSource.produce old instructions state control (state.pending.length + allowance)).withheld ≤ allowance) :
    Completes old instructions control (state.pending.length + allowance) state state.pending [] := by
  have passed := of_decide_eq_true checks
  exact funded_prefix_completes_under_actual_omission_bound old instructions clockFree control _
    state.pending [] state allowance rfl (List.append_nil _).symm
    passed.1 passed.2.1 passed.2.2.1 passed.2.2.2 within

inductive Verdict (control : Controller old instructions) (state : State old instructions) (allowance : Nat) where
  | completed (actual : Completes old instructions control (state.pending.length + allowance) state state.pending [])
  | checksFailed (checks : funded old instructions state allowance = false)
  | overrun (checks : funded old instructions state allowance = true)
      (omissions : allowance < (InletOmissionSource.produce old instructions state control (state.pending.length + allowance)).withheld)

-- Both the resource gate and the communication count are calculated here.
def inspect (clockFree : ClockFree old instructions) (control : Controller old instructions)
    (state : State old instructions) (allowance : Nat) : Verdict old instructions control state allowance :=
  if checks : funded old instructions state allowance = true then
    if within : (InletOmissionSource.produce old instructions state control (state.pending.length + allowance)).withheld ≤ allowance then
      .completed (checked_production_completes old instructions clockFree control state allowance checks within)
    else .overrun checks (by omega)
  else .checksFailed (by cases h : funded old instructions state allowance <;> simp_all)

private theorem the_attempt_row_is_in_its_actual_block (state : State old instructions) (command : Command) :
    (row old instructions state command) ∈ StageTrace.records state.cursor (stages old instructions state command) := by
  rw [stages,OriginQueue.records_append,SilentWindow.execution_is_the_actual_cursor]
  apply List.mem_append_right
  exact List.mem_cons_self

theorem every_attempt_keeps_its_queue_control_observation_and_actual_row (control : Controller old instructions)
    (count remaining : Nat) (state : State old instructions) (entry : Attempt old instructions)
    (inside : entry ∈ (InletOmissionSource.run old instructions control count remaining state).attempts) :
    entry.row = row old instructions entry.state entry.command ∧
      entry.observation = observe old instructions entry.state entry.command ∧
      entry.row ∈ StageTrace.records state.cursor (InletOmissionSource.run old instructions control count remaining state).stages := by
  induction count generalizing remaining state with
  | zero => change entry ∈ [] at inside;contradiction
  | succ count ih =>
    by_cases empty : remaining = 0
    · subst remaining
      rw [stopped] at inside
      change entry ∈ [] at inside
      contradiction
    · rw [active old instructions state control count remaining empty] at inside ⊢
      change entry ∈ attempt old instructions state (control state) ::
        (InletOmissionSource.run old instructions control count
          (remaining - if observe old instructions state (control state) = some .executed then 1 else 0)
          (after old instructions state (control state))).attempts at inside
      rcases List.mem_cons.mp inside with same | later
      · subst entry
        refine ⟨rfl,rfl,?_⟩
        change row old instructions state (control state) ∈ StageTrace.records state.cursor (stages old instructions state (control state) ++ _)
        rw [OriginQueue.records_append]
        exact List.mem_append_left _ (the_attempt_row_is_in_its_actual_block old instructions state (control state))
      · obtain ⟨actual,observation,member⟩ := ih _ _ later
        refine ⟨actual,observation,?_⟩
        change entry.row ∈ StageTrace.records state.cursor (stages old instructions state (control state) ++ _)
        rw [OriginQueue.records_append,← one_block_is_the_original_execution]
        exact List.mem_append_right _ member

def countWithheld (entries : List (Attempt old instructions)) : Nat :=
  (entries.map fun entry => if entry.observation = some .withheld then 1 else 0).sum

theorem the_omission_count_is_its_actual_attempt_ledger (control : Controller old instructions)
    (count remaining : Nat) (state : State old instructions) :
    (InletOmissionSource.run old instructions control count remaining state).withheld =
      countWithheld old instructions (InletOmissionSource.run old instructions control count remaining state).attempts := by
  induction count generalizing remaining state with
  | zero => rfl
  | succ count ih =>
    by_cases empty : remaining = 0
    · subst remaining;rw [stopped];rfl
    · rw [active old instructions state control count remaining empty]
      change (if observe old instructions state (control state) = some .withheld then 1 else 0) +
        (InletOmissionSource.run old instructions control count _ _).withheld = _
      rw [ih]
      rfl

theorem every_attempt_is_consumed_in_the_final_native_inventory (control : Controller old instructions)
    (count remaining : Nat) (state : State old instructions) (entry : Attempt old instructions)
    (inside : entry ∈ (InletOmissionSource.run old instructions control count remaining state).attempts) :
    (Financial.inventoryAt (InletOmissionSource.run old instructions control count remaining state).state.cursor.source.input
      (ProgrammeHistory.visitAt (InletOmissionSource.run old instructions control count remaining state).state.cursor.source.input
        (EventStep.boundary entry.row.cursor))).filterMap
      (Financial.InstructionOrigin.instruction? (InletOmissionSource.run old instructions control count remaining state).state.cursor.source.input) =
        StageTrace.items entry.row :=
  every_generated_record_is_native_financial old instructions control count remaining state entry.row
    (every_attempt_keeps_its_queue_control_observation_and_actual_row old instructions control count remaining state entry inside).2.2

-- This consumer re-executes commands from the original state; saved contexts are not used as endpoints.
def replay (state : State old instructions) (entries : List (Attempt old instructions)) : State old instructions :=
  entries.foldl (fun current entry => after old instructions current entry.command) state

theorem the_actual_attempt_ledger_replays_to_the_complete_original_endpoint (control : Controller old instructions)
    (count remaining : Nat) (state : State old instructions) :
    replay old instructions state (InletOmissionSource.run old instructions control count remaining state).attempts =
      (InletOmissionSource.run old instructions control count remaining state).state := by
  induction count generalizing remaining state with
  | zero => rfl
  | succ count ih =>
    by_cases empty : remaining = 0
    · subst remaining;rw [stopped];rfl
    · rw [active old instructions state control count remaining empty]
      change replay old instructions (after old instructions state (control state))
        (InletOmissionSource.run old instructions control count _ _).attempts =
          (InletOmissionSource.run old instructions control count _ _).state
      exact ih _ _
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletOmissionProgress
