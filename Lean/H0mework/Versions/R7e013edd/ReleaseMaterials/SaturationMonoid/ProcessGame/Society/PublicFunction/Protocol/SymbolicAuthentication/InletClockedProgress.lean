import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletClockedSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletClockedProgress
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open InletClockedSource
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old : Code Party Good Port (Mandate.State Party Technology) Instrument)
  (instructions : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
local notation "Word" => RawEvent Party Good Port (Mandate.State Party Technology) Instrument
local notation "Request" => Institutions.Capitalism.Universal.Source.Program.Request Party Good Port (Mandate.State Party Technology) Instrument
local notation "Current" => RawCurrent Party Good (Mandate.State Party Technology) Instrument

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem strip_paid (current : Current) (request : Request) :
    strip (old.law.paidStep current request) = old.law.paidStep (strip current) request := by
  cases request.operation <;> rfl

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem strip_step (clockFree : ClockFree old instructions) (current : Current)
    (request : Request) (admitted : request ∈ instructions) :
    strip (old.law.step current request) = old.law.step (strip current) request := by
  simp only [RawLaw.step, clockFree current request admitted]
  split
  · exact strip_paid old current request
  · rfl

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

structure Block (state : State old instructions) (arrival : Word) (head : Request) (tail : Word) : Prop where
  pending : (after old instructions state arrival).pending = tail ++ arrival
  word : submitted old instructions state arrival = [head]
  current : strip (EventStep.seed (after old instructions state arrival).cursor).current = old.law.step (strip (EventStep.seed state.cursor).current) head
  aligned : (after old instructions state arrival).cursor.ownerStart ≤ (EventStep.seed (after old instructions state arrival).cursor).history.length
  fuel : (EventStep.seed (after old instructions state arrival).cursor).remaining = (EventStep.seed state.cursor).remaining - (delay old instructions state + 1)
  length : (stages old instructions state arrival).length ≤ 2

include old instructions in
private theorem block (clockFree : ClockFree old instructions) (state : State old instructions)
    (arrival : Word) (head : Request) (tail : Word)
    (pending : state.pending = head :: tail)
    (aligned : state.cursor.ownerStart ≤ (EventStep.seed state.cursor).history.length)
    (fuel : 2 ≤ (EventStep.seed state.cursor).remaining)
    (admitted : head ∈ instructions)
    (valid : old.law.Valid (strip (EventStep.seed state.cursor).current) head) :
    Block old instructions state arrival head tail := by
  have resource : old.law.Valid (EventStep.seed (prepared old instructions state)).current head := by
    apply (clockFree _ head admitted).mpr
    rwa [prepared_material old instructions state]
  have success := external_success old instructions state head aligned fuel admitted resource
  have actual := LiveProductionInletConsumer.executed_keeps_the_actual_input_and_next old instructions
    (prepared old instructions state) SilentWindow.quiet true head success
  have queue : (queued old instructions state arrival).pending ++ (command old instructions).incoming = head :: (tail ++ arrival) := by
    simp only [queued,List.append_nil,pending,List.cons_append]
  have stage : LiveProductionInletSource.stage old instructions (queued old instructions state arrival) (command old instructions) =
      (SilentWindow.quiet,LiveProductionInletSource.rival old instructions true head) := by
    unfold LiveProductionInletSource.stage
    rw [queue]
  have cursor : (after old instructions state arrival).cursor = LiveProductionInletSource.next old instructions
      (prepared old instructions state) SilentWindow.quiet true head := by
    change ((queued old instructions state arrival).cursor.after _ _) = _
    rw [stage]; rfl
  have next := StageTrace.material_is_the_actual_step (prepared old instructions state)
    SilentWindow.quiet (LiveProductionInletSource.rival old instructions true head)
  have history : (EventStep.seed (after old instructions state arrival).cursor).history =
      (EventStep.seed (prepared old instructions state)).history ++ [[head]] := by
    rw [cursor,EventStep.actual_next_state]
    change (EventStep.seed (prepared old instructions state)).history ++ [_] = _
    rw [← next.2,actual.2.1]
  have remaining : (EventStep.seed (after old instructions state arrival).cursor).remaining =
      (EventStep.seed (prepared old instructions state)).remaining - 1 := by
    rw [cursor,EventStep.actual_next_state]
    rfl
  have preservation := SilentWindow.preserves_the_actual_state state.cursor (delay old instructions state)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · change (LiveProductionInletSource.step old instructions (queued old instructions state arrival) (command old instructions)).pending = _
    unfold LiveProductionInletSource.step
    rw [queue]
    change (if LiveProductionInletSource.assess old instructions (prepared old instructions state) SilentWindow.quiet true head = .executed then tail ++ arrival else _) = _
    rw [if_pos success]
  · change (StageTrace.material _ _ _).submitted = _
    rw [stage]
    exact actual.2.1
  · rw [cursor,actual.2.2.1]
    change strip (old.law.step (EventStep.seed (prepared old instructions state)).current head) = _
    rw [strip_step old instructions clockFree _ head admitted,prepared_material old instructions state]
  · change (prepared old instructions state).ownerStart ≤ _
    rw [history,List.length_append,List.length_singleton,preservation.history,preservation.roster]
    omega
  · rw [remaining,preservation.fuel]
    exact Nat.sub_sub _ _ _
  · rw [stages,List.length_append,SilentWindow.stage_count,List.length_singleton]
    have := delay_bound old instructions state
    omega

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

structure Completes (state : State old instructions) (incoming : Incoming old instructions)
    (original tail : Word) : Prop where
  submitted : (InletClockedSource.run old instructions incoming original.length state).submitted = original
  pending : ∃ arrivals, (InletClockedSource.run old instructions incoming original.length state).state.pending = tail ++ arrivals
  current : strip (EventStep.seed (InletClockedSource.run old instructions incoming original.length state).state.cursor).current =
    (old.law.execute (strip (EventStep.seed state.cursor).current) 0 original).final
  length : (InletClockedSource.run old instructions incoming original.length state).stages.length ≤ 2 * original.length

-- The resource premise checks the original law on the starting material, not the generated schedule's outcomes.
theorem funded_original_prefix_completes (clockFree : ClockFree old instructions)
    (incoming : Incoming old instructions) (original tail : Word) (state : State old instructions)
    (pending : state.pending = original ++ tail)
    (aligned : state.cursor.ownerStart ≤ (EventStep.seed state.cursor).history.length)
    (fuel : 2 * original.length ≤ (EventStep.seed state.cursor).remaining)
    (admitted : ∀ request ∈ original,request ∈ instructions)
    (resources : ∀ item ∈ old.law.rawItems (strip (EventStep.seed state.cursor).current) original,
      old.law.Valid item.before item.request) : Completes old instructions state incoming original tail := by
  induction original generalizing state tail with
  | nil =>
    refine ⟨rfl,⟨[],?_⟩,rfl,by rfl⟩
    change state.pending = tail ++ []
    simpa only [List.nil_append,List.append_nil] using pending
  | cons head rest ih =>
    have headAdmitted := admitted head (List.mem_cons_self)
    have firstValid : old.law.Valid (strip (EventStep.seed state.cursor).current) head :=
      resources ⟨0,_,head⟩ (List.mem_cons_self)
    have first := block old instructions clockFree state (incoming state) head (rest ++ tail)
      (by simpa only [List.cons_append] using pending) aligned (by simp only [List.length_cons] at fuel; omega) headAdmitted firstValid
    have restResources : ∀ item ∈ old.law.rawItems
        (strip (EventStep.seed (after old instructions state (incoming state)).cursor).current) rest,
        old.law.Valid item.before item.request := by
      rw [first.current]
      apply (execution_index old (old.law.step (strip (EventStep.seed state.cursor).current) head) rest 1 0).2.mp
      intro item member
      exact resources item (List.mem_cons_of_mem _ member)
    have later := ih (tail ++ incoming state) (after old instructions state (incoming state))
      (by rw [first.pending,List.append_assoc]) first.aligned
      (by rw [first.fuel]; have := delay_bound old instructions state; simp only [List.length_cons] at fuel; omega)
      (fun request member => admitted request (List.mem_cons_of_mem _ member)) restResources
    refine ⟨?_,?_,?_,?_⟩
    · change submitted old instructions state (incoming state) ++
        (InletClockedSource.run old instructions incoming rest.length (after old instructions state (incoming state))).submitted = _
      rw [first.word,later.submitted]
      rfl
    · obtain ⟨arrivals,same⟩ := later.pending
      refine ⟨incoming state ++ arrivals,?_⟩
      change (InletClockedSource.run old instructions incoming rest.length (after old instructions state (incoming state))).state.pending = _
      rw [same,List.append_assoc]
    · change strip (EventStep.seed (InletClockedSource.run old instructions incoming rest.length
        (after old instructions state (incoming state))).state.cursor).current = _
      rw [later.current,first.current]
      exact (execution_index old _ rest 0 1).1
    · change (stages old instructions state (incoming state) ++
        (InletClockedSource.run old instructions incoming rest.length (after old instructions state (incoming state))).stages).length ≤ _
      rw [List.length_append,List.length_cons]
      have := first.length
      have := later.length
      omega

theorem checked_queue_completes (clockFree : ClockFree old instructions)
    (incoming : Incoming old instructions) (state : State old instructions) (funded : ready old instructions state = true) :
    Completes old instructions state incoming state.pending [] := by
  have checks := of_decide_eq_true funded
  exact funded_original_prefix_completes old instructions clockFree incoming state.pending [] state
    (List.append_nil _).symm checks.1 checks.2.1 checks.2.2.1 checks.2.2.2

theorem every_generated_record_is_native_financial (incoming : Incoming old instructions)
    (count : Nat) (state : State old instructions) (record : StageTrace.Record (code := Active old instructions))
    (inside : record ∈ StageTrace.records state.cursor (InletClockedSource.run old instructions incoming count state).stages) :
    (Financial.inventoryAt (InletClockedSource.run old instructions incoming count state).state.cursor.source.input
      (ProgrammeHistory.visitAt (InletClockedSource.run old instructions incoming count state).state.cursor.source.input
        (EventStep.boundary record.cursor))).filterMap
      (Financial.InstructionOrigin.instruction? (InletClockedSource.run old instructions incoming count state).state.cursor.source.input) =
        StageTrace.items record := by
  rw [every_run_is_the_original_execution]
  exact StageTrace.final_financial_inventory_is_the_original_record_items _ _ _ inside
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InletClockedProgress
