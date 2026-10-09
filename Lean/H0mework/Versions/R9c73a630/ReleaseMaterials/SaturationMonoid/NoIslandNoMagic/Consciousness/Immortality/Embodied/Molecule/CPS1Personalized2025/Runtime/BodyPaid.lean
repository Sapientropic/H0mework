import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeBodyPaidSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeRootData
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Runtime.RegisteredBody

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

namespace CPS1MaterialIncidence.NativeBodyFunctionProbe
noncomputable section
open CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange NativeAmmoniaDynamics
open NativeResumableProbe NativeBodyProbe NativePrepareNextProbe NativePrepareBinding
open NativePaidEvent NativeCPContinuationProbe NativeAdoptionProbe NativeRootDataProbe

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}

/-- This is the state restriction of actual refinement, not a new source. -/
def refineSteps (state : PostState current) : Nat → PostState current
  | 0 => state
  | n+1 => refineState (refineSteps state n)

theorem refine_steps_exact (state : PostState current) (n : Nat) :
    refineSteps state n = {state with index := state.index+n} := by
  induction n with
  | zero => rfl
  | succ n previous =>
      simp only [refineSteps,previous,refineState,Nat.add_assoc]

theorem refine_steps_fields (state : PostState current) (n : Nat) :
    (refineSteps state n).index = state.index+n ∧
    (refineSteps state n).pose = state.pose ∧
    (refineSteps state n).rawC = state.rawC ∧
    (refineSteps state n).occupied = state.occupied ∧
    (refineSteps state n).reserve = state.reserve ∧
    (refineSteps state n).elapsed = state.elapsed ∧
    (refineSteps state n).energy = state.energy := by
  rw [refine_steps_exact]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem refine_steps_time (state : PostState current) (n : Nat) :
    (refineSteps state n).time = state.time/(2:ℝ)^n := by
  induction n with
  | zero => simp only [refineSteps,pow_zero,div_one]
  | succ n previous =>
      rw [refineSteps,refinement_time,previous,pow_succ,div_div]

private def PaidGuard (state : PostState current) : Prop :=
  Body.ready (endPose state) ∧ energyPrice state ≤ state.reserve

private theorem advance_refines_if_unpaid (state : PostState current) (unpaid : ¬ PaidGuard state) :
    (advanceNative state).next = refineState state := by
  classical
  have smooth := post_full_smooth state
  by_cases ready : Body.ready (endPose state)
  · have shortage : ¬ energyPrice state ≤ state.reserve := fun budget => unpaid ⟨ready,budget⟩
    rw [advance_native_energy_shortage state smooth ready shortage]
    rfl
  · rw [advance_native_collision state smooth ready]
    rfl

section Body
variable {oldBody : CPS1BiologicalUpdate.Body} {receipt : CPS1BiologicalUpdate.LocalRepairReceipt oldBody}
  {priorRaw : Classical.Raw} {before : Classical.Current receipt.nextBody.current.2 priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current} {continuation : CPNativeContinuation paid}
  {returned : NativePrepareNext paid continuation} {germ : NativeOriginGerm returned.occurrence}

/-- Each element executes the existing writer on the preceding stored body. -/
def bodySteps (body : NativeBody receipt returned germ) : Nat → NativeBody receipt returned germ
  | 0 => body
  | n+1 => body_next receipt (bodySteps body n)

theorem body_steps_zero (body : NativeBody receipt returned germ) : bodySteps body 0 = body := rfl

theorem body_steps_next (body : NativeBody receipt returned germ) (n : Nat) :
    bodySteps body (n+1) = body_next receipt (bodySteps body n) := rfl

theorem body_steps_iterate (body : NativeBody receipt returned germ) (n : Nat) :
    bodySteps body n = ((body_next receipt)^[n]) body := by
  induction n with
  | zero => rfl
  | succ n previous => simp only [bodySteps,previous,Function.iterate_succ_apply']

theorem body_steps_actual (body : NativeBody receipt returned germ) (n : Nat) :
    (bodySteps body (n+1)).current = advanceSource (bodySteps body n).current ∧
    (bodySteps body (n+1)).current.stock = (runPulse (bodySteps body n).current).stock ∧
    (bodySteps body (n+1)).history = (bodySteps body n).history ++
      [.written (bodySteps body n).current (body_event_at receipt (bodySteps body n))] ∧
    BodyUpdate receipt returned germ (bodySteps body n) (body_event_at receipt (bodySteps body n)) (bodySteps body (n+1)) ∧
    BodyInvariant receipt returned germ (bodySteps body (n+1)) :=
  ⟨body_next_kernel receipt _,body_next_stock receipt _,body_next_history receipt _,
    body_next_law receipt _,body_next_invariant receipt _⟩

private theorem body_steps_refine_prefix (body : NativeBody receipt returned germ) (n : Nat)
    (unpaid : ∀ k < n, ¬ PaidGuard (refineSteps body.current.state k)) :
    (bodySteps body n).current.state = refineSteps body.current.state n := by
  induction n with
  | zero => rfl
  | succ n previous =>
      have same := previous (fun k less => unpaid k (Nat.lt_succ_of_lt less))
      rw [body_steps_next,body_next_state,same,advance_refines_if_unpaid _ (unpaid n (Nat.lt_succ_self n))]
      rfl

private def firstPaidIndex (body : NativeBody receipt returned germ)
    (eventual : ∃ n, PaidGuard (refineSteps body.current.state n)) : Nat := by
  classical
  exact Nat.find eventual

private theorem first_paid_guard (body : NativeBody receipt returned germ)
    (eventual : ∃ n, PaidGuard (refineSteps body.current.state n)) :
    PaidGuard (bodySteps body (firstPaidIndex body eventual)).current.state := by
  classical
  have previous : ∀ k < firstPaidIndex body eventual, ¬ PaidGuard (refineSteps body.current.state k) := by
    intro k less
    exact Nat.find_min eventual less
  rw [body_steps_refine_prefix body _ previous]
  exact Nat.find_spec eventual

/-- Conditional construction is private until the source owns the reserve.
Its ordinal selects actual checker success; no after-state is selected. -/
private def paidBodyEvent (body : NativeBody receipt returned germ)
    (eventual : ∃ n, PaidGuard (refineSteps body.current.state n)) :
    PaidStep (bodySteps body (firstPaidIndex body eventual)).current.state :=
  ⟨post_full_smooth _,(first_paid_guard body eventual).1,(first_paid_guard body eventual).2⟩

private theorem actual_paid_body_event (body : NativeBody receipt returned germ)
    (eventual : ∃ n, PaidGuard (refineSteps body.current.state n)) :
    (body_event_at receipt (bodySteps body (firstPaidIndex body eventual))).result = .paid (paidBodyEvent body eventual) :=
  advance_native_paid _ (post_full_smooth _) (first_paid_guard body eventual).1 (first_paid_guard body eventual).2

private theorem paid_body_clock (body : NativeBody receipt returned germ)
    (eventual : ∃ n, PaidGuard (refineSteps body.current.state n)) :
    (bodySteps body (firstPaidIndex body eventual)).current.state.elapsed <
      (bodySteps body (firstPaidIndex body eventual+1)).current.state.elapsed := by
  rw [body_steps_next,body_next_state]
  change (bodySteps body (firstPaidIndex body eventual)).current.state.elapsed <
    (body_event_at receipt (bodySteps body (firstPaidIndex body eventual))).result.next.elapsed
  rw [actual_paid_body_event]
  exact paid_clock (paidBodyEvent body eventual)

private theorem source_disposition_before (body : NativeBody receipt returned germ)
    (generated : PaidSourceDisposition body.current.state) :
    (bodySteps body generated.index).current.state = refinedAt body.current.state generated.index := by
  have earlier : ∀ k < generated.index, ¬ PaidGuard (refineSteps body.current.state k) := by
    intro k less
    simpa only [PaidGuard,RefinementPaidGuard,refinedAt,refine_steps_exact] using generated.unpaid_prefix k less
  exact (body_steps_refine_prefix body generated.index earlier).trans (refine_steps_exact _ _)

private theorem advance_states_heq (left right : PostState current) (same : left = right) :
    HEq (advanceNative left) (advanceNative right) := by
  cases same
  rfl

private theorem result_next_eq {left right : PostState current} (same : left = right)
    (leftResult : NativePhysicalResult left) (rightResult : NativePhysicalResult right)
    (actual : HEq leftResult rightResult) : leftResult.next = rightResult.next := by
  cases same
  rw [eq_of_heq actual]

structure NativeBodyPaidRun (body : NativeBody receipt returned germ) where
  generated : PaidSourceDisposition body.current.state
  generatedActual : generated = source_generated_paid_disposition body.current.state
  before : NativeBody receipt returned germ
  beforeActual : before = bodySteps body generated.index
  beforeState : before.current.state = refinedAt body.current.state generated.index
  event : NativeWrite returned germ before.current
  eventActual : event = body_event_at receipt before
  next : NativeBody receipt returned germ
  nextActual : next = body_next receipt before
  resultActual : HEq event.result generated.result
  nextState : next.current.state = generated.next
  law : BodyUpdate receipt returned germ before event next
  invariant : BodyInvariant receipt returned germ next

def source_generated_native_body_paid_run (body : NativeBody receipt returned germ) : NativeBodyPaidRun body := by
  let generated := source_generated_paid_disposition body.current.state
  let before := bodySteps body generated.index
  have beforeState : before.current.state = refinedAt body.current.state generated.index :=
    source_disposition_before body generated
  let event := body_event_at receipt before
  have resultActual : HEq event.result generated.result :=
    (heq_of_eq event.resultActual).trans
      ((advance_states_heq _ _ beforeState).trans (heq_of_eq generated.actual))
  refine ⟨generated,rfl,before,rfl,beforeState,event,rfl,body_next receipt before,rfl,resultActual,?_,
    body_next_law receipt before,body_next_invariant receipt before⟩
  exact (body_next_state receipt before).trans
    (result_next_eq beforeState (advanceNative before.current.state) generated.result
      ((advance_states_heq _ _ beforeState).trans (heq_of_eq generated.actual)))

namespace NativeBodyPaidRun
variable {body : NativeBody receipt returned germ} (run : NativeBodyPaidRun body)

theorem actual_stock : run.next.current.stock = run.event.execution.stock := run.law.stock

theorem actual_history : run.next.history = run.before.history ++ [.written run.before.current run.event] := run.law.history

theorem whole : type_of% run.next.whole := run.next.whole

theorem fields : type_of% run.next.fields := run.next.fields

theorem electrons : type_of% run.next.electrons := run.next.electrons

theorem account : run.next.current.state.energy + run.next.current.state.reserve =
    body.current.state.energy + body.current.state.reserve :=
  (congrArg (fun state : PostState current => state.energy+state.reserve) run.nextState).trans run.generated.complete_next.1

theorem actual_after : run.next = bodySteps body (run.generated.index+1) := by
  rw [run.nextActual,run.beforeActual]
  rfl

end NativeBodyPaidRun

end Body
end
end CPS1MaterialIncidence.NativeBodyFunctionProbe

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
noncomputable section
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open CPS1MaterialIncidence.NativeRootDataProbe CPS1SameEventFunction
open Source.NativeRegistration
attribute [local irreducible] generated_input source_programme InputBodyAt input_body_next DispositionBodyAt disposition_body_next
attribute [local implicit_reducible] ProgrammeAt ClassicalRepairResponse GeneratedBodyAt

/-- The compiler's existing body calculation, with each written body fed back. -/
def inputSteps (input : RegisteredNativeInput) (body : InputBodyAt input) : Nat → InputBodyAt input
  | 0 => body
  | n+1 => input_body_next input (inputSteps input body n)

/-- Every state is obtained through the same installed root's sealed tick. -/
def runtimeSteps (runtime : LivingRuntimeState Delivery.process) : Nat → LivingRuntimeState Delivery.process
  | 0 => runtime
  | n+1 => (runtimeSteps runtime n).tick.next

private theorem input_next_heq {leftInput rightInput : RegisteredNativeInput}
    (sameInput : leftInput = rightInput) (left : InputBodyAt leftInput) (right : InputBodyAt rightInput)
    (sameBody : HEq left right) :
    HEq (input_body_next leftInput left) (input_body_next rightInput right) := by
  cases sameInput
  have same := eq_of_heq sameBody
  cases same
  rfl

theorem runtime_steps_input (runtime : LivingRuntimeState Delivery.process) (n : Nat) :
    (runtimeSteps runtime n).current.visit.current.input = runtime.current.visit.current.input := by
  induction n with
  | zero => rfl
  | succ n previous =>
      exact (congrArg Root.Native.Current.input (Delivery.full_native_current_next (runtimeSteps runtime n))).trans
        ((Root.Native.next_input (runtimeSteps runtime n).current.visit.current).trans previous)

theorem runtime_steps_body (runtime : LivingRuntimeState Delivery.process) (n : Nat) :
    HEq (runtimeSteps runtime n).current.visit.current.body
      (inputSteps runtime.current.visit.current.input runtime.current.visit.current.body n) := by
  induction n with
  | zero => rfl
  | succ n previous =>
      let reached := runtimeSteps runtime n
      have actual : reached.tick.next.current.visit.current.body =
          input_body_next reached.current.visit.current.input reached.current.visit.current.body :=
        (Delivery.native_material_source_actual reached.tick.next).symm.trans
          ((Delivery.literal_native_body_next reached).trans
            (congrArg (input_body_next reached.current.visit.current.input) (Delivery.native_material_source_actual reached)))
      exact (heq_of_eq actual).trans
        (input_next_heq (runtime_steps_input runtime n) reached.current.visit.current.body
          (inputSteps runtime.current.visit.current.input runtime.current.visit.current.body n) previous)

private theorem input_next_disposition_heq (input : RegisteredNativeInput) (occurrence : InputOccurrence input)
    (actual : generated_input input = some occurrence) (body : InputBodyAt input)
    (represented : DispositionBodyAt occurrence.whole input.supply occurrence.repair occurrence.response
      occurrence.outcome occurrence.repairActual) (sameBody : HEq body represented) :
    HEq (input_body_next input body)
      (disposition_body_next occurrence.whole input.supply occurrence.repair occurrence.response
        occurrence.outcome occurrence.repairActual represented) := by
  have law := input_write_law input body
  unfold InputWriteLaw at law
  rw [actual] at law
  obtain ⟨selected,selectedActual,nextActual,_law⟩ := law
  have same : selected = represented := eq_of_heq (selectedActual.symm.trans sameBody)
  rw [same] at nextActual
  exact nextActual

private def dispositionSteps (input : RegisteredNativeInput) (occurrence : InputOccurrence input)
    (body : DispositionBodyAt occurrence.whole input.supply occurrence.repair occurrence.response
      occurrence.outcome occurrence.repairActual) : Nat →
    DispositionBodyAt occurrence.whole input.supply occurrence.repair occurrence.response
      occurrence.outcome occurrence.repairActual
  | 0 => body
  | n+1 => disposition_body_next occurrence.whole input.supply occurrence.repair occurrence.response
      occurrence.outcome occurrence.repairActual (dispositionSteps input occurrence body n)

private theorem input_steps_disposition_heq (input : RegisteredNativeInput) (occurrence : InputOccurrence input)
    (actual : generated_input input = some occurrence) (body : InputBodyAt input)
    (represented : DispositionBodyAt occurrence.whole input.supply occurrence.repair occurrence.response
      occurrence.outcome occurrence.repairActual) (sameBody : HEq body represented) (n : Nat) :
    HEq (inputSteps input body n) (dispositionSteps input occurrence represented n) := by
  induction n with
  | zero => exact sameBody
  | succ n previous =>
      exact input_next_disposition_heq input occurrence actual _ _ previous

private theorem iterates_heq {α β : Type} (leftNext : α → α) (rightNext : β → β)
    (step : ∀ left right, HEq left right → HEq (leftNext left) (rightNext right))
    (left : α) (right : β) (same : HEq left right) (n : Nat) :
    HEq ((leftNext^[n]) left) ((rightNext^[n]) right) := by
  induction n with
  | zero => exact same
  | succ n previous =>
      simpa only [Function.iterate_succ_apply'] using step _ _ previous

section Positive
open CPS1ResourceExecution CPS1BiologicalUpdate CPS1PhosphorylExchange CPS1LiveEditing CPS1MaterialIncidence.NativeBodyProbe
variable {frame : CPS1Recycling.Frame} {origin : CPS1ReactiveNuclear.SourceCursor frame}
  {water : Nat} {material : List RawSupply} {path : CPS1Recycling.SplitSite}
  {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
  {physical : PhysicalRaw} {depth : Nat}
  (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
  (profile : NativeProfile supply) (receipt : LocalRepairReceipt (initialBody ⟨frame,origin⟩))
  {responseRaw : WholeRaw} {exchange : CPS1PhosphorylExchange.Raw}
  (response : WholeResponse (.repaired receipt) responseRaw)
  (before : Classical.Current receipt.nextBody.current.2 responseRaw.particles)
  (step : Classical.NativeStep before responseRaw.particles.time)
  (selected : response.particles = Classical.Disposition.responded before step)
  (source : Common before step exchange) (current : NativeCurrent source)
  (repairActual : LocalRepairDisposition.repaired receipt = repairWhole whole supply)

private theorem positive_next_heq
    (body : DispositionBodyAt whole supply (.repaired receipt) response
      (.responded response before step selected source current) repairActual)
    (native : GeneratedBodyAt whole supply profile receipt repairActual.symm source
      (source_paid_data whole supply profile receipt repairActual.symm source current)
      (source_continuation_data (source_paid_data whole supply profile receipt repairActual.symm source current)))
    (same : HEq body native) :
    HEq (disposition_body_next whole supply (.repaired receipt) response
      (.responded response before step selected source current) repairActual body) (body_next receipt native) := by
  classical
  have law := disposition_write_law whole supply (.repaired receipt) response
    (.responded response before step selected source current) repairActual body
  simp only [DispositionWriteLaw,dif_pos profile] at law
  obtain ⟨represented,beforeActual,afterActual,_kernel,_stock,_history,_update,_invariant,_genome,
    _fullLength,_whole,_fields,_electrons,_account,_legacy,_duties,_strict⟩ := law
  have identical : represented = native := eq_of_heq (beforeActual.symm.trans same)
  rw [identical] at afterActual
  exact afterActual

end Positive

private theorem disposition_steps_iterate (input : RegisteredNativeInput) (occurrence : InputOccurrence input)
    (body : DispositionBodyAt occurrence.whole input.supply occurrence.repair occurrence.response
      occurrence.outcome occurrence.repairActual) (n : Nat) :
    dispositionSteps input occurrence body n =
      ((disposition_body_next occurrence.whole input.supply occurrence.repair occurrence.response
        occurrence.outcome occurrence.repairActual)^[n]) body := by
  induction n with
  | zero => rfl
  | succ n previous => simp only [dispositionSteps,previous,Function.iterate_succ_apply']

private theorem runtime_steps_disposition (runtime : LivingRuntimeState Delivery.process)
    (transition : NativeBodyRootTransitionAt runtime.current.visit.current (Delivery.readNativeWrite runtime)) :
    ∃ occurrence : InputOccurrence runtime.current.visit.current.input,
      generated_input runtime.current.visit.current.input = some occurrence ∧
      ∃ represented : DispositionBodyAt occurrence.whole runtime.current.visit.current.input.supply occurrence.repair
          occurrence.response occurrence.outcome occurrence.repairActual,
        HEq runtime.current.visit.current.body represented ∧
        ∀ n, HEq (runtimeSteps runtime n).current.visit.current.body
          (dispositionSteps runtime.current.visit.current.input occurrence represented n) := by
  obtain ⟨_registered,occurrence,actual,_native,_profile,represented,beforeActual,_after,_law,_strict⟩ := transition
  refine ⟨occurrence,actual,represented,beforeActual,?_⟩
  intro n
  exact (runtime_steps_body runtime n).trans
    (input_steps_disposition_heq runtime.current.visit.current.input occurrence actual
      runtime.current.visit.current.body represented beforeActual n)


open CPS1MaterialIncidence.NativeBodyFunctionProbe CPS1MaterialIncidence.NativeBodyProbe

private theorem written_body_at_run {oldBody : CPS1BiologicalUpdate.Body}
    {receipt : CPS1BiologicalUpdate.LocalRepairReceipt oldBody}
    {priorRaw : CPS1SameEventFunction.Classical.Raw}
    {before : CPS1SameEventFunction.Classical.Current receipt.nextBody.current.2 priorRaw}
    {step : CPS1SameEventFunction.Classical.NativeStep before priorRaw.time}
    {raw : CPS1PhosphorylExchange.Raw} {source : CPS1PhosphorylExchange.Common before step raw}
    {current : CPS1PhosphorylExchange.NativeCurrent source}
    {paid : CPS1MaterialIncidence.NativePaidEvent.SourceGeneratedPaidReturn source current}
    {continuation : CPS1MaterialIncidence.NativeCPContinuationProbe.CPNativeContinuation paid}
    {returned : CPS1MaterialIncidence.NativePrepareNextProbe.NativePrepareNext paid continuation}
    {germ : CPS1MaterialIncidence.NativePrepareBinding.NativeOriginGerm returned.occurrence}
    (runtime : LivingRuntimeState Delivery.process) (body : NativeBody receipt returned germ)
    (bodyActual : ∀ n, HEq (runtimeSteps runtime n).current.visit.current.body (bodySteps body n))
    (run : NativeBodyPaidRun body) :
    HEq (Delivery.readWrittenNativeBody (runtimeSteps runtime run.generated.index)) run.next ∧
    HEq (Delivery.readNativeBody (runtimeSteps runtime (run.generated.index+1))) run.next := by
  let reached := runtimeSteps runtime run.generated.index
  have nextBody : HEq (Delivery.readNativeBody (runtimeSteps runtime (run.generated.index+1))) run.next :=
    (heq_of_eq (Delivery.native_material_source_actual (runtimeSteps runtime (run.generated.index+1)))).trans
      ((bodyActual _).trans (heq_of_eq run.actual_after.symm))
  have literal : Delivery.readNativeBody reached.tick.next = Delivery.readWrittenNativeBody reached :=
    (Delivery.literal_native_body_next reached).trans (Delivery.native_written_body_actual reached).symm
  exact ⟨(heq_of_eq literal.symm).trans nextBody,nextBody⟩

section PaidDisposition
open CPS1ResourceExecution CPS1BiologicalUpdate CPS1PhosphorylExchange CPS1LiveEditing
variable {frame : CPS1Recycling.Frame} {origin : CPS1ReactiveNuclear.SourceCursor frame}
  {water : Nat} {material : List RawSupply} {path : CPS1Recycling.SplitSite}
  {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
  {physical : PhysicalRaw} {depth : Nat}
  (whole : WholeRun origin water material path events feed physical depth) (supply : ContinuationRaw)
  {responseRaw : WholeRaw} {exchange : CPS1PhosphorylExchange.Raw}
  (repair : LocalRepairDisposition (initialBody ⟨frame,origin⟩))
  (response : WholeResponse repair responseRaw)
  (outcome : CPS1PhosphorylExchange.Disposition responseRaw exchange repair response)
  (repairActual : repair = repairWhole whole supply)

private def PaidAtDisposition (runtime : LivingRuntimeState Delivery.process) : Prop := by
  classical
  cases outcome with
  | retained response failure => exact False
  | @responded receipt response before step selected source current =>
      exact if profile : NativeProfile supply then
        let paid := source_paid_data whole supply profile receipt repairActual.symm source current
        let continuation := source_continuation_data paid
        ∃ body : GeneratedBodyAt whole supply profile receipt repairActual.symm source paid continuation,
          ∃ run : NativeBodyPaidRun body,
            run = source_generated_native_body_paid_run body ∧
            HEq runtime.current.visit.current.body body ∧
            (∀ n, HEq (runtimeSteps runtime n).current.visit.current.body (bodySteps body n)) ∧
            HEq (Delivery.readWrittenNativeBody (runtimeSteps runtime run.generated.index)) run.next ∧
            HEq (Delivery.readNativeBody (runtimeSteps runtime (run.generated.index+1))) run.next ∧
            (type_of% (Delivery.native_material_factorizes (runtimeSteps runtime run.generated.index)))
      else False

private theorem paid_at_actual_runtime (runtime : LivingRuntimeState Delivery.process)
    (body : DispositionBodyAt whole supply repair response outcome repairActual)
    (native : Source.NativeRegistration.IsNativeOutcome outcome) (profile : NativeProfile supply)
    (law : DispositionWriteLaw whole supply repair response outcome repairActual body)
    (bodyActual : HEq runtime.current.visit.current.body body)
    (stepsActual : ∀ n, HEq (runtimeSteps runtime n).current.visit.current.body
      (((disposition_body_next whole supply repair response outcome repairActual)^[n]) body)) :
    PaidAtDisposition whole supply repair response outcome repairActual runtime := by
  classical
  cases outcome with
  | retained response failure => exact False.elim native
  | @responded receipt response before step selected source current =>
      simp only [PaidAtDisposition,dif_pos profile]
      simp only [DispositionWriteLaw,dif_pos profile] at law
      obtain ⟨represented,beforeActual,_nextActual,_kernel,_stock,_history,_update,_invariant,_genome,
        _fullLength,_whole,_fields,_electrons,_account,_legacy,_duties,_strict⟩ := law
      have everyBody : ∀ n, HEq (runtimeSteps runtime n).current.visit.current.body (bodySteps represented n) := by
        intro n
        rw [body_steps_iterate]
        exact (stepsActual n).trans
          (iterates_heq _ _ (positive_next_heq whole supply profile receipt response before step selected source current repairActual)
            body represented beforeActual n)
      let run := source_generated_native_body_paid_run represented
      have written := written_body_at_run runtime represented everyBody run
      exact ⟨represented,run,rfl,bodyActual.trans beforeActual,everyBody,written.1,written.2,
        Delivery.native_material_factorizes (runtimeSteps runtime run.generated.index)⟩

end PaidDisposition

/-- The chosen source ordinal is an actual finite history of this installed
root. Its body event is paid, or carries the exact zero-reserve shortage. -/
def NativeBodyPaidRootAt (runtime : LivingRuntimeState Delivery.process) : Prop :=
  NativeBodyRootTransitionAt runtime.current.visit.current (Delivery.readNativeWrite runtime) ∧
  ∃ occurrence : InputOccurrence runtime.current.visit.current.input,
    generated_input runtime.current.visit.current.input = some occurrence ∧
    PaidAtDisposition occurrence.whole runtime.current.visit.current.input.supply occurrence.repair
      occurrence.response occurrence.outcome occurrence.repairActual runtime

private theorem native_body_paid_root_actual (runtime : LivingRuntimeState Delivery.process)
    (transition : NativeBodyRootTransitionAt runtime.current.visit.current (Delivery.readNativeWrite runtime)) :
    NativeBodyPaidRootAt runtime := by
  refine ⟨transition,?_⟩
  obtain ⟨_registered,occurrence,actual,native,profile,represented,beforeActual,_after,law,_strict⟩ := transition
  refine ⟨occurrence,actual,paid_at_actual_runtime occurrence.whole runtime.current.visit.current.input.supply
    occurrence.repair occurrence.response occurrence.outcome occurrence.repairActual runtime represented native profile law beforeActual ?_⟩
  intro n
  exact (runtime_steps_body runtime n).trans
    ((input_steps_disposition_heq runtime.current.visit.current.input occurrence actual
      runtime.current.visit.current.body represented beforeActual n).trans
      (heq_of_eq (disposition_steps_iterate runtime.current.visit.current.input occurrence represented n)))

theorem source_generated_native_body_paid_at_root (n : Nat) : NativeBodyPaidRootAt (registered_body_runtime n) :=
  native_body_paid_root_actual (registered_body_runtime n) (source_generated_native_body_root_next n).1

theorem source_generated_native_body_paid_after_parent : NativeBodyPaidRootAt Delivery.afterParent :=
  native_body_paid_root_actual Delivery.afterParent source_generated_native_body_after_parent.1

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
