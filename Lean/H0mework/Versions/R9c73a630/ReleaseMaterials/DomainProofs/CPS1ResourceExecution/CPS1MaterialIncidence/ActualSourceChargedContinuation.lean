import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualSerialChargeBoundary

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence
noncomputable section
open CPS1PhosphorylExchange CPS1ElectronicSource CPS1AtomicDynamics
open scoped BigOperators InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : CPS1SameEventFunction.Classical.Raw}
  {before : CPS1SameEventFunction.Classical.Current cursor priorRaw}
  {step : CPS1SameEventFunction.Classical.NativeStep before priorRaw.time}
  {raw : Raw} {source : Common before step raw}

def sourceAtomChargedWord (current : NativeCurrent source) : ChargedSourceWord cursor :=
  (sourceAtomCARWord current).filterMap AtomCARMonomial.instruction?

theorem source_atom_charged_word_vertices (current : NativeCurrent source)
    (instruction : ChargedInstruction cursor) (held : instruction ∈ sourceAtomChargedWord current) :
    ∃ donor receiver, instruction = .electron donor receiver ∧
      donor ∈ vertices source ∧ receiver ∈ vertices source := by
  classical
  obtain ⟨term, held, actual⟩ := List.mem_filterMap.mp held
  obtain ⟨_, actualInstruction, _⟩ := source_atom_instruction_actual current term instruction actual
  have vertices := source_atom_instruction_vertices current term
  exact ⟨sectorOrigin current term.removing, sectorOrigin current term.creating,
    actualInstruction, vertices.1, vertices.2⟩

private theorem charged_step_instruction
    (source : Common before step raw) (current : NativeCurrent source)
    (state : ChargedState source current) (instruction : ChargedInstruction cursor)
    (event : SourceChargedStep source current)
    (actual : stepCharged? source current state instruction = .ok event) :
    event.instruction = instruction := by
  unfold stepCharged? at actual
  split at actual
  · cases actual
  · repeat' split at actual
    all_goals cases actual
    all_goals rfl

private def runChargedContinuationFrom (source : Common before step raw)
    (current : NativeCurrent source) (word : ChargedSourceWord cursor)
    (state : ChargedState source current) : SourceChargedRun source current :=
  match word with
  | [] => ⟨[],[],state,none⟩
  | instruction :: rest => match stepCharged? source current state instruction with
    | .error residual => ⟨[],instruction :: rest,state,some residual⟩
    | .ok event =>
      let next := runChargedContinuationFrom source current rest event.after
      ⟨event :: next.fired,next.remaining,next.state,next.residual⟩

private theorem run_charged_continuation_spent
    (current : NativeCurrent source) (word : ChargedSourceWord cursor)
    (state : ChargedState source current)
    (held : ∀ instruction ∈ word, instruction ∈ sourceAtomChargedWord current) :
    (runChargedContinuationFrom source current word state).state.spent = state.spent := by
  induction word generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
    have instructionHeld : instruction ∈ sourceAtomChargedWord current :=
      held instruction (by simp)
    have restHeld : ∀ next ∈ rest, next ∈ sourceAtomChargedWord current := by
      intro next nextHeld
      exact held next (by simp [nextHeld])
    cases actual : stepCharged? source current state instruction with
    | error residual =>
      simp only [runChargedContinuationFrom, actual]
    | ok event =>
      have instructionShape := source_atom_charged_word_vertices current instruction instructionHeld
      obtain ⟨donor,receiver,instructionEq,_,_⟩ := instructionShape
      subst instruction
      have eventInstruction := charged_step_instruction source current state
        (.electron donor receiver) event actual
      have tokenEq : event.token = ⟨donor,receiver,none⟩ := by
        apply Option.some.inj
        exact event.prepared.symm.trans (by rw [eventInstruction]; rfl)
      have beforeEq := charged_step_before source current state (.electron donor receiver) event actual
      have nextSpent := ih event.after restHeld
      calc
        (runChargedContinuationFrom source current (.electron donor receiver :: rest) state).state.spent =
            (runChargedContinuationFrom source current rest event.after).state.spent := by
              simp only [runChargedContinuationFrom,actual]
        _ = event.after.spent := nextSpent
        _ = state.spent := by
          rw [SourceChargedStep.after,charged_record_spent,beforeEq,tokenEq]
          simp [ChargedToken.debits]

def nativeIncidenceSourceChargedContinuation (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current) :
    SourceChargedRun source current :=
  runChargedContinuationFrom source current (sourceAtomChargedWord current) trace.after

theorem native_incidence_source_charged_continuation_whole
    (current : NativeCurrent source) (trace : NativeIncidenceTrace source current)
    (_actual : nativeIncidence? source current = .ok trace) :
    (nativeIncidenceSourceChargedContinuation current trace).state.whole.1 = current ∧
      (nativeIncidenceSourceChargedContinuation current trace).state.whole.1.nodes = current.nodes ∧
      (nativeIncidenceSourceChargedContinuation current trace).state.whole.1.occupied = current.occupied ∧
      (nativeIncidenceSourceChargedContinuation current trace).state.whole.1.remaining = current.remaining :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem native_incidence_source_charged_continuation_spent
    (current : NativeCurrent source) (trace : NativeIncidenceTrace source current)
    (_actual : nativeIncidence? source current = .ok trace) :
    (nativeIncidenceSourceChargedContinuation current trace).state.spent = trace.after.spent := by
  unfold nativeIncidenceSourceChargedContinuation
  apply run_charged_continuation_spent current
  intro instruction held
  exact held

structure SourceChargedMaterialContinuation
    (source : Common before step raw) (current : NativeCurrent source)
    (trace : NativeIncidenceTrace source current) where
  actual : nativeIncidence? source current = .ok trace
  charged : SourceChargedRun source current
  material : SourceMaterialStep source current
  charged_source : charged = nativeIncidenceSourceChargedContinuation current trace
  material_token : material.token = trace.selection.bond
  material_actual :
    stepSource? source current (materialInitial source current) = .ok material
  material_incidence : material.after.graph.incidence = trace.after.graph.incidence
  material_reused :
    stepSource? source current material.after = .error (.reusedBond material.token.debit)
  charged_spent : charged.state.spent = trace.after.spent

def nativeIncidenceSourceChargedMaterialContinuation
    (current : NativeCurrent source) (trace : NativeIncidenceTrace source current)
    (actual : nativeIncidence? source current = .ok trace) :
    SourceChargedMaterialContinuation source current trace := by
  classical
  let materialWitness := native_incidence_material_serial_continuation current trace actual
  let material := Classical.choose materialWitness
  have materialSpec := Classical.choose_spec materialWitness
  exact
    { actual := actual
      charged := nativeIncidenceSourceChargedContinuation current trace
      material := material
      charged_source := rfl
      material_token := materialSpec.1
      material_actual := materialSpec.2.1
      material_incidence := materialSpec.2.2.1
      material_reused := materialSpec.2.2.2
      charged_spent := native_incidence_source_charged_continuation_spent current trace actual }

end
end CPS1MaterialIncidence
