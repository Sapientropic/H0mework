import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Instruction
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeMovement
open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

/-- Source classification and slot-loop calls with generated review/boundary subtraces.
    Source lookup, validity, lifecycle and scalar/memory primitive internals retain their costs. -/
inductive Event where
  | source (event : Financial.InstructionSource.Event)
  | issueStep (event : Financial.IssueSource.Event)
  | movementStep (event : Financial.MovementSource.Event)
  | issue (classification : Fin 4)
  | movementRead (present : Bool)
  | movement (assignment : Bool) (quantity : ℚ)
  | allocationStart (available : ℚ) (slots : Nat)
  | allocationStep (event : Financial.AllocationSource.Event)
  | idle (available : ℚ)
  | iterate (position fuel : Nat)
  | append
  | finish (available used remaining : ℚ)
  deriving DecidableEq
private structure Part (α : Type) where
  value : α
  work : List Event

private def allocateOne {origin : Financial.InstructionOrigin input} (source : Financial.InstructionSource.Compilation input origin) (state : (Financial.process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) : Part (Financial.Allocation input state available) :=
  let made := Financial.AllocationSource.compileFrom input source state position available nonnegative
  ⟨made.result,made.work.map Event.allocationStep⟩
private theorem one_exact {origin : Financial.InstructionOrigin input} (source : Financial.InstructionSource.Compilation input origin) (state : (Financial.process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) :
    (allocateOne input source state position available nonnegative).value = Financial.allocateAt input origin state position available nonnegative :=
  (Financial.AllocationSource.compileFrom input source state position available nonnegative).exact
private theorem one_work {origin : Financial.InstructionOrigin input} (source : Financial.InstructionSource.Compilation input origin) (state : (Financial.process input).GeneratedState)
    (position : Nat) (available : ℚ) (nonnegative : 0 ≤ available) :
    (allocateOne input source state position available nonnegative).work.length ≤ 13 := by
  simpa only [allocateOne,List.length_map] using Financial.AllocationSource.from_work_bound input source state position available nonnegative
private def scan {origin : Financial.InstructionOrigin input} (source : Financial.InstructionSource.Compilation input origin) (position : Nat) :
    (fuel : Nat) → (state : (Financial.process input).GeneratedState) →
      (available : ℚ) → 0 ≤ available → Part (Financial.Allocation input state available)
  | 0,state,available,nonnegative => ⟨Financial.Allocation.idle input state available nonnegative,[.idle available]⟩
  | fuel+1,state,available,nonnegative =>
      let first := allocateOne input source state position available nonnegative
      let rest := scan source (position+1) fuel first.value.after first.value.remaining first.value.remaining_nonnegative
      ⟨first.value.append input rest.value,[.iterate position (fuel+1)]++first.work++rest.work++[.append]⟩
private theorem scan_exact {origin : Financial.InstructionOrigin input} (source : Financial.InstructionSource.Compilation input origin) (position fuel : Nat)
    (state : (Financial.process input).GeneratedState) (available : ℚ) (nonnegative : 0 ≤ available) :
    (scan input source position fuel state available nonnegative).value = Financial.allocateFrom input origin position fuel state available nonnegative := by
  induction fuel generalizing position state available with
  | zero => rfl
  | succ fuel ih =>
    simp only [scan,Financial.allocateFrom,ih]
    exact congrArg (fun first : Financial.Allocation input state available =>
      first.append input (Financial.allocateFrom input origin (position+1) fuel first.after first.remaining first.remaining_nonnegative))
      (one_exact input source state position available nonnegative)
private theorem scan_work {origin : Financial.InstructionOrigin input} (source : Financial.InstructionSource.Compilation input origin) (position fuel : Nat)
    (state : (Financial.process input).GeneratedState) (available : ℚ) (nonnegative : 0 ≤ available) :
    (scan input source position fuel state available nonnegative).work.length ≤ 15*fuel+1 := by
  induction fuel generalizing position state available with
  | zero => simp [scan]
  | succ fuel ih =>
    have first := one_work input source state position available nonnegative
    have rest := ih (position+1) (allocateOne input source state position available nonnegative).value.after
      (allocateOne input source state position available nonnegative).value.remaining
      (allocateOne input source state position available nonnegative).value.remaining_nonnegative
    simp only [scan,List.length_append,List.length_cons,List.length_nil]
    omega
private def allocation {origin : Financial.InstructionOrigin input} (source : Financial.InstructionSource.Compilation input origin) (state : (Financial.process input).GeneratedState)
    (available : ℚ) (nonnegative : 0 ≤ available) : Part (Financial.Allocation input state available) :=
  let made := scan input source 0 state.current.slots.length state available nonnegative
  ⟨made.value,[.allocationStart available state.current.slots.length]++made.work++
    [.finish available (made.value.used input) made.value.remaining]⟩
private theorem allocation_exact {origin : Financial.InstructionOrigin input} (source : Financial.InstructionSource.Compilation input origin) (state : (Financial.process input).GeneratedState)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    (allocation input source state available nonnegative).value = Financial.allocate input origin state available nonnegative :=
  scan_exact input source 0 _ state available nonnegative
private theorem allocation_work {origin : Financial.InstructionOrigin input} (source : Financial.InstructionSource.Compilation input origin) (state : (Financial.process input).GeneratedState)
    (available : ℚ) (nonnegative : 0 ≤ available) :
    (allocation input source state available nonnegative).work.length ≤ 15*state.current.slots.length+3 := by
  have h := scan_work input source 0 state.current.slots.length state available nonnegative
  simp only [allocation,List.length_append,List.length_cons,List.length_nil]
  omega
private def produceWith {origin : Financial.InstructionOrigin input}
    (source : Financial.InstructionSource.Compilation input origin)
    (before : (Financial.process input).GeneratedState) : Part (Financial.InstructionResult input origin before) :=
  let issue := Financial.IssueSource.compileFrom input source
  let issueWork := issue.work.map Event.issueStep
  match issue.result with
  | .issued claim exactOrigin => ⟨.issued claim exactOrigin,issueWork++[.issue 0]⟩
  | .rejected instruction original refused => ⟨.refused instruction original refused,issueWork++[.issue 1]⟩
  | .missingBirth party notBorn => ⟨.missingBirth party notBorn,issueWork++[.issue 2]⟩
  | .nonfinancial =>
    let moving := Financial.MovementSource.compileFrom input source
    let movingWork := moving.work.map Event.movementStep
    match moving.receipt with
    | none => ⟨.retained,issueWork++[.issue 3]++movingWork++[.movementRead false]⟩
    | some movement =>
      let made := allocation input source before movement.quantity (movement.quantity_nonnegative input)
      let assignment := match movement.kind with | .payment => false | .assignment => true
      ⟨.movement movement made.value,issueWork++[.issue 3]++movingWork++
        [.movementRead true,.movement assignment movement.quantity]++made.work⟩
private theorem with_exact {origin : Financial.InstructionOrigin input}
    (source : Financial.InstructionSource.Compilation input origin)
    (before : (Financial.process input).GeneratedState) :
    (produceWith input source before).value = Financial.consume input origin before := by
  unfold produceWith Financial.consume
  dsimp only
  rw [(Financial.IssueSource.compileFrom input source).exact,
    (Financial.MovementSource.compileFrom input source).exact]
  repeat' first | split | (solve | rfl | simp_all [allocation_exact] | grind [allocation_exact])
private theorem with_work {origin : Financial.InstructionOrigin input}
    (source : Financial.InstructionSource.Compilation input origin)
    (before : (Financial.process input).GeneratedState) :
    (produceWith input source before).work.length ≤ 15*before.current.slots.length+14 := by
  have issued := Financial.IssueSource.work_bound input source
  have moving := Financial.MovementSource.work_bound input source
  unfold produceWith
  dsimp only
  split <;> try (simp only [List.length_append,List.length_map,List.length_cons,List.length_nil]; omega)
  split
  · simp only [List.length_append,List.length_map,List.length_cons,List.length_nil]; omega
  · rename_i movement selected
    have h := allocation_work input source before movement.quantity (movement.quantity_nonnegative input)
    simp only [List.length_append,List.length_map,List.length_cons,List.length_nil]
    omega
private def produce (origin : Financial.InstructionOrigin input) (before : (Financial.process input).GeneratedState) :
    Part (Financial.InstructionResult input origin before) :=
  let source := Financial.InstructionSource.compile input origin
  let made := produceWith input source before
  ⟨made.value,source.work.map Event.source++made.work⟩
private theorem produce_exact (origin : Financial.InstructionOrigin input) (before : (Financial.process input).GeneratedState) :
    (produce input origin before).value = Financial.consume input origin before :=
  with_exact input (Financial.InstructionSource.compile input origin) before

/-- The one origin read/validity trace is shared by all incoming slots. -/
def budget (origin : Financial.InstructionOrigin input) (before : (Financial.process input).GeneratedState) : Nat := 15*before.current.slots.length+14+Financial.InstructionSource.budget input origin
private theorem produce_work (origin : Financial.InstructionOrigin input) (before : (Financial.process input).GeneratedState) :
    (produce input origin before).work.length ≤ budget input origin before := by
  have source := Financial.InstructionSource.work_bound input origin
  have made := with_work input (Financial.InstructionSource.compile input origin) before
  simp only [produce,List.length_append,List.length_map]
  dsimp only [budget]
  omega

structure Compilation (origin : Financial.InstructionOrigin input) (before : (Financial.process input).GeneratedState) where
  private mk ::
  result : Financial.InstructionResult input origin before
  work : List Event
  exact : result = Financial.consume input origin before
  private generated : result = (produce input origin before).value ∧ work = (produce input origin before).work

def compile (origin : Financial.InstructionOrigin input) (before : (Financial.process input).GeneratedState) : Compilation input origin before :=
  let made := produce input origin before
  ⟨made.value,made.work,produce_exact input origin before,⟨rfl,rfl⟩⟩
theorem work_bound (origin : Financial.InstructionOrigin input) (before : (Financial.process input).GeneratedState) :
    (compile input origin before).work.length ≤ budget input origin before := produce_work input origin before

theorem Compilation.next_exact {origin : Financial.InstructionOrigin input} {before : (Financial.process input).GeneratedState}
    (made : Compilation input origin before) : made.result.next input = (Financial.consume input origin before).next input := by rw [made.exact]
theorem Compilation.original_claims_retained {origin : Financial.InstructionOrigin input} {before : (Financial.process input).GeneratedState}
    (made : Compilation input origin before) : before.current.slots.map (Financial.slotClaim input) <+:
      (made.result.next input).current.slots.map (Financial.slotClaim input) := made.result.original_claims_retained input

theorem Compilation.history_retained {origin : Financial.InstructionOrigin input} {before : (Financial.process input).GeneratedState}
    (made : Compilation input origin before) : before.current.history <+: (made.result.next input).current.history := made.result.history_retained input
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.NativeMovement
