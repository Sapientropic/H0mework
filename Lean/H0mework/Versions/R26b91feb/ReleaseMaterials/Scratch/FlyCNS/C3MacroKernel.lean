import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ProgrammeKernel
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3RegisteredInventory
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3TraceWriterStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ClockSchema
set_option autoImplicit false
namespace FlyCNS.C3Macro
open FlyCNS.C3Integer

structure Material where
  native : FlyCNS.C3Native.Material
  programme : FlyCNS.C3Programme.Material
  catalogue : FlyCNS.C3Registered.Material
structure Current where
  programme : FlyCNS.C3Programme.Current
  bodyWords : Vector Word 25
  sourceDocument : ByteArray
  visit : Nat
structure Cycle where
  startTick : Int64
  startPhysics : Nat
  events : FlyCNS.C3Integer.Events
  plastic : Array A
  trajectory : Array Float
  controls : Array Float
  integrations : ByteArray
structure Generated where
  current : Current
  cycles : Array Cycle
  registers : Vector FlyCNS.C3Writer.Register 59

def neuralTicks (operation : FlyCNS.C3Native.Operation) : Nat :=
  match operation with | .neural => 100 | .damage | .repair => 0
def controller (operation : FlyCNS.C3Native.Operation) (current : Current) : Except String Current :=
  match operation with
  | .neural => .ok current
  | .damage =>
    if current.programme.numerical.body.signal.controllerEnabled then
      .ok {current with programme := {current.programme with
        numerical := FlyCNS.C3Native.applyGate current.programme.numerical false}}
    else .error "the source gate is not in the opposite failure/settlement phase"
  | .repair =>
    if current.programme.numerical.body.signal.controllerEnabled then
      .error "the source gate is not in the opposite failure/settlement phase"
    else .ok {current with programme := {current.programme with
      numerical := FlyCNS.C3Native.applyGate current.programme.numerical true}}

def runCycles (m : Material) (before : Current) (programmeStart : FlyCNS.C3Programme.Current) (firstPhysics ticks : Nat) :
    Except String (FlyCNS.C3Programme.Current × Array Cycle) := do
  let mut programme := programmeStart
  let mut cycles := #[]
  for i in [:ticks] do
    let tick := getA programme.numerical.neural.neural[6]! 0
    let (later,result) ← FlyCNS.C3Programme.step m.native m.programme programme
    let received := FlyCNS.C3BodySignal.receive m.native.body.signal programme.numerical.body.signal result.events.fired
    let integrations := result.bodyEvents.physical.foldl (fun bytes p =>
      bytes++FlyCNS.C3Raw.floats (#[p.state.time]++p.state.position++p.state.velocity++p.state.warmstart++
        p.state.control++p.state.applied)++
        (before.bodyWords.get ⟨1,by decide⟩).bytes.extract (8*348) (8*762)) ByteArray.empty
    let trajectory := match result.bodyEvents.physical.back? with
      | none => #[]
      | some p =>
        let thorax := m.native.body.observation.thorax
        #[(tick+1).toUInt64.toFloat]++p.pose.position.extract (3*thorax) (3*thorax+3)++
          p.pose.quaternion.extract (4*thorax) (4*thorax+4)++received.signal++
          #[received.feeding,later.numerical.body.resource.values[0]!,later.numerical.body.resource.values[1]!]++result.bodyEvents.receipts
    cycles := cycles.push ⟨tick,firstPhysics+10*i,result.events,result.state.neural.plastic,
      trajectory,result.bodyEvents.controls.foldl (·++·) #[],integrations⟩
    programme := later
  return (programme,cycles)

def generate (m : Material) (operation : FlyCNS.C3Native.Operation) (before : Current) : Except String Generated :=
  if FlyCNS.C3Native.operationAt before.visit != operation then
    .error "operation not admitted at this source incidence"
  else match controller operation before with
  | .error why => .error why
  | .ok admitted =>
    let ticks := neuralTicks operation
    let firstPhysics := (before.bodyWords.get ⟨20,by decide⟩).bits 0 |>.toNat
    match runCycles m before admitted.programme firstPhysics ticks with
    | .error why => .error why
    | .ok (programme,cycles) =>
      let bodies := FlyCNS.C3Registered.generatedBodies before.bodyWords programme.numerical ticks
      let registers := FlyCNS.C3Registered.registers m.catalogue programme.numerical bodies
      .ok ⟨⟨programme,bodies,before.sourceDocument,before.visit+1⟩,cycles,registers⟩

def eventIntegers (values : Array Int64) : ByteArray := FlyCNS.C3Raw.signed values
def eventNodes (values : Array Nat) : ByteArray := FlyCNS.C3Raw.narrow values
def repeatedTick (cycle : Cycle) (size : Nat) : Array Int64 := Array.replicate size cycle.startTick
def eventMember (name dtype : String) (count : Nat) (bytes : ByteArray) : FlyCNS.C3TraceWriter.Member :=
  ⟨name,dtype,#[count],bytes⟩
def eventMembers (before : Current) (operation : FlyCNS.C3Native.Operation) (g : Generated) : Array FlyCNS.C3TraceWriter.Member :=
  let fired := g.cycles.flatMap fun c => c.events.fired
  let spikeTicks := g.cycles.flatMap fun c => repeatedTick c c.events.fired.size
  let inputs := g.cycles.flatMap fun c => c.events.inputCells
  let inputTicks := g.cycles.flatMap fun c => repeatedTick c c.events.inputCells.size
  let uv := g.cycles.flatMap fun c => c.events.inputUV
  let graded := g.cycles.flatMap fun c => c.events.gradedCells
  let gradedTicks := g.cycles.flatMap fun c => repeatedTick c c.events.gradedCells.size
  let fractions := g.cycles.flatMap fun c => c.events.gradedFraction
  let doses := g.cycles.flatMap fun c => c.events.gradedDose
  let terminals := g.cycles.flatMap fun c => c.events.terminalCells
  let terminalTicks := g.cycles.flatMap fun c => repeatedTick c c.events.terminalCells.size
  let gains := g.cycles.flatMap fun c => c.events.terminalGain
  let operationName := match operation with | .neural => "neural" | .damage => "damage" | .repair => "repair"
  let operationBytes := (operationName.toList.toArray.map fun c => FlyCNS.C3Writer.little c.toNat 4).foldl (·++·) ByteArray.empty
  let trajectory := g.cycles.flatMap fun c => c.trajectory
  #[eventMember "spike_neuron" "<i4" fired.size (eventNodes fired),
    eventMember "spike_tick" "<i8" spikeTicks.size (eventIntegers spikeTicks),
    eventMember "input_neuron" "<i4" inputs.size (eventNodes inputs),
    eventMember "input_tick" "<i8" inputTicks.size (eventIntegers inputTicks),
    eventMember "input_uv" "<i8" uv.size (eventIntegers uv),
    ⟨"trajectory","<f8",#[g.cycles.size,15],FlyCNS.C3Raw.floats trajectory⟩,
    ⟨"operation","<U"++toString operationName.length,#[],operationBytes⟩,
    ⟨"before_visit","<i8",#[],FlyCNS.C3Writer.little before.visit 8⟩,
    ⟨"after_visit","<i8",#[],FlyCNS.C3Writer.little g.current.visit 8⟩,
    eventMember "graded_tick" "<i8" gradedTicks.size (eventIntegers gradedTicks),
    eventMember "graded_neuron" "<i4" graded.size (eventNodes graded),
    eventMember "graded_fraction_q" "<i8" fractions.size (eventIntegers fractions),
    eventMember "graded_dose_q" "<i8" doses.size (eventIntegers doses),
    eventMember "gamma_terminal_tick" "<i8" terminalTicks.size (eventIntegers terminalTicks),
    eventMember "gamma_terminal_neuron" "<i4" terminals.size (eventNodes terminals),
    eventMember "gamma_terminal_gain_q" "<i8" gains.size (eventIntegers gains),
    eventMember "body_controller_gate_tick" "<i8" 0 ByteArray.empty,
    eventMember "body_controller_gate_enabled" "|b1" 0 ByteArray.empty]

def physicsMembers (before : Current) (g : Generated) : Array FlyCNS.C3TraceWriter.Member :=
  let ticks := g.cycles.flatMap fun c => (List.range 10).toArray.map
    fun i => Int64.ofNat (c.startPhysics+i)
  let controls := g.cycles.flatMap fun c => c.controls
  let integration := g.cycles.foldl (fun bytes c => bytes++c.integrations) (before.bodyWords.get ⟨1,by decide⟩).bytes
  #[eventMember "physics_tick" "<i8" ticks.size (eventIntegers ticks),
    ⟨"control","<f8",#[ticks.size,50],FlyCNS.C3Raw.floats controls⟩,
    ⟨"integration","<f8",#[ticks.size+1,762],integration⟩]

def learningMembers (g : Generated) : Array FlyCNS.C3TraceWriter.Member :=
  #["eligibility_q","dopamine_q","labile_q","stable_q","delta_uv","last_update_tick","modulation_scratch_q"].mapIdx
    fun i name =>
      let values := g.cycles.flatMap fun c => c.plastic[i]!
      let width := if i==1 || i==6 then 97 else 61210
      ⟨name,"<i8",#[g.cycles.size,width],eventIntegers values⟩

theorem generated_visit {m : Material} {operation : FlyCNS.C3Native.Operation} {before : Current} {g : Generated}
    (same : generate m operation before=.ok g) : g.current.visit=before.visit+1 := by
  unfold generate at same
  split at same
  next h => contradiction
  next h =>
    split at same
    next err reason => contradiction
    next admitted reason =>
      dsimp only at same
      split at same
      next err reason => contradiction
      next updated reason =>
        cases same
        rfl

end FlyCNS.C3Macro
