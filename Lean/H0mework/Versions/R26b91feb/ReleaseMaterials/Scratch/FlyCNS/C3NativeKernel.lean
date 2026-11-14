import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3BodyKernel
set_option autoImplicit false
namespace FlyCNS.C3Native
structure Material where
  neural : FlyCNS.C3Integer.Material
  body : FlyCNS.C3Body.Material
structure State where
  neural : FlyCNS.C3Integer.State
  pending : FlyCNS.C3Integer.Pending
  body : FlyCNS.C3Body.State
structure Result where
  state : State
  events : FlyCNS.C3Integer.Events
  bodyEvents : FlyCNS.C3Body.Result

/-- Complete native numerical F: current afferents generate original NN21
and plasticity, its actual spikes drive the body, and its later generates
the next current afferents. No externally evaluated update is a premise. -/
def step (m : Material) (s : State) : Result :=
  let neural := FlyCNS.C3Integer.step m.neural s.neural s.pending
  let body := FlyCNS.C3Body.advance m.body s.body neural.events.fired
  let nextPending : FlyCNS.C3Integer.Pending := ⟨body.feedback.stimulus,
    body.feedback.probabilities.map Float.toBits,body.feedback.auxiliary,body.feedback.currents⟩
  ⟨⟨neural.state,nextPending,body.state⟩,neural.events,body⟩

inductive Operation where
  | neural
  | damage
  | repair
  deriving DecidableEq

def operationAt (visit : Nat) : Operation :=
  if visit==55 then .damage else if visit==58 then .repair else .neural

def applyGate (state : State) (enabled : Bool) : State :=
  {state with body := {state.body with signal := {state.body.signal with controllerEnabled:=enabled}}}

def microsteps (m : Material) : Nat → State → State
  | 0,s => s
  | n+1,s => microsteps m n (step m s).state

def operate (m : Material) (op : Operation) (s : State) : State :=
  match op with
  | .neural => microsteps m 100 s
  | .damage => applyGate s false
  | .repair => applyGate s true

structure Current where
  numerical : State
  visit : Nat
def successor (m : Material) (current : Current) : Current :=
  ⟨operate m (operationAt current.visit) current.numerical,current.visit+1⟩

end FlyCNS.C3Native
