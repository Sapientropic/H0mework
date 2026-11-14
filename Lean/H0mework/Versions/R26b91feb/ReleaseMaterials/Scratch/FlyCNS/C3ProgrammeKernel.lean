import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3NativeKernel
set_option autoImplicit false
namespace FlyCNS.C3Programme
open FlyCNS.C3Integer

structure EnvironmentFrame where
  tick : Int64
  odor : Array Float
  sugar : Array Float
  water : Array Float
structure NeuralFrame where
  start : Int64
  stop : Int64
  period : Int64
  neurons : Array Nat
  pulse : Int64
structure Material where
  environment : Array EnvironmentFrame
  neural : Array NeuralFrame
structure StockEvent where
  tick : Int64
  odorBefore : Array Float
  odorAfter : Array Float
  sugarBefore : Array Float
  sugarAfter : Array Float
  sugarSupplied : Array Float
  sugarRemoved : Array Float
  waterBefore : Array Float
  waterAfter : Array Float
  waterSupplied : Array Float
  waterRemoved : Array Float
structure Current where
  numerical : FlyCNS.C3Native.State
  environmentHistory : Array StockEvent

def difference (after before : Array Float) : Array Float × Array Float :=
  let delta := after.mapIdx fun i v => v-before[i]!
  (delta.map fun v => max v (Float.ofBits 0),delta.map fun v => max (-v) (Float.ofBits 0))

/-- Original source programme acts before the neural primitive. The schedule
is original source material, not a later firing/reward/choice tape. -/
def apply (m : Material) (c : Current) : Except String Current := Id.run do
  let tick := getA c.numerical.neural.neural[6]! 0
  let mut s := c.numerical
  let mut history := c.environmentHistory
  for frame in m.environment do
    if frame.tick != tick then continue
    if let some previous := history.back? then
      if previous.tick >= tick then return .error "raw environmental input repeated"
    let (sugarSupplied,sugarRemoved) := difference frame.sugar s.body.resource.sugar
    let (waterSupplied,waterRemoved) := difference frame.water s.body.resource.water
    history := history.push ⟨tick,s.body.odorGains,frame.odor,s.body.resource.sugar,frame.sugar,
      sugarSupplied,sugarRemoved,s.body.resource.water,frame.water,waterSupplied,waterRemoved⟩
    let resource := {s.body.resource with sugar:=frame.sugar, water:=frame.water}
    let body := {s.body with odorGains:=frame.odor, resource:=resource}
    s := {s with body:=body}
  let mut cells := s.pending.auxiliary
  let mut pulses := s.pending.uv
  let mut added := false
  for frame in m.neural do
    if frame.start <= tick && tick < frame.stop && (tick-frame.start)%frame.period == 0 then
      cells := cells++frame.neurons
      pulses := pulses++Array.replicate frame.neurons.size frame.pulse
      added := true
  if added then
    let unique := (cells.toList.mergeSort (·≤·)).eraseDups.toArray
    let values := unique.map fun cell => Id.run do
      let mut value : Int64 := 0
      for i in [:cells.size] do if cells[i]! == cell then value := value+pulses[i]!
      return value
    let pending := {s.pending with auxiliary:=unique, uv:=values}
    s := {s with pending:=pending}
  return .ok ⟨s,history⟩

def step (native : FlyCNS.C3Native.Material) (m : Material) (c : Current) : Except String (Current × FlyCNS.C3Native.Result) := do
  let applied ← apply m c
  let result := FlyCNS.C3Native.step native applied.numerical
  return (⟨result.state,applied.environmentHistory⟩,result)

end FlyCNS.C3Programme
