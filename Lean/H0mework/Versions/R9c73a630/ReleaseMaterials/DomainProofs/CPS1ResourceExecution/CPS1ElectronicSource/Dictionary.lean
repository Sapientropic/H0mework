import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Accounting

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource
noncomputable section

structure ElectronicPulse where
  time : ℝ
  beforeEnergy : ℝ
  afterEnergy : ℝ
  beforeReserve : ℝ
  afterReserve : ℝ

inductive Species (frame : CPS1Recycling.Frame)
  | retained (old : CPS1EnzymeBath.Species frame)
  | quantum (state : State frame)
  | rawRow (address : CPS1AtomicDynamics.Charged.Address) (row : CPS1AtomicDynamics.Body.Row)
  | rawEnergy (amount : ℝ)
  | rawTime (time : ℝ)
  | spentQuantum (pulse : ElectronicPulse)
  | guard (failure : Failure)
  | missingCarrier

instance (frame : CPS1Recycling.Frame) : DecidableEq (Species frame) := Classical.decEq _
abbrev Stock (frame : CPS1Recycling.Frame) := List (Species frame)

variable {frame : CPS1Recycling.Frame}

inductive Carrier (frame : CPS1Recycling.Frame)
  | joint (source : CPS1EnzymeBath.Joint.State frame)
  | quantum (source : State frame)

def jointPulse? (frame : CPS1Recycling.Frame) (joint : CPS1EnzymeBath.Joint.State frame) (time : ℝ) :
    Except Failure (CPS1EnzymeBath.Joint.State frame × CPS1AtomicDynamics.Body.Pulse) :=
  (CPS1EnzymeBath.Joint.pulse? frame joint time).mapError Failure.body

def quantumReport? (state : State frame) (address : CPS1AtomicDynamics.Charged.Address)
    (row : CPS1AtomicDynamics.Body.Row) : Except Failure (State frame) := by
  classical
  exact match CPS1EnzymeBath.Joint.report? frame state.geometry.originJoint address row with
    | .error failure => .error (.body failure)
    | .ok joint => if joint = state.geometry.originJoint then .ok state
      else .error (.body (.conflictingRow address))

inductive Reaction (frame : CPS1Recycling.Frame)
  | prepare (joint : CPS1EnzymeBath.Joint.State frame)
  | jointAttach (joint : CPS1EnzymeBath.Joint.State frame) (kind : CPS1EnzymeBath.Primary.TemplateKind)
  | jointReport (joint : CPS1EnzymeBath.Joint.State frame)
      (address : CPS1AtomicDynamics.Charged.Address) (row : CPS1AtomicDynamics.Body.Row)
  | jointDeposit (joint : CPS1EnzymeBath.Joint.State frame) (amount : ℝ)
  | jointPulse (joint : CPS1EnzymeBath.Joint.State frame) (time : ℝ)
  | quantumReport (state : State frame) (address : CPS1AtomicDynamics.Charged.Address) (row : CPS1AtomicDynamics.Body.Row)
  | quantumDeposit (state : State frame) (amount : ℝ)
  | quantumPulse (state : State frame) (time : ℝ)
  | keepQuantum (state : State frame)
  | requireCarrier

def guards {A : Type} (frame : CPS1Recycling.Frame) : Except Failure A → Stock frame
  | .ok _ => [] | .error failure => [.guard failure]

def Reaction.reactants (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .prepare joint => [.retained (.joint joint)] ++ guards frame (State.fromJoint? frame joint)
  | .jointAttach joint kind => [.retained (.joint joint),.retained (CPS1EnzymeBath.componentSpecies frame kind)]
  | .jointReport joint address row => [.retained (.joint joint),.rawRow address row] ++
      guards frame ((CPS1EnzymeBath.Joint.report? frame joint address row).mapError Failure.body)
  | .jointDeposit joint amount => [.retained (.joint joint),.rawEnergy amount] ++
      guards frame ((CPS1EnzymeBath.Joint.deposit? frame joint amount).mapError Failure.body)
  | .jointPulse joint time => [.retained (.joint joint),.rawTime time] ++ guards frame (jointPulse? frame joint time)
  | .quantumReport state address row => [.quantum state,.rawRow address row] ++ guards frame (quantumReport? state address row)
  | .quantumDeposit state amount => [.quantum state,.rawEnergy amount] ++ guards frame (state.deposit? amount)
  | .quantumPulse state time => [.quantum state,.rawTime time] ++ guards frame (state.pulse? time)
  | .keepQuantum state => [.quantum state]
  | .requireCarrier => [.missingCarrier]

def Reaction.products (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .prepare joint => match State.fromJoint? frame joint with | .ok state => [.quantum state] | .error _ => []
  | .jointAttach joint kind => [.retained (.joint (CPS1EnzymeBath.Joint.attach frame joint kind))]
  | .jointReport joint address row => match CPS1EnzymeBath.Joint.report? frame joint address row with
      | .ok next => [.retained (.joint next)] | .error _ => []
  | .jointDeposit joint amount => match CPS1EnzymeBath.Joint.deposit? frame joint amount with
      | .ok next => [.retained (.joint next)] | .error _ => []
  | .jointPulse joint time => match jointPulse? frame joint time with
      | .ok next => [.retained (.joint next.1),.retained (.spentPulse next.2)] | .error _ => []
  | .quantumReport state address row => match quantumReport? state address row with
      | .ok next => [.quantum next] | .error _ => []
  | .quantumDeposit state amount => match state.deposit? amount with | .ok next => [.quantum next] | .error _ => []
  | .quantumPulse state time => match state.pulse? time with
      | .ok next => [.quantum next,.spentQuantum ⟨time,state.energy,next.energy,state.reserve,next.reserve⟩]
      | .error _ => []
  | .keepQuantum state => [.quantum state]
  | .requireCarrier => []

abbrev Execution (frame : CPS1Recycling.Frame) :=
  CPS1ResourceExecution.Inventory.Execution (Species frame) (Reaction frame)

def execute (frame : CPS1Recycling.Frame) (program : List (Reaction frame)) (stock : Stock frame) : Execution frame :=
  CPS1ResourceExecution.Inventory.execute (Reaction.reactants frame) (Reaction.products frame) program stock

end
end CPS1ElectronicSource
