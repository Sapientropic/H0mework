import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Pulse

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1QuantumNuclear
noncomputable section

inductive Species (frame : CPS1Recycling.Frame)
  | retained (old : CPS1ElectronicSource.Species frame)
  | guard (failure : Failure)

instance (frame : CPS1Recycling.Frame) : DecidableEq (Species frame) := Classical.decEq _
abbrev Stock (frame : CPS1Recycling.Frame) := List (Species frame)

inductive Reaction (frame : CPS1Recycling.Frame)
  | retained (old : CPS1ElectronicSource.Reaction frame)
  | nuclearPulse (state : CPS1ElectronicSource.State frame) (time : ℝ)

variable {frame : CPS1Recycling.Frame}

def guards {A : Type} (frame : CPS1Recycling.Frame) : Except Failure A → Stock frame
  | .error failure => [.guard failure] | .ok _ => []

def Reaction.reactants (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .retained old => (old.reactants frame).map Species.retained
  | .nuclearPulse state time =>
      [.retained (.quantum state),.retained (.rawTime time)] ++ guards frame (pulse? state time)

def Reaction.products (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .retained old => (old.products frame).map Species.retained
  | .nuclearPulse state time => match pulse? state time with
    | .error _ => []
    | .ok next => [.retained (.quantum next.1),.retained (.spentQuantum next.2)]

abbrev Execution (frame : CPS1Recycling.Frame) :=
  CPS1ResourceExecution.Inventory.Execution (Species frame) (Reaction frame)

def execute (frame : CPS1Recycling.Frame) : List (Reaction frame) → Stock frame → Execution frame :=
  CPS1ResourceExecution.Inventory.execute (Reaction.reactants frame) (Reaction.products frame)

end
end CPS1QuantumNuclear
