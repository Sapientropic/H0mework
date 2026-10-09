import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Pulse

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Following
noncomputable section

inductive Species (frame : CPS1Recycling.Frame)
  | retained (old : CPS1QuantumNuclear.Species frame)
  | following (state : CPS1ElectronicSource.State frame)
  | spentRelocation (receipt : RelocationReceipt)
  | spentPulse (pulse : CPS1ElectronicSource.ElectronicPulse)
  | guard (failure : Failure)

instance (frame : CPS1Recycling.Frame) : DecidableEq (Species frame) := Classical.decEq _
abbrev Stock (frame : CPS1Recycling.Frame) := List (Species frame)

inductive Reaction (frame : CPS1Recycling.Frame)
  | retained (old : CPS1QuantumNuclear.Reaction frame)
  | relocate (state : CPS1ElectronicSource.State frame)
  | pulse (state : CPS1ElectronicSource.State frame) (time : ℝ)
  | deposit (state : CPS1ElectronicSource.State frame) (amount : ℝ)
  | keepFollowing (state : CPS1ElectronicSource.State frame)

variable {frame : CPS1Recycling.Frame}

def guards {A : Type} (frame : CPS1Recycling.Frame) : Except Failure A → Stock frame
  | .error failure => [.guard failure] | .ok _ => []

def Reaction.reactants (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .retained old => (old.reactants frame).map Species.retained
  | .relocate state => [.retained (.retained (.quantum state))] ++ guards frame (relocate? state)
  | .pulse state time => [.following state,.retained (.retained (.rawTime time))] ++ guards frame (pulse? state time)
  | .deposit state amount => [.following state,.retained (.retained (.rawEnergy amount))] ++ guards frame (deposit? state amount)
  | .keepFollowing state => [.following state]

def Reaction.products (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .retained old => (old.products frame).map Species.retained
  | .relocate state => match relocate? state with
      | .error _ => [] | .ok next => [.following next.1,.spentRelocation next.2]
  | .pulse state time => match pulse? state time with
      | .error _ => [] | .ok next => [.following next.1,.spentPulse next.2]
  | .deposit state amount => match deposit? state amount with
      | .error _ => [] | .ok next => [.following next]
  | .keepFollowing state => [.following state]

abbrev Execution (frame : CPS1Recycling.Frame) :=
  CPS1ResourceExecution.Inventory.Execution (Species frame) (Reaction frame)

def execute (frame : CPS1Recycling.Frame) : List (Reaction frame) → Stock frame → Execution frame :=
  CPS1ResourceExecution.Inventory.execute (Reaction.reactants frame) (Reaction.products frame)

end
end CPS1Following
