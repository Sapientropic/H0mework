import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.State
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Dictionary

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section

inductive Species (frame : CPS1Recycling.Frame)
  | retained (old : CPS1Following.Species frame)
  | molecular (state : Material frame)
  | spentAdopt (reference : CPS1ElectronicSource.State frame)
  | spentPulse (before : Material frame) (time : ℝ)
  | guard (failure : Failure)
  | missingCarrier

instance (frame : CPS1Recycling.Frame) : DecidableEq (Species frame) := Classical.decEq _
abbrev Stock (frame : CPS1Recycling.Frame) := List (Species frame)

inductive Reaction (frame : CPS1Recycling.Frame)
  | retained (old : CPS1Following.Reaction frame)
  | adopt (reference : CPS1ElectronicSource.State frame)
  | pulse (state : Material frame) (time : ℝ)
  | deposit (state : Material frame) (amount : ℝ)
  | keepMolecular (state : Material frame)
  | requireCarrier

variable {frame : CPS1Recycling.Frame}

def guards {A : Type} (frame : CPS1Recycling.Frame) : Except Failure A → Stock frame
  | .error failure => [.guard failure]
  | .ok _ => []

def Reaction.reactants (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .retained old => (old.reactants frame).map Species.retained
  | .adopt reference => [.retained (.following reference)] ++ guards frame (adopt? reference)
  | .pulse state time => [.molecular state,.retained (.retained (.retained (.rawTime time)))] ++
      guards frame (state.pulse? time)
  | .deposit state amount => [.molecular state,.retained (.retained (.retained (.rawEnergy amount)))] ++
      guards frame (state.deposit? amount)
  | .keepMolecular state => [.molecular state]
  | .requireCarrier => [.missingCarrier]

def Reaction.products (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .retained old => (old.products frame).map Species.retained
  | .adopt reference => match adopt? reference with
      | .error _ => []
      | .ok next => [.molecular next,.spentAdopt reference]
  | .pulse state time => match state.pulse? time with
      | .error _ => []
      | .ok next => [.molecular next,.spentPulse state time]
  | .deposit state amount => match state.deposit? amount with
      | .error _ => []
      | .ok next => [.molecular next]
  | .keepMolecular state => [.molecular state]
  | .requireCarrier => []

abbrev Execution (frame : CPS1Recycling.Frame) :=
  CPS1ResourceExecution.Inventory.Execution (Species frame) (Reaction frame)

def execute (frame : CPS1Recycling.Frame) : List (Reaction frame) → Stock frame → Execution frame :=
  CPS1ResourceExecution.Inventory.execute (Reaction.reactants frame) (Reaction.products frame)

end
end CPS1MolecularFrame
