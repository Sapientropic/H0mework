import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Pulse
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Dictionary

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section

inductive Species (frame : CPS1Recycling.Frame)
  | retained (old : CPS1MolecularFrame.Species frame)
  | deformed (state : Material frame)
  | spentAdopt (reference : CPS1MolecularFrame.Material frame)
  | spentPulse (before : Material frame) (time : ℝ)
  | guard (failure : Failure)
  | missingCarrier

instance (frame : CPS1Recycling.Frame) : DecidableEq (Species frame) := Classical.decEq _
abbrev Stock (frame : CPS1Recycling.Frame) := List (Species frame)

inductive Reaction (frame : CPS1Recycling.Frame)
  | retained (old : CPS1MolecularFrame.Reaction frame)
  | adopt (reference : CPS1MolecularFrame.Material frame)
  | pulse (state : Material frame) (time : ℝ)
  | deposit (state : Material frame) (amount : ℝ)
  | keepDeformed (state : Material frame)
  | requireCarrier

variable {frame : CPS1Recycling.Frame}

def guards {A : Type} (frame : CPS1Recycling.Frame) : Except Failure A → Stock frame
  | .error failure => [.guard failure]
  | .ok _ => []

def Reaction.reactants (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .retained old => (old.reactants frame).map Species.retained
  | .adopt reference => [.retained (.molecular reference)] ++ guards frame (adopt? reference)
  | .pulse state time => [.deformed state,.retained (.retained (.retained (.retained (.rawTime time))))] ++
      guards frame (state.pulse? time)
  | .deposit state amount => [.deformed state,.retained (.retained (.retained (.retained (.rawEnergy amount))))] ++
      guards frame (state.deposit? amount)
  | .keepDeformed state => [.deformed state]
  | .requireCarrier => [.missingCarrier]

def Reaction.products (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .retained old => (old.products frame).map Species.retained
  | .adopt reference => match adopt? reference with
      | .error _ => []
      | .ok next => [.deformed next,.spentAdopt reference]
  | .pulse state time => match state.pulse? time with
      | .error _ => []
      | .ok next => [.deformed next.1,.spentPulse state time]
  | .deposit state amount => match state.deposit? amount with
      | .error _ => []
      | .ok next => [.deformed next]
  | .keepDeformed state => [.deformed state]
  | .requireCarrier => []

abbrev Execution (frame : CPS1Recycling.Frame) :=
  CPS1ResourceExecution.Inventory.Execution (Species frame) (Reaction frame)

def execute (frame : CPS1Recycling.Frame) : List (Reaction frame) → Stock frame → Execution frame :=
  CPS1ResourceExecution.Inventory.execute (Reaction.reactants frame) (Reaction.products frame)

end
end CPS1Deformation
