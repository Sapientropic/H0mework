import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Joint

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1EnzymeBath
noncomputable section
open CPS1ResourceExecution

inductive Species (frame : CPS1Recycling.Frame)
  | retained (old : CPS1AtomicDynamics.Species frame)
  | joint (state : Joint.State frame)
  | rawRow (address : CPS1AtomicDynamics.Charged.Address) (row : CPS1AtomicDynamics.Body.Row)
  | rawEnergy (amount : ℝ)
  | rawTime (dt : ℝ)
  | spentPulse (pulse : CPS1AtomicDynamics.Body.Pulse)
  | guard (failure : CPS1AtomicDynamics.Body.Failure)
  | missingBody
  deriving DecidableEq

abbrev Stock (frame : CPS1Recycling.Frame) := List (Species frame)

def componentSpecies (frame : CPS1Recycling.Frame) (kind : Primary.TemplateKind) : Species frame :=
  .retained (.retained (.retained (CPS1LocalChemicalExecution.molecule frame kind.molecule)))

inductive Reaction (frame : CPS1Recycling.Frame)
  | capture (body : CPS1AtomicDynamics.Body.State frame)
  | requireBody
  | attach (state : Joint.State frame) (kind : Primary.TemplateKind)
  | report (state : Joint.State frame) (address : CPS1AtomicDynamics.Charged.Address) (row : CPS1AtomicDynamics.Body.Row)
  | deposit (state : Joint.State frame) (amount : ℝ)
  | pulse (state : Joint.State frame) (dt : ℝ)
  deriving DecidableEq

def guards {A : Type} (frame : CPS1Recycling.Frame) : Except CPS1AtomicDynamics.Body.Failure A → Stock frame
  | .error failure => [.guard failure] | .ok _ => []

def Reaction.reactants (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .capture body => [.retained (.body body)]
  | .requireBody => [.missingBody]
  | .attach state kind => [.joint state,componentSpecies frame kind]
  | .report state address row => [.joint state,.rawRow address row] ++ guards frame (Joint.report? frame state address row)
  | .deposit state amount => [.joint state,.rawEnergy amount] ++ guards frame (Joint.deposit? frame state amount)
  | .pulse state dt => [.joint state,.rawTime dt] ++ guards frame (Joint.pulse? frame state dt)

def Reaction.products (frame : CPS1Recycling.Frame) : Reaction frame → Stock frame
  | .capture body => [.joint (Joint.fromBody frame body)]
  | .requireBody => []
  | .attach state kind => [.joint (Joint.attach frame state kind)]
  | .report state address row =>
    match Joint.report? frame state address row with | .ok next => [.joint next] | .error _ => []
  | .deposit state amount =>
    match Joint.deposit? frame state amount with | .ok next => [.joint next] | .error _ => []
  | .pulse state dt =>
    match Joint.pulse? frame state dt with | .ok next => [.joint next.1,.spentPulse next.2] | .error _ => []

abbrev Execution (frame : CPS1Recycling.Frame) := Inventory.Execution (Species frame) (Reaction frame)

def execute (frame : CPS1Recycling.Frame) (program : List (Reaction frame)) (stock : Stock frame) : Execution frame :=
  Inventory.execute (Reaction.reactants frame) (Reaction.products frame) program stock

theorem capture_actual (frame : CPS1Recycling.Frame) (body : CPS1AtomicDynamics.Body.State frame)
    (stock surplus : Stock frame) (inventory : stock.Perm (.retained (.body body) :: surplus)) :
    let result := execute frame [.capture body] stock
    result.fired = [.capture body] ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm (.joint (Joint.fromBody frame body) :: surplus) := by
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame) (.capture body)
    surplus stock inventory with ⟨next,paid,generated⟩
  dsimp only
  simp only [execute,Inventory.execute,paid]
  exact ⟨True.intro,True.intro,True.intro,generated⟩

theorem attach_existing (frame : CPS1Recycling.Frame) (state : Joint.State frame) (kind : Primary.TemplateKind)
    (stock surplus : Stock frame) (inventory : stock.Perm ([.joint state,componentSpecies frame kind] ++ surplus)) :
    let result := execute frame [.attach state kind] stock
    result.fired = [.attach state kind] ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm (.joint (Joint.attach frame state kind) :: surplus) := by
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame) (.attach state kind)
    surplus stock inventory with ⟨next,paid,generated⟩
  dsimp only
  simp only [execute,Inventory.execute,paid]
  exact ⟨True.intro,True.intro,True.intro,generated⟩

theorem whole_inventory (frame : CPS1Recycling.Frame) (program : List (Reaction frame))
    (stock : Stock frame) (species : Species frame) :
    let result := execute frame program stock
    stock.count species + (Inventory.credit (Reaction.products frame) result.fired).count species =
      result.stock.count species + (Inventory.debit (Reaction.reactants frame) result.fired).count species :=
  Inventory.execution_balance (Reaction.reactants frame) (Reaction.products frame) program stock species

theorem actual_cut (frame : CPS1Recycling.Frame) (program : List (Reaction frame))
    (stock : Stock frame) (missing : Species frame) (cut : (execute frame program stock).missing = some missing) :
    ∃ reaction rest, (execute frame program stock).remaining = reaction :: rest ∧
      (execute frame program stock).stock.count missing < (reaction.reactants frame).count missing :=
  Inventory.execution_cut (Reaction.reactants frame) (Reaction.products frame) program stock missing cut

end
end CPS1EnzymeBath
