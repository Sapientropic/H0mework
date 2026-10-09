import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Payment

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1QuantumNuclear
noncomputable section
open CPS1ResourceExecution
variable {frame : CPS1Recycling.Frame}

theorem nuclear_actual (state : CPS1ElectronicSource.State frame) (time : ℝ)
    (next : CPS1ElectronicSource.State frame × CPS1ElectronicSource.ElectronicPulse)
    (actual : pulse? state time = .ok next) (stock : Stock frame)
    (carrier : Species.retained (.quantum state) ∈ stock)
    (clock : Species.retained (.rawTime time) ∈ stock.erase (.retained (.quantum state))) :
    execute frame [.nuclearPulse state time] stock =
      ⟨[.nuclearPulse state time],[],
        [.retained (.quantum next.1),.retained (.spentQuantum next.2)] ++
          (stock.erase (.retained (.quantum state))).erase (.retained (.rawTime time)),none⟩ := by
  have fired : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) (.nuclearPulse state time) stock =
      .ok ([.retained (.quantum next.1),.retained (.spentQuantum next.2)] ++
        (stock.erase (.retained (.quantum state))).erase (.retained (.rawTime time))) := by
    simp [Inventory.fire,Reaction.reactants,Reaction.products,guards,actual,Inventory.consume,carrier,clock]
  rw [execute,Inventory.execute_cons,fired]

theorem whole_inventory (program : List (Reaction frame)) (stock : Stock frame) (species : Species frame) :
    stock.count species + (Inventory.credit (Reaction.products frame) (execute frame program stock).fired).count species =
      (execute frame program stock).stock.count species +
        (Inventory.debit (Reaction.reactants frame) (execute frame program stock).fired).count species :=
  Inventory.execution_balance _ _ _ _ _

theorem actual_cut (program : List (Reaction frame)) (stock : Stock frame) (missing : Species frame)
    (cut : (execute frame program stock).missing = some missing) :
    ∃ reaction rest, (execute frame program stock).remaining = reaction :: rest ∧
      (execute frame program stock).stock.count missing < (reaction.reactants frame).count missing :=
  Inventory.execution_cut _ _ _ _ _ cut

theorem raw_length (actions : List Source.RawAction) (carrier : Option (CPS1ElectronicSource.Carrier frame)) :
    (Source.program frame carrier actions).length = actions.length := by
  induction actions generalizing carrier with
  | nil => rfl
  | cons action rest ih =>
    change (Source.program frame (action.next frame carrier) rest).length+1 = rest.length+1
    rw [ih]

theorem pending_same (cursor : Source.Cursor frame) (actions : List Source.RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    let available := cursor.stock ++
      feed.map (fun kind => Species.retained (.retained (CPS1EnzymeBath.componentSpecies frame kind))) ++
      actions.flatMap (Source.RawAction.material frame)
    let result := execute frame (Source.program frame (Source.heldCarrier frame available) (actions ++ cursor.pending)) available
    (Source.advance frame cursor actions feed).pending = (actions ++ cursor.pending).drop result.fired.length := rfl

end
end CPS1QuantumNuclear
