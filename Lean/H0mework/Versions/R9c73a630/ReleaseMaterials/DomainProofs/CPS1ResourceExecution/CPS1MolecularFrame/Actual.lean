import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Source

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section
open CPS1ResourceExecution
variable {frame : CPS1Recycling.Frame}

theorem adopt_actual (reference : CPS1ElectronicSource.State frame) (next : Material frame)
    (actual : adopt? reference = .ok next) (stock : Stock frame)
    (carrier : Species.retained (.following reference) ∈ stock) :
    execute frame [.adopt reference] stock =
      ⟨[.adopt reference],[],[.molecular next,.spentAdopt reference] ++
        stock.erase (.retained (.following reference)),none⟩ := by
  have fired : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) (.adopt reference) stock =
      .ok ([.molecular next,.spentAdopt reference] ++ stock.erase (.retained (.following reference))) := by
    simp [Inventory.fire,Reaction.reactants,Reaction.products,guards,actual,Inventory.consume,carrier]
  rw [execute,Inventory.execute_cons,fired]

theorem pulse_actual (state next : Material frame) (time : ℝ)
    (actual : state.pulse? time = .ok next) (stock : Stock frame) (carrier : Species.molecular state ∈ stock)
    (clock : Species.retained (.retained (.retained (.rawTime time))) ∈ stock.erase (.molecular state)) :
    execute frame [.pulse state time] stock =
      ⟨[.pulse state time],[],[.molecular next,.spentPulse state time] ++
        (stock.erase (.molecular state)).erase (.retained (.retained (.retained (.rawTime time)))),none⟩ := by
  have fired : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) (.pulse state time) stock =
      .ok ([.molecular next,.spentPulse state time] ++
        (stock.erase (.molecular state)).erase (.retained (.retained (.retained (.rawTime time))))) := by
    simp [Inventory.fire,Reaction.reactants,Reaction.products,guards,actual,Inventory.consume,carrier,clock]
  rw [execute,Inventory.execute_cons,fired]

theorem deposit_actual (state next : Material frame) (amount : ℝ)
    (actual : state.deposit? amount = .ok next) (stock : Stock frame) (carrier : Species.molecular state ∈ stock)
    (energy : Species.retained (.retained (.retained (.rawEnergy amount))) ∈ stock.erase (.molecular state)) :
    execute frame [.deposit state amount] stock =
      ⟨[.deposit state amount],[],[.molecular next] ++
        (stock.erase (.molecular state)).erase (.retained (.retained (.retained (.rawEnergy amount)))),none⟩ := by
  have fired : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) (.deposit state amount) stock =
      .ok ([.molecular next] ++
        (stock.erase (.molecular state)).erase (.retained (.retained (.retained (.rawEnergy amount))))) := by
    simp [Inventory.fire,Reaction.reactants,Reaction.products,guards,actual,Inventory.consume,carrier,energy]
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

theorem raw_length (actions : List Source.RawAction) (carrier : Option (Source.Carrier frame)) :
    (Source.program frame carrier actions).length = actions.length := by
  induction actions generalizing carrier with
  | nil => rfl
  | cons action rest ih =>
    change (Source.program frame (action.next frame carrier) rest).length+1 = rest.length+1
    rw [ih]

theorem pending_same (cursor : Source.Cursor frame) (actions : List Source.RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    let available := cursor.stock ++
      feed.map (fun kind => Species.retained (.retained (.retained (.retained
        (CPS1EnzymeBath.componentSpecies frame kind))))) ++ actions.flatMap (Source.RawAction.material frame)
    let result := execute frame (Source.program frame (Source.heldCarrier frame available) (actions ++ cursor.pending)) available
    (Source.advance frame cursor actions feed).pending = (actions ++ cursor.pending).drop result.fired.length := rfl

theorem legacy_phase_cut (action : CPS1Following.Source.RawAction) (state : Material frame) :
    (Source.RawAction.old action).reaction frame (some (.molecular state)) = .requireCarrier ∧
      (Source.RawAction.old action).next frame (some (.molecular state)) = some (.molecular state) := ⟨rfl,rfl⟩

theorem repeated_adopt (state : Material frame) :
    Source.RawAction.adopt.reaction frame (some (.molecular state)) = .keepMolecular state ∧
      Source.RawAction.adopt.next frame (some (.molecular state)) = some (.molecular state) := ⟨rfl,rfl⟩

end
end CPS1MolecularFrame
