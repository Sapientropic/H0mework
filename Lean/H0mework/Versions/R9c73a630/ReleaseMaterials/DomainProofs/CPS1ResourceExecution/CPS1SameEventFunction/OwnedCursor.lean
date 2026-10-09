import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.OwnedDeformed
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.AmmoniaReached

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1SameEventFunction
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1BiologicalUpdate CPS1SameEventFunction.Classical
variable {frame : CPS1Recycling.Frame}

theorem current_stock_of_no_deformed (old : CPS1Deformation.Source.Occurrence frame)
    (absent : CPS1ReactiveField.heldDeformed old.current.stock = Option.none) :
    CPS1ReactiveField.liveStock (CPS1ReactiveField.next (CPS1ReactiveField.start old) [] [] []) =
      old.current.stock.map CPS1ReactiveField.LiveMaterial.old := by
  let current := CPS1ReactiveField.next (CPS1ReactiveField.start old) [] [] []
  have oldStock : CPS1ReactiveField.oldResidual current = old.current.stock := by
    unfold CPS1ReactiveField.oldResidual
    change (match CPS1ReactiveField.heldDeformed old.current.stock with
      | none => old.current.stock | some state => old.current.stock.erase (.deformed state)) = _
    rw [absent]
  have freshStock : current.ingress.atomic.source.stock = [] := by
    rw [empty_fresh_stock]
    unfold CPS1ReactiveField.enzymeView
    rw [absent]
    rfl
  unfold CPS1ReactiveField.liveStock
  rw [oldStock,freshStock,List.map_nil,List.append_nil]

theorem returned_owned_chain {before : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path [] [] noPhysicalSupply depth)
    (complete : event.physicalEvent.seed.translation.native.missing = none) :
    ownedChain event.reached = some (initialOwner event.physicalEvent.seed.translation.generatedFrame) := by
  have owned := physical_deformed_owned event.physicalEvent complete
  have entry := congrArg (fun value : CPS1ReactiveSourceEntry.Entry event.physicalEvent.seed.translation.generatedFrame =>
    CPS1ReactiveField.liveStock (entryCursor value).native.current) event.physicalEvent.actualEntry
  dsimp only [noPhysicalSupply] at entry
  rw [initial_entry_current,current_stock_of_no_deformed event.physicalEvent.deformation owned.2] at entry
  have reached := reached_live_stock event.outcome
  rw [entry] at reached
  change CPS1ReactiveField.liveStock event.reached.native.current = _ at reached
  unfold ownedChain
  change ((CPS1ReactiveField.liveStock event.reached.native.current).filterMap ownedLive?).head? = _
  rw [reached,List.filterMap_map]
  change (event.physicalEvent.deformation.current.stock.filterMap ownedDeformed?).head? = _
  rw [owned.1]
  rfl

theorem returned_paid_source {before : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path [] [] noPhysicalSupply depth)
    (complete : event.physicalEvent.seed.translation.native.missing = none)
    (ammonia : 0 < (liveResources before.native.current).count .ammonia) :
    ∃ source : Source event.reached, Classical.sourceAt event.reached = .ok source ∧ source.owned.chainRows = [] := by
  have owner := returned_owned_chain event complete
  have read := returned_ammonia event ammonia
  unfold Classical.sourceAt
  split
  · rename_i missing
    have impossible := owner.symm.trans missing
    cases impossible
  · rename_i ownerValue actualOwner
    have identity := Option.some.inj (actualOwner.symm.trans owner)
    subst ownerValue
    cases selected : ammoniaAt? event.reached with
    | none => rw [selected] at read; cases read
    | some material =>
      refine ⟨_,rfl,?_⟩
      rfl

end
end CPS1SameEventFunction
