import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.AmmoniaReached
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Repair

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
namespace CPS1SameEventFunction
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1BiologicalUpdate
variable {frame : CPS1Recycling.Frame}

def localResource? : CPS1LocalChemicalExecution.Species frame → Option Species
  | .retained (.retained (.old species)) => some species
  | _ => none

theorem same_current_resource_reader (material : CPS1ReactiveField.LiveMaterial frame) :
    liveResource? material = (liveLocal? material).bind localResource? := by
  cases material
  repeat first
    | rfl
    | (rename_i inherited; cases inherited)

theorem ammonia_resource_positive {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : AmmoniaAt cursor) : 0 < (liveResources cursor.native.current).count .ammonia := by
  apply List.count_pos_iff.mpr
  apply List.mem_filterMap.mpr
  refine ⟨source.material,List.get_mem _ _,?_⟩
  rw [same_current_resource_reader]
  dsimp only [AmmoniaAt.material]
  rw [source.species]
  rfl

theorem ammonia_reader_resource_positive {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (read : (ammoniaAt? cursor).isSome) : 0 < (liveResources cursor.native.current).count .ammonia := by
  cases selected : ammoniaAt? cursor with
  | none => rw [selected] at read; cases read
  | some source => exact ammonia_resource_positive source

theorem repair_return_current {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
    {physical : PhysicalRaw} {depth : Nat}
    (whole : WholeRun before water raw path events feed physical depth) (supply : ContinuationRaw)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,before⟩))
    (selected : repairWhole whole supply = .repaired receipt) :
    ∃ first : NativeBiosyntheticEvent before water raw path events feed physical depth,
      ∃ update : RenewedBiosynthesis first supply,
        receipt.nextBody.current = ⟨update.returned.physicalEvent.seed.translation.generatedFrame,update.returned.reached⟩ := by
  unfold repairWhole classifyRepair at selected
  dsimp only at selected
  split at selected
  · rename_i successful
    have same := LocalRepairDisposition.repaired.inj selected
    subst receipt
    change ∃ first : NativeBiosyntheticEvent before water raw path events feed physical depth,
      ∃ update : RenewedBiosynthesis first supply,
      (bodyWrite (initialBody ⟨frame,before⟩)
        ⟨⟨water,raw,path,events,feed,physical,depth,supply⟩,whole,classifyWhole whole supply,rfl⟩).current = _
    change ResultSuccessful (classifyWhole whole supply) at successful
    have returned : ∀ result : BiologicalDisposition before water raw path events feed physical depth supply,
        ∀ actual : result = classifyWhole whole supply,
          ResultSuccessful result →
            ∃ first : NativeBiosyntheticEvent before water raw path events feed physical depth,
              ∃ update : RenewedBiosynthesis first supply,
              (bodyWrite (initialBody ⟨frame,before⟩)
                ⟨⟨water,raw,path,events,feed,physical,depth,supply⟩,whole,result,actual⟩).current =
                  ⟨update.returned.physicalEvent.seed.translation.generatedFrame,update.returned.reached⟩ := by
      intro result actual success
      cases result with
      | originalResidual original failed => cases success
      | localUpdate original first chosen next =>
        cases next with
        | residual continuation failure => cases success
        | renewed update => exact ⟨first,update,rfl⟩
    exact returned _ rfl successful
  · cases selected

def CurrentHasAmmonia (current : SourcePoint) : Prop := (ammoniaAt? current.2).isSome

end
end CPS1SameEventFunction
