import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1StockRecursion.Stock

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1StockRecursion.Initial
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

def historicalRemainder (frame : CPS1Recycling.Frame) : CPS1Recycling.StockAt frame :=
  (CPS1Reinitiation.Handover.Source.historicalPassive frame).erase (.old (.actor .metRS))

theorem historical_partition (frame : CPS1Recycling.Frame) :
    (CPS1Reinitiation.Handover.Source.historicalPassive frame).Perm
      (.old (.actor .metRS) :: historicalRemainder frame) := by
  have present : CPS1Recycling.Species.old (.actor .metRS) ∈
      CPS1Reinitiation.Handover.Source.historicalPassive frame := by
    simp [CPS1Reinitiation.Handover.Source.historicalPassive]
  exact List.perm_cons_erase present

/-- The previous generation's message and all excess feed remain in the actual stock. -/
def surplus (frame : CPS1Recycling.Frame) (tail : List AA)
    (recycleExtra : List CPS1Recycling.RawMaterial)
    (scanExtra : List CPS1Reinitiation.RawMaterial)
    (extra : List CPS1Reinitiation.Handover.RawMaterial) : Dictionary.Stock frame :=
  (([.releasedPeptide (.M,tail)] ++ currencyWaste tail ++
    CPS1InitiationTermination.NativeComplete.chargingWaste tail ++
    [.gdp,.phosphate,.proton,.gdp,.phosphate,.proton,.gdp,.phosphate,.proton,
      .phosphate,.proton]) : CPS1ResourceExecution.Stock).map (Dictionary.old frame) ++
    CPS1Reinitiation.workProducts frame 151 ++
    (historicalRemainder frame ++
      recycleExtra.map (CPS1Recycling.RawMaterial.species frame)).map CPS1Reinitiation.Species.retained ++
    scanExtra.map (CPS1Reinitiation.RawMaterial.species frame) ++
    extra.map (CPS1Reinitiation.Handover.RawMaterial.species frame)

theorem products_inventory (frame : CPS1Recycling.Frame) (tail : List AA)
    (recycleExtra : List CPS1Recycling.RawMaterial)
    (scanExtra : List CPS1Reinitiation.RawMaterial)
    (extra : List CPS1Reinitiation.Handover.RawMaterial) :
    ((CPS1Reinitiation.Handover.bodyProducts tail).map
      (CPS1Reinitiation.NativeDictionary.embedded frame) ++
      CPS1Reinitiation.Handover.joinPassive frame Molecules.mrna ++
      CPS1Reinitiation.Handover.Source.surplus frame recycleExtra scanExtra extra).Perm
      (Native.reusable frame tail ++ surplus frame tail recycleExtra scanExtra extra) := by
  rw [show CPS1Reinitiation.NativeDictionary.embedded frame = Dictionary.old frame from rfl]
  apply List.perm_iff_count.mpr
  intro species
  have trnas := ((free_trnas_partition tail).map (Dictionary.old frame)).count_eq species
  have historical := ((historical_partition frame).map
    CPS1Reinitiation.Species.retained).count_eq species
  simp only [List.map_append,List.map_cons,List.count_append,List.count_cons] at trnas historical
  simp only [CPS1Reinitiation.Handover.bodyProducts,CPS1Reinitiation.Handover.joinPassive,
    CPS1Reinitiation.Handover.retainedAfterJoin,CPS1Reinitiation.Handover.Source.surplus,
    CPS1InitiationTermination.NativeComplete.terminationWaste,Native.reusable,
    Native.actors,Native.recruitment,surplus,CPS1Reinitiation.NativeDictionary.embedded,
    Dictionary.old,factorStock,List.map_append,List.map_cons,List.map_nil,
    List.count_append,List.count_cons,List.count_nil] at trnas historical ⊢
  omega

/-- This bridge consumes the completed actual editor execution; it does not reload the genesis stock. -/
theorem actual_stock (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite)
    (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (feed extra : List CPS1Reinitiation.Handover.RawMaterial)
    (raw : feed.Perm (CPS1Reinitiation.Handover.rawFuel Program.originalPeptide.2 ++ extra)) :
    let frame := CPS1Recycling.Source.frame edits water additional
    let recycled := CPS1Recycling.run frame (CPS1Recycling.productiveEvents path) recycleFeed
    let prior := CPS1Reinitiation.run frame recycled path.after Molecules.mrna scanFeed
    let result := CPS1Reinitiation.Handover.execute frame
      (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna 151 Program.originalPeptide.2)
      (prior.stock ++ feed.map (CPS1Reinitiation.Handover.RawMaterial.species frame))
    result.stock.Perm (Native.reusable frame Program.originalPeptide.2 ++
      surplus frame Program.originalPeptide.2 recycleExtra scanExtra extra) := by
  have generated := (CPS1Reinitiation.Handover.Source.native_complete edits water additional path
    recycleFeed recycleExtra recyclingRaw scanFeed scanExtra scanningRaw feed extra raw).2.2.2
  exact generated.trans (products_inventory _ _ _ _ _)

end CPS1StockRecursion.Initial
