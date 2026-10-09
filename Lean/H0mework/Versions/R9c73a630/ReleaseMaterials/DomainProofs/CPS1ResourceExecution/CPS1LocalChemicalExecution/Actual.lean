import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1StockRecursion.Source

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1LocalChemicalExecution.Actual
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

/-- This is the actual genomic CPS1 coordinate retained by the paid common frame.
The separately translated editor peptide is not selected by this mouth. -/
def cps1 (frame : CPS1Recycling.Frame) : Peptide := (.M,frame.peptide.2)

def species (frame : CPS1Recycling.Frame) : CPS1Reinitiation.Species frame :=
  CPS1StockRecursion.Dictionary.old frame (.releasedPeptide (cps1 frame))

theorem in_historical_remainder (frame : CPS1Recycling.Frame) :
    CPS1Recycling.Species.old (.releasedPeptide (cps1 frame)) ∈
      CPS1StockRecursion.Initial.historicalRemainder frame := by
  have present : CPS1Recycling.Species.old (.releasedPeptide (cps1 frame)) ∈
      CPS1Reinitiation.Handover.Source.historicalPassive frame := by
    simp [CPS1Reinitiation.Handover.Source.historicalPassive,cps1]
  simpa only [CPS1StockRecursion.Initial.historicalRemainder,
    List.mem_erase_of_ne (show CPS1Recycling.Species.old (.releasedPeptide (cps1 frame)) ≠
      CPS1Recycling.Species.old (.actor .metRS) from by simp)] using present

theorem in_current_surplus (frame : CPS1Recycling.Frame) (tail : List AA)
    (recycleExtra : List CPS1Recycling.RawMaterial) (scanExtra : List CPS1Reinitiation.RawMaterial)
    (bodyExtra : List CPS1Reinitiation.Handover.RawMaterial) :
    species frame ∈ CPS1StockRecursion.Initial.surplus frame tail recycleExtra scanExtra bodyExtra := by
  have present := in_historical_remainder frame
  have mapped : CPS1Reinitiation.Species.retained (CPS1Recycling.Species.old (.releasedPeptide (cps1 frame))) ∈
      (CPS1StockRecursion.Initial.historicalRemainder frame ++
        recycleExtra.map (CPS1Recycling.RawMaterial.species frame)).map CPS1Reinitiation.Species.retained :=
    List.mem_map.mpr ⟨_,List.mem_append_left _ present,rfl⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ mapped))

theorem current_free_cps1 (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite)
    (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (bodyFeed bodyExtra : List CPS1Reinitiation.Handover.RawMaterial)
    (bodyRaw : bodyFeed.Perm (CPS1Reinitiation.Handover.rawFuel Program.originalPeptide.2 ++ bodyExtra))
    (depth : Nat) :
    let frame := CPS1Recycling.Source.frame edits water additional
    let recycled := CPS1Recycling.run frame (CPS1Recycling.productiveEvents path) recycleFeed
    let prior := CPS1Reinitiation.run frame recycled path.after Molecules.mrna scanFeed
    let previous := CPS1Reinitiation.Handover.execute frame
      (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna 151 Program.originalPeptide.2)
      (prior.stock ++ bodyFeed.map (CPS1Reinitiation.Handover.RawMaterial.species frame))
    let result := CPS1StockRecursion.Source.requested frame path depth previous.stock
    species frame ∈ result.current.stock := by
  have paid := CPS1StockRecursion.Source.actual_requested_complete edits water additional path
    recycleFeed recycleExtra recyclingRaw scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw depth
  apply paid.2.1.mem_iff.mpr
  exact List.mem_append_right _ (in_current_surplus _ _ _ _ _)

end CPS1LocalChemicalExecution.Actual
