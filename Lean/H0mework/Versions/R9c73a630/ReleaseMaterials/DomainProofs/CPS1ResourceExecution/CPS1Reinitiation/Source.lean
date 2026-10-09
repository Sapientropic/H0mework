import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Reinitiation.Native
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Reinitiation.Accounting

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1Reinitiation.Source
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

/-- This is the exact old residue split, with the returned eIF5 consumed by recognition. -/
def nativeRemainder (frame : CPS1Recycling.Frame) : CPS1Recycling.StockAt frame :=
  let tail := frame.peptide.2
  (([.releasedPeptide (.M,tail)] ++ CPS1Recycling.ResidueSplit.remainingElongationWaste tail ++
    CPS1InitiationTermination.NativeComplete.terminationWaste ++
    CPS1InitiationTermination.NativeComplete.loadingWaste ++
    CPS1InitiationTermination.NativeComplete.chargingWaste tail ++ [.amp,.ppi] ++
    factorStock [.eIF5B]) : CPS1ResourceExecution.Stock).map CPS1Recycling.Species.old

def passiveOld (frame : CPS1Recycling.Frame) : CPS1Recycling.StockAt frame :=
  [.old .subunit60,.old (.actor .eRF1),.old .phosphate,.old .proton,
    .messageCoordinate,.old .amp,.old .ppi,.old (.actor .metRS)] ++
    CPS1Recycling.remainingTrna frame (CPS1Recycling.sourceTrna frame) ++ nativeRemainder frame

theorem actual_old_partition (edits : Target.Edits) (water additional : Nat)
    (site : CPS1Recycling.SplitSite) (feed extra : List CPS1Recycling.RawMaterial)
    (raw : feed.Perm (CPS1Recycling.freshFuel ++ extra)) :
    let frame := CPS1Recycling.Source.frame edits water additional
    let prior := CPS1Recycling.run frame (CPS1Recycling.productiveEvents site) feed
    prior.stock.Perm ([.next43 site.after,.old (.actor .eIF5)] ++
      passiveOld frame ++ extra.map (CPS1Recycling.RawMaterial.species frame)) := by
  have old := (CPS1Recycling.Source.source_native_complete edits water additional site feed extra raw).2.2.2
  dsimp only
  apply old.trans
  apply List.perm_iff_count.mpr
  intro species
  simp only [CPS1Recycling.coreProducts,CPS1Recycling.Source.remainder,
    CPS1Recycling.ResidueSplit.remainder,passiveOld,nativeRemainder,factorStock,
    List.map_append,List.map_cons,List.map_nil,List.count_cons,List.count_append,List.count_nil]
  omega

def surplus (frame : CPS1Recycling.Frame)
    (recycleExtra : List CPS1Recycling.RawMaterial) (extra : List RawMaterial) : Stock frame :=
  (passiveOld frame ++ recycleExtra.map (CPS1Recycling.RawMaterial.species frame)).map Species.retained ++
    extra.map (RawMaterial.species frame)

theorem actual_initial_inventory (edits : Target.Edits) (water additional : Nat)
    (site : CPS1Recycling.SplitSite) (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (feed extra : List RawMaterial) (raw : feed.Perm (rawFuel 151 ++ extra)) :
    let frame := CPS1Recycling.Source.frame edits water additional
    let prior := CPS1Recycling.run frame (CPS1Recycling.productiveEvents site) recycleFeed
    (initialStock frame prior Molecules.mrna feed).Perm
      (scanInput frame site.after Molecules.mrna 151 ++ surplus frame recycleExtra extra) := by
  let frame := CPS1Recycling.Source.frame edits water additional
  have old := (actual_old_partition edits water additional site recycleFeed recycleExtra recyclingRaw).map
    (Species.retained (frame := frame))
  have fresh := raw.map (RawMaterial.species frame)
  have combined := (old.append_right [Species.rna Molecules.mrna]).append fresh
  apply combined.trans
  apply List.perm_iff_count.mpr
  intro species
  dsimp only [frame]
  simp only [scanInput,surplus,rawFuel,RawMaterial.species,List.map_append,List.map_cons,List.map_nil,
    List.map_replicate,List.count_cons,List.count_append,List.count_nil]
  omega

/-- Actual recycled stock and the fixed registered editor RNA generate the full paid scan.
No recognized address, RNA equality witness, completed PIC or future trace is an input. -/
theorem native_complete (edits : Target.Edits) (water additional : Nat)
    (site : CPS1Recycling.SplitSite) (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (feed extra : List RawMaterial) (raw : feed.Perm (rawFuel 151 ++ extra)) :
    let frame := CPS1Recycling.Source.frame edits water additional
    let prior := CPS1Recycling.run frame (CPS1Recycling.productiveEvents site) recycleFeed
    let result := run frame prior site.after Molecules.mrna feed
    result.fired = scanProgram site.after Molecules.mrna ∧ result.remaining = [] ∧
      result.missing = none ∧ result.stock.Perm
        (scanProducts frame site.after Molecules.mrna 151 ++ surplus frame recycleExtra extra) :=
  native_scan_complete _ site.after Molecules.mrna 151 original_start_and_context.1
    original_start_and_context.2 _ _
    (actual_initial_inventory edits water additional site recycleFeed recycleExtra recyclingRaw feed extra raw)

theorem execution_from_actual_stock (edits : Target.Edits) (water additional : Nat)
    (site : CPS1Recycling.SplitSite) (recycleFeed : List CPS1Recycling.RawMaterial) (feed : List RawMaterial) :
    execution edits water additional site recycleFeed feed =
      some ⟨CPS1Recycling.Source.frame edits water additional,
        run (CPS1Recycling.Source.frame edits water additional)
          (CPS1Recycling.run (CPS1Recycling.Source.frame edits water additional)
            (CPS1Recycling.productiveEvents site) recycleFeed) site.after Molecules.mrna feed⟩ := by
  rw [execution,CPS1Recycling.Source.source_execution]
  rfl

theorem paid48_and_both_message_identities (edits : Target.Edits) (water additional : Nat)
    (site : CPS1Recycling.SplitSite) (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (feed extra : List RawMaterial) (raw : feed.Perm (rawFuel 151 ++ extra)) :
    let frame := CPS1Recycling.Source.frame edits water additional
    let prior := CPS1Recycling.run frame (CPS1Recycling.productiveEvents site) recycleFeed
    let result := run frame prior site.after Molecules.mrna feed
    Species.committed site.after Molecules.mrna 151 ∈ result.stock ∧
      Species.retained CPS1Recycling.Species.messageCoordinate ∈ result.stock ∧
      Species.retained (.old .subunit60) ∈ result.stock ∧
      Rna.parse Source.rawMrna = some Molecules.mrna ∧
      frame.messageTemplate = Target.coding
        (CPS1Deamination.CodingReadout.paidEdits edits (water+additional)) := by
  have generated := (native_complete edits water additional site recycleFeed recycleExtra recyclingRaw feed extra raw).2.2.2
  refine ⟨generated.mem_iff.mpr ?_,generated.mem_iff.mpr ?_,generated.mem_iff.mpr ?_,
    Molecules.complete_original_chemical_words.2,rfl⟩
  all_goals simp [scanProducts,surplus,passiveOld]

end CPS1Reinitiation.Source
