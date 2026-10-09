import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Recycling.Native
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Recycling.Residue

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1Recycling.Source
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

/-- Both restrictions come from the actual coding update and its paid native program. -/
def frame (edits : Target.Edits) (water additional : Nat) : Frame :=
  ⟨Target.coding (CPS1Deamination.CodingReadout.paidEdits edits (water+additional)),
    CPS1EndogenousTranslation.selectedPeptide edits water additional,
    CPS1InitiationTermination.UnifiedBoundary.compile
      (CPS1EndogenousTranslation.selectedPeptide edits water additional).2,
    execute (CPS1InitiationTermination.UnifiedBoundary.compile
      (CPS1EndogenousTranslation.selectedPeptide edits water additional).2)
      (CPS1InitiationTermination.NativeComplete.rawFuel
        (CPS1EndogenousTranslation.selectedPeptide edits water additional).2)⟩

theorem source_frame (edits : Target.Edits) (water additional : Nat) :
    sourceFrame edits water additional = some (frame edits water additional) :=
  source_frame_generated edits water additional

/-- The same current stock is consumed. Raw event and material inputs cannot select a future object. -/
def execution (edits : Target.Edits) (water additional : Nat) (events : List RawEvent)
    (feed : List RawMaterial) : Option (Σ current : Frame, ExecutionAt current) :=
  (sourceFrame edits water additional).map (fun current => ⟨current,run current events feed⟩)

theorem source_execution (edits : Target.Edits) (water additional : Nat)
    (events : List RawEvent) (feed : List RawMaterial) :
    execution edits water additional events feed =
      some ⟨frame edits water additional,run (frame edits water additional) events feed⟩ := by
  rw [execution,source_frame]
  rfl


def remainder (current : Frame) : StockAt current :=
  (ResidueSplit.remainder current.peptide.2).map Species.old

theorem before_initiator_is_source_return (current : Frame) :
    beforeInitiator current (sourceTrna current) =
      (ResidueSplit.returnedInitiator current.peptide.2).map Species.old := by
  cases h : current.peptide.2 <;> simp [sourceTrna,beforeInitiator,ResidueSplit.returnedInitiator,h]

/-- Actual native products provide the postTC, all retained factors and the fine initiator. -/
theorem source_current_inventory (edits : Target.Edits) (water additional : Nat)
    (feed extra : List RawMaterial) (raw : feed.Perm (freshFuel ++ extra)) :
    let current := frame edits water additional
    (currentStock current feed).Perm
      (coreInput current (sourceTrna current) ++
        (remainder current ++ extra.map (RawMaterial.species current))) := by
  let current := frame edits water additional
  have native := (CPS1InitiationTermination.NativeComplete.canonical_raw_complete current.peptide.2).2.2.2
  change current.native.stock.Perm _ at native
  have partition := native.trans (ResidueSplit.final_products_recycling_partition current.peptide.2)
  have fine := (partition.map (Species.old (frame := current))).append
    (raw.map (RawMaterial.species current))
  change (currentStock current feed).Perm _ at fine
  apply fine.trans
  unfold coreInput
  rw [before_initiator_is_source_return]
  apply List.perm_iff_count.mpr
  intro species
  rw [source_post_restriction]
  simp only [remainder,Frame.postSpecies,ResidueSplit.nextActors,factorStock,
    freshFuel,RawMaterial.species,List.map_append,List.map_cons,List.map_nil,
    List.count_cons,List.count_append,List.count_nil]
  dsimp only [current]
  omega

/-- Every source coding update and either registered site path generate a paid bound 43S.
The only premise is a permutation of the raw resource inlet; every surplus is retained. -/
theorem source_native_complete (edits : Target.Edits) (water additional : Nat) (site : SplitSite)
    (feed extra : List RawMaterial) (raw : feed.Perm (freshFuel ++ extra)) :
    let current := frame edits water additional
    let result := run current (productiveEvents site) feed
    result.fired = compile current (productiveEvents site) ∧ result.remaining = [] ∧
      result.missing = none ∧ result.stock.Perm
        (coreProducts current (sourceTrna current) site ++ remainder current ++
          extra.map (RawMaterial.species current)) := by
  let current := frame edits water additional
  have inventory := source_current_inventory edits water additional feed extra raw
  have generated := native_core_complete current (sourceTrna current) site
    (remainder current ++ extra.map (RawMaterial.species current)) (currentStock current feed) inventory
  simpa only [run,productive_compiles,List.append_assoc] using generated

theorem source_bound43_and_same_message (edits : Target.Edits) (water additional : Nat)
    (site : SplitSite) (feed extra : List RawMaterial) (raw : feed.Perm (freshFuel ++ extra)) :
    let current := frame edits water additional
    let result := run current (productiveEvents site) feed
    Species.next43 site.after ∈ result.stock ∧ Species.old .subunit60 ∈ result.stock ∧
      Species.messageCoordinate ∈ result.stock ∧
      current.messageTemplate = Target.coding
        (CPS1Deamination.CodingReadout.paidEdits edits (water+additional)) := by
  have inventory := (source_native_complete edits water additional site feed extra raw).2.2.2
  refine ⟨inventory.mem_iff.mpr ?_,inventory.mem_iff.mpr ?_,inventory.mem_iff.mpr ?_,rfl⟩
  all_goals simp [coreProducts]

structure RecyclingContract : Prop where
  sourceFrame : type_of% source_frame
  execution : type_of% source_execution
  nativeComplete : type_of% source_native_complete
  bound43AndTemplate : type_of% source_bound43_and_same_message
  disposition : type_of% run_disposition
  inventory : type_of% run_inventory_balance
  potential : type_of% run_potential
  cut : type_of% run_cut
  currencies : type_of% run_currency_balance
  carriers : type_of% run_carrier_balance
  actors : type_of% run_actor_balance
  residuesAndMessage : type_of% run_residue_message_balance

theorem sourceGeneratedRecycling : RecyclingContract :=
  ⟨source_frame,source_execution,source_native_complete,source_bound43_and_same_message,
    run_disposition,run_inventory_balance,run_potential,run_cut,run_currency_balance,
    run_carrier_balance,run_actor_balance,run_residue_message_balance⟩

end CPS1Recycling.Source
