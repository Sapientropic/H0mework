import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Translation
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.EmptyResume
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Repair
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.OwnedCursor
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1SameEventFunction.RepairCurrent

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1BiologicalUpdate CPS1SameEventFunction
attribute [local irreducible] registeredBefore registeredOld

noncomputable def registeredWhole : WholeRun registeredBefore 2 registeredTranslationRaw .first [] [] noPhysicalSupply 0 :=
  executeWhole registeredBefore 2 registeredTranslationRaw .first [] [] noPhysicalSupply 0

private theorem reached_peptide {frame : CPS1Recycling.Frame}
    {before : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path [] [] noPhysicalSupply depth) :
    actualGenePeptide event.reached.native.current = some event.physicalEvent.seed.translation.peptide := by
  unfold actualGenePeptide readPeptide readCoding
  rw [reached_native_genome event]
  rw [← event.physicalEvent.seed.translation.genomic.event.codingActual,
    ← event.physicalEvent.seed.translation.genomic.event.peptideActual]
  exact event.physicalEvent.seed.translation.peptideSource

private theorem reached_mature {frame : CPS1Recycling.Frame}
    {before : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path [] [] noPhysicalSupply depth)
    (decoded : event.physicalEvent.seed.translation.peptide = CPS1EndogenousTranslation.correctedPeptide) :
    readProteinDamage event.reached.native.current = .fullLength := by
  unfold readProteinDamage
  rw [reached_peptide event,decoded]
  have mature : ¬ (CPS1EndogenousTranslation.correctedPeptide.2.length + 1 < Source.referenceProtein.length) := by
    decide +kernel
  simp only [if_neg mature]

theorem registered_complete_whole_birth :
    ∃ event : NativeBiosyntheticEvent registeredBefore 2 registeredTranslationRaw .first [] [] noPhysicalSupply 0,
      consumeWhole registeredWhole = .produced event ∧
      event.physicalEvent.seed.translation.peptide = CPS1EndogenousTranslation.correctedPeptide ∧
      event.physicalEvent.seed.translation.genomic.event.result.remaining = [] ∧
      event.physicalEvent.seed.translation.native.missing = none ∧ event.newlyProduced = 1 ∧
      readProteinDamage event.reached.native.current = .fullLength ∧
      0 < event.physicalEvent.seed.translation.native.stock.count .ammonia := by
  have source := registered_translation_complete
  cases selected : translateLive registeredBefore.native.current 2 registeredTranslationRaw with
  | genomicRejected original => rw [selected] at source; cases source
  | decodingRejected genomic unspent unspentSource failure => rw [selected] at source; cases source
  | translated translation =>
    rw [selected] at source
    let returned := physicalEvent registeredBefore 2 registeredTranslationRaw .first [] [] noPhysicalSupply
      (sourceSeed registeredBefore.native.current 2 registeredTranslationRaw .first [] [] translation)
    let event := nativeBiosyntheticEvent registeredBefore 2 registeredTranslationRaw .first [] [] noPhysicalSupply 0
      returned (runBirth returned.entry 0)
    have emitted : consumeWhole registeredWhole = .produced event :=
      consume_execute_translated registeredBefore 2 _ .first [] [] noPhysicalSupply 0 translation selected
    have birth : event.newlyProduced = 1 := by
      rw [biosynthetic_birth_credit]
      exact source.2.2.2.1
    exact ⟨event,emitted,source.1,source.2.1,source.2.2.1,birth,reached_mature event source.1,source.2.2.2.2⟩

private theorem next_whole_birth
    (event : NativeBiosyntheticEvent registeredBefore 2 registeredTranslationRaw .first [] [] noPhysicalSupply 0)
    (decoded : event.physicalEvent.seed.translation.peptide = CPS1EndogenousTranslation.correctedPeptide)
    (completeSource : event.physicalEvent.seed.translation.genomic.event.result.remaining = []) :
    ∃ returned : NativeBiosyntheticEvent event.reached 0 registeredTranslationRaw .first [] [] noPhysicalSupply 0,
      consumeWhole (continueBiosynthesis event registeredSupply).next = .produced returned ∧
      returned.physicalEvent.seed.translation.coding = event.physicalEvent.seed.translation.coding ∧
      returned.physicalEvent.seed.translation.native.missing = none ∧ returned.newlyProduced = 1 ∧
      readProteinDamage returned.reached.native.current = .fullLength := by
  obtain ⟨translation,selected,coding,peptide⟩ := next_translation_from_complete_source event registeredTranslationRaw completeSource
  have decodedNext : translation.peptide = CPS1EndogenousTranslation.correctedPeptide := peptide.trans decoded
  have inventory : translation.available.Perm
      (CPS1InitiationTermination.NativeComplete.rawFuel translation.peptide.2 ++ translation.genomic.event.result.stock) := by
    rw [translation.availableSource]
    simp only [registeredTranslationRaw,translation_raw_species]
    rw [decodedNext]
    exact List.perm_append_comm
  have native := CPS1InitiationTermination.NativeComplete.native_compile_complete
    translation.peptide.2 translation.genomic.event.result.stock translation.available inventory
  have complete : translation.native.missing = none := by
    rw [translation.actual,translation.programSource]
    exact native.2.2.1
  let source := physicalEvent event.reached 0 registeredTranslationRaw .first [] [] noPhysicalSupply
    (sourceSeed event.reached.native.current 0 registeredTranslationRaw .first [] [] translation)
  let returned := nativeBiosyntheticEvent event.reached 0 registeredTranslationRaw .first [] [] noPhysicalSupply 0
    source (runBirth source.entry 0)
  have emitted : consumeWhole (continueBiosynthesis event registeredSupply).next = .produced returned :=
    consume_execute_translated event.reached 0 _ .first [] [] noPhysicalSupply 0 translation selected
  have birth : returned.newlyProduced = 1 := by
    rw [biosynthetic_birth_credit]
    exact (translation_release_is_new _ _ _ translation complete).2.1
  exact ⟨returned,emitted,coding,complete,birth,reached_mature returned decodedNext⟩

private theorem registered_renewed
    (event : NativeBiosyntheticEvent registeredBefore 2 registeredTranslationRaw .first [] [] noPhysicalSupply 0)
    (decoded : event.physicalEvent.seed.translation.peptide = CPS1EndogenousTranslation.correctedPeptide)
    (completeSource : event.physicalEvent.seed.translation.genomic.event.result.remaining = [])
    (native : event.physicalEvent.seed.translation.native.missing = none) :
    ∃ update, renewBiosynthesis event registeredSupply = .renewed update := by
  obtain ⟨returned,selected,coding,nextNative,birth,nextRead⟩ := next_whole_birth event decoded completeSource
  have priorDamage : PrematureStop (readProteinDamage registeredBefore.native.current) := by
    rw [registered_before_damage]
    trivial
  have repaired := reached_mature event decoded
  unfold renewBiosynthesis
  dsimp only
  simp only [dif_pos native,dif_pos priorDamage,dif_pos repaired]
  split
  · rename_i cut actualCut
    have impossible := selected.symm.trans actualCut
    cases impossible
  · rename_i found actualFound
    have same : found = returned := BiosyntheticDisposition.produced.inj (actualFound.symm.trans selected)
    subst found
    simp only [dif_pos coding,dif_pos nextNative,dif_pos nextRead]
    exact ⟨_,rfl⟩

section
attribute [local irreducible] ResultSuccessful

private theorem whole_successful (whole : WholeRun registeredBefore 2 registeredTranslationRaw .first [] [] noPhysicalSupply 0)
    (event : NativeBiosyntheticEvent registeredBefore 2 registeredTranslationRaw .first [] [] noPhysicalSupply 0)
    (emitted : consumeWhole whole = .produced event)
    (decoded : event.physicalEvent.seed.translation.peptide = CPS1EndogenousTranslation.correctedPeptide)
    (completeSource : event.physicalEvent.seed.translation.genomic.event.result.remaining = [])
    (native : event.physicalEvent.seed.translation.native.missing = none) :
    ResultSuccessful (classifyWhole whole registeredSupply) := by
  obtain ⟨update,renewed⟩ := registered_renewed event decoded completeSource native
  unfold classifyWhole
  split
  · rename_i original selected
    have impossible := emitted.symm.trans selected
    cases impossible
  · rename_i found selected
    have same : found = event := BiosyntheticDisposition.produced.inj (selected.symm.trans emitted)
    subst found
    unfold ResultSuccessful
    rw [renewed]
    trivial

end

theorem registered_whole_successful : ResultSuccessful (classifyWhole registeredWhole registeredSupply) := by
  obtain ⟨event,emitted,decoded,completeSource,native,_birth,_read,_ammonia⟩ := registered_complete_whole_birth
  exact whole_successful registeredWhole event emitted decoded completeSource native

theorem registered_repair_selected :
    ∃ receipt : LocalRepairReceipt (initialBody ⟨registeredFrame,registeredBefore⟩),
      repairWhole registeredWhole registeredSupply = .repaired receipt :=
  repair_whole_of_success registeredWhole registeredSupply registered_whole_successful

private theorem returned_ammonia_from_native {frame : CPS1Recycling.Frame}
    {before : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} {depth : Nat}
    (event : NativeBiosyntheticEvent before water raw path [] [] noPhysicalSupply depth)
    (input : 0 < event.physicalEvent.seed.translation.native.stock.count .ammonia) :
    (ammoniaAt? event.reached).isSome := by
  have count := CPS1SameEventFunction.physical_event_ammonia event.physicalEvent
  have positive : 0 < event.physicalEvent.deformation.current.stock.count
      (CPS1SameEventFunction.deformedNH3 event.physicalEvent.seed.translation.generatedFrame) := by
    rw [count]
    exact input
  let initial := CPS1ReactiveField.next (CPS1ReactiveField.start event.physicalEvent.deformation) [] [] []
  have held : CPS1ReactiveField.LiveMaterial.old
      (CPS1SameEventFunction.deformedNH3 event.physicalEvent.seed.translation.generatedFrame) ∈
      CPS1ReactiveField.liveStock initial := by
    apply List.mem_append_left _
    apply List.mem_map_of_mem
    apply List.count_pos_iff.mp
    rw [CPS1SameEventFunction.old_residual_ammonia]
    exact positive
  have entry := congrArg (fun value : CPS1ReactiveSourceEntry.Entry event.physicalEvent.seed.translation.generatedFrame =>
    CPS1ReactiveField.liveStock (entryCursor value).native.current) event.physicalEvent.actualEntry
  rw [initial_entry_current] at entry
  have reached := CPS1SameEventFunction.reached_live_stock event.outcome
  rw [entry] at reached
  apply CPS1SameEventFunction.ammonia_at_of_live
    (.old (CPS1SameEventFunction.deformedNH3 event.physicalEvent.seed.translation.generatedFrame))
  · rw [show LiveStock event.reached = CPS1ReactiveField.liveStock initial from reached]
    exact held
  · rfl

@[irreducible] private def selected_first {frame : CPS1Recycling.Frame}
    {before : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} {events : List CPS1Recycling.RawEvent}
    {feed : List CPS1Recycling.RawMaterial} {physical : PhysicalRaw} {depth : Nat} {supply : ContinuationRaw}
    (first : NativeBiosyntheticEvent before water raw path events feed physical depth) :
    BiologicalDisposition before water raw path events feed physical depth supply → Prop
  | .originalResidual _ _ => True
  | .localUpdate _ found _ _ => found = first

private theorem repair_return_actual_first {frame : CPS1Recycling.Frame}
    {before : CPS1ReactiveNuclear.SourceCursor frame} {water : Nat} {raw : List RawSupply}
    {path : CPS1Recycling.SplitSite} {events : List CPS1Recycling.RawEvent}
    {feed : List CPS1Recycling.RawMaterial} {physical : PhysicalRaw} {depth : Nat}
    (whole : WholeRun before water raw path events feed physical depth) (supply : ContinuationRaw)
    (first : NativeBiosyntheticEvent before water raw path events feed physical depth)
    (firstActual : consumeWhole whole = .produced first)
    (receipt : LocalRepairReceipt (initialBody ⟨frame,before⟩))
    (selected : repairWhole whole supply = .repaired receipt) :
    ∃ update : RenewedBiosynthesis first supply,
      receipt.nextBody.current = ⟨update.returned.physicalEvent.seed.translation.generatedFrame,update.returned.reached⟩ := by
  unfold repairWhole classifyRepair at selected
  dsimp only at selected
  split at selected
  · rename_i successful
    have same := LocalRepairDisposition.repaired.inj selected
    subst receipt
    have returned : ∀ result : BiologicalDisposition before water raw path events feed physical depth supply,
        ∀ actual : result = classifyWhole whole supply,
          ResultSuccessful result →
          ∃ update : RenewedBiosynthesis first supply,
            (bodyWrite (initialBody ⟨frame,before⟩)
              ⟨⟨water,raw,path,events,feed,physical,depth,supply⟩,whole,result,actual⟩).current =
                ⟨update.returned.physicalEvent.seed.translation.generatedFrame,update.returned.reached⟩ := by
      intro result actual success
      have expected : selected_first first (classifyWhole whole supply) := by
        unfold classifyWhole
        split
        · simp only [selected_first]
        · rename_i found generated
          simp only [selected_first]
          exact BiosyntheticDisposition.produced.inj (generated.symm.trans firstActual)
      have firstSame : selected_first first result := Eq.mpr (congrArg (selected_first first) actual) expected
      cases result with
      | originalResidual original failed => cases success
      | localUpdate original found chosen next =>
        simp only [selected_first] at firstSame
        subst found
        cases next with
        | residual continuation failure => cases success
        | renewed update => exact ⟨update,rfl⟩
    exact returned _ rfl successful
  · cases selected

theorem registered_repaired_source_ready
    (receipt : LocalRepairReceipt (initialBody ⟨registeredFrame,registeredBefore⟩))
    (selected : repairWhole registeredWhole registeredSupply = .repaired receipt) :
    ∃ source : CPS1SameEventFunction.Classical.Source receipt.nextBody.current.2,
      CPS1SameEventFunction.Classical.sourceAt receipt.nextBody.current.2 = .ok source ∧
      source.owned.chainRows = [] := by
  obtain ⟨first,firstActual,_decoded,_remaining,_native,_birth,_read,ammonia⟩ := registered_complete_whole_birth
  obtain ⟨update,current⟩ := repair_return_actual_first registeredWhole registeredSupply first firstActual receipt selected
  have firstResources := CPS1SameEventFunction.ammonia_reader_resource_positive (returned_ammonia_from_native first ammonia)
  have nativeSource := CPS1SameEventFunction.returned_paid_source update.returned update.nextNative firstResources
  exact Eq.mpr (congrArg (fun point : SourcePoint =>
    ∃ source : CPS1SameEventFunction.Classical.Source point.2,
      CPS1SameEventFunction.Classical.sourceAt point.2 = .ok source ∧ source.owned.chainRows = []) current) nativeSource

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
