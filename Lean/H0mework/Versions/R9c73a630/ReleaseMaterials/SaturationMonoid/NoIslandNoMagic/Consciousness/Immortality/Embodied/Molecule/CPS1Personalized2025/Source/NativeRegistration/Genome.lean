import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Prefix

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1ResourceExecution CPS1BiologicalUpdate
attribute [local irreducible] registeredHandover registeredCaptured registeredOld

private theorem elongation_waste_dna (chain : Peptide) (tail : List AA) :
    (CPS1EndogenousTranslation.elongationWaste chain tail).filterMap nativeDNA? = [] := by
  induction tail generalizing chain with
  | nil => rfl
  | cons aa rest ih =>
    change (CPS1EndogenousTranslation.elongationWaste (chain.extend aa) rest ++
      CPS1EndogenousTranslation.cycleWaste chain).filterMap nativeDNA? = []
    rw [List.filterMap_append,ih]
    rfl

private theorem elongation_with_initiator_dna (tail : List AA) :
    (CPS1InitiationTermination.NativeComplete.elongationWasteWithInitiator tail).filterMap nativeDNA? = [] := by
  cases tail with
  | nil => rfl
  | cons aa rest =>
    change (CPS1EndogenousTranslation.elongationWaste (.M,[aa]) rest ++
      CPS1InitiationTermination.NativeComplete.firstCycleWaste).filterMap nativeDNA? = []
    rw [List.filterMap_append,elongation_waste_dna]
    rfl

private theorem charging_waste_dna (tail : List AA) :
    (CPS1InitiationTermination.NativeComplete.chargingWaste tail).filterMap nativeDNA? = [] := by
  induction tail with
  | nil => rfl
  | cons aa rest ih =>
    change (CPS1InitiationTermination.NativeComplete.chargingWaste rest).filterMap nativeDNA? = []
    exact ih

private theorem terminal_dna (tail : List AA) :
    nativeDNA? (CPS1InitiationTermination.NativeComplete.terminalComplex tail) = none := by
  cases tail <;> rfl

private theorem body_products_dna (tail : List AA) :
    (CPS1Reinitiation.Handover.bodyProducts tail).filterMap nativeDNA? = [] := by
  unfold CPS1Reinitiation.Handover.bodyProducts
  simp only [List.filterMap_append,elongation_with_initiator_dna,charging_waste_dna]
  have first : [Species.releasedPeptide (.M,tail),CPS1InitiationTermination.NativeComplete.terminalComplex tail].filterMap nativeDNA? = [] := by
    simp only [List.filterMap_cons,List.filterMap_nil,terminal_dna]
    rfl
  rw [first]
  rfl

private theorem remaining_waste_dna (tail : List AA) :
    (CPS1Recycling.ResidueSplit.remainingElongationWaste tail).filterMap nativeDNA? = [] := by
  cases tail with
  | nil => rfl
  | cons aa rest =>
    change (CPS1EndogenousTranslation.elongationWaste (.M,[aa]) rest ++
      [Species.gdp,.phosphate,.proton,.gdp,.phosphate,.proton]).filterMap nativeDNA? = []
    rw [List.filterMap_append,elongation_waste_dna]
    rfl

private theorem remaining_trna_dna (frame : CPS1Recycling.Frame) (trna : CPS1Recycling.Trna) :
    (CPS1Recycling.remainingTrna frame trna).filterMap recycledDNA? = [] := by
  cases trna <;> rfl

private theorem embedded_genome (frame : CPS1Recycling.Frame) (stock : Stock) :
    (stock.map (CPS1Reinitiation.NativeDictionary.embedded frame)).filterMap reinitiatedDNA? =
      stock.filterMap nativeDNA? := by
  rw [List.filterMap_map]
  rfl

private theorem old_genome (frame : CPS1Recycling.Frame) (stock : Stock) :
    (stock.map (CPS1Recycling.Species.old (frame := frame))).filterMap recycledDNA? =
      stock.filterMap nativeDNA? := by
  rw [List.filterMap_map]
  rfl

private theorem retained_genome (frame : CPS1Recycling.Frame) (stock : List (CPS1Recycling.Species frame)) :
    (stock.map CPS1Reinitiation.Species.retained).filterMap reinitiatedDNA? = stock.filterMap recycledDNA? := by
  rw [List.filterMap_map]
  rfl

private theorem historical_dna (frame : CPS1Recycling.Frame) :
    (CPS1Reinitiation.Handover.Source.historicalPassive frame).filterMap recycledDNA? = [] := by
  unfold CPS1Reinitiation.Handover.Source.historicalPassive
  simp only [List.filterMap_append,remaining_trna_dna,old_genome,remaining_waste_dna,charging_waste_dna]
  rfl

private theorem handover_products_genome (frame : CPS1Recycling.Frame) (tail : List AA) (rna : RegisteredRna) :
    ((CPS1Reinitiation.Handover.bodyProducts tail).map (CPS1Reinitiation.NativeDictionary.embedded frame) ++
      CPS1Reinitiation.Handover.joinPassive frame rna ++
      CPS1Reinitiation.Handover.Source.surplus frame [] [] []).filterMap reinitiatedDNA? = [] := by
  simp only [List.filterMap_append,embedded_genome,body_products_dna,List.nil_append]
  unfold CPS1Reinitiation.Handover.joinPassive CPS1Reinitiation.Handover.Source.surplus
  simp only [List.map_nil,List.append_nil,List.filterMap_append,retained_genome,historical_dna]
  simp only [CPS1Reinitiation.workProducts,List.filterMap_append,List.filterMap_replicate]
  rfl

private theorem canonical_handover_genome (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite) :
    let frame := CPS1Recycling.Source.frame edits water additional
    let recycled := CPS1Recycling.run frame (CPS1Recycling.productiveEvents path) CPS1Recycling.freshFuel
    let scanning := CPS1Reinitiation.run frame recycled path.after Molecules.mrna (CPS1Reinitiation.rawFuel 151)
    let result := CPS1Reinitiation.Handover.execute frame
      (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna 151 Program.originalPeptide.2)
      (scanning.stock ++ (CPS1Reinitiation.Handover.rawFuel Program.originalPeptide.2).map
        (CPS1Reinitiation.Handover.RawMaterial.species frame))
    result.stock.filterMap (reinitiatedDNA? (frame := frame)) = [] := by
  dsimp only
  have generated := CPS1Reinitiation.Handover.Source.native_complete edits water additional path
    CPS1Recycling.freshFuel [] (by simp only [List.append_nil]; rfl)
    (CPS1Reinitiation.rawFuel 151) [] (by simp only [List.append_nil]; rfl)
    (CPS1Reinitiation.Handover.rawFuel Program.originalPeptide.2) [] (by simp only [List.append_nil]; rfl)
  have selected := generated.2.2.2.filterMap (reinitiatedDNA? (frame := CPS1Recycling.Source.frame edits water additional))
  rw [handover_products_genome] at selected
  exact List.perm_nil.mp selected

theorem registered_handover_genome : registeredHandover.stock.filterMap reinitiatedDNA? = [] := by
  let property (frame : CPS1Recycling.Frame) : Prop :=
    (CPS1Reinitiation.Handover.execute frame
      (CPS1Reinitiation.Handover.fullProgram registeredPath Molecules.mrna 151 Program.originalPeptide.2)
      ((CPS1Reinitiation.run frame (CPS1Recycling.run frame (CPS1Recycling.productiveEvents registeredPath)
        CPS1Recycling.freshFuel) registeredPath.after Molecules.mrna (CPS1Reinitiation.rawFuel 151)).stock ++
        (CPS1Reinitiation.Handover.rawFuel Program.originalPeptide.2).map
          (CPS1Reinitiation.Handover.RawMaterial.species frame))).stock.filterMap (reinitiatedDNA? (frame := frame)) = []
  have canonical : property (CPS1Recycling.Source.frame registeredEdits registeredWater registeredAdditional) :=
    canonical_handover_genome registeredEdits registeredWater registeredAdditional registeredPath
  have same : CPS1Recycling.Source.frame registeredEdits registeredWater registeredAdditional = registeredFrame := rfl
  have closed : property registeredFrame := Eq.mp (congrArg property same) canonical
  simpa only [property,registeredHandover,registeredScanning,registeredRecycled,
    registeredRecycleFeed,registeredScanFeed,registeredBodyFeed] using closed

private theorem captured_depth_zero_genome (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (stock : CPS1Reinitiation.Stock frame) :
    (CPS1LocalChemicalExecution.Source.fromCurrent frame
      (CPS1StockRecursion.Source.requested frame path 0 stock)).current.stock.filterMap localDNA? =
      stock.filterMap reinitiatedDNA? := by
  simpa only [CPS1StockRecursion.Source.requested,List.replicate_zero,
    CPS1StockRecursion.Source.observe,CPS1StockRecursion.Source.start] using
    captured_source_genome (CPS1StockRecursion.Source.requested frame path 0 stock)

theorem registered_capture_genome : registeredCaptured.current.stock.filterMap localDNA? = [] := by
  have preserved := captured_depth_zero_genome registeredFrame registeredPath registeredHandover.stock
  simpa only [registeredCaptured,registeredObserved,registeredDepth] using preserved.trans registered_handover_genome

def registeredDNA := CPS1Deamination.ExecutionReadout.prefixWord CPS1Deamination.Source.originalMinusAligned
  ((CPS1Deamination.Source.sourceProgram registeredEdits).steps.take (registeredWater+registeredAdditional))

private theorem working_genome (word : DNA) (paid water : Nat) :
    (CPS1Deamination.ExecutionReadout.workingStock word paid water).filterMap nativeDNA? = [word] := by
  simp [CPS1Deamination.ExecutionReadout.workingStock,nativeDNA?]

private theorem continued_genome (edits : Target.Edits) (water additional : Nat) :
    (CPS1Deamination.Continuation.sourceContinuation edits water additional).stock.filterMap nativeDNA? =
      [CPS1Deamination.ExecutionReadout.prefixWord CPS1Deamination.Source.originalMinusAligned
        ((CPS1Deamination.Source.sourceProgram edits).steps.take (water+additional))] := by
  have projected := congrArg (List.filterMap nativeDNA?)
    (CPS1Deamination.Continuation.source_continuation_update edits water additional).2.2.1
  exact projected.trans (working_genome _ _ _)

private theorem source_after_capture_initial_genome (frame : CPS1Recycling.Frame)
    (captured : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (edits : Target.Edits) (water additional : Nat) (actions : List CPS1EnzymeBath.Source.RawAction)
    (empty : captured.current.stock.filterMap localDNA? = []) :
    (sourceAfterCapture frame captured edits water additional actions).current.stock.filterMap deformedDNA? =
      [CPS1Deamination.ExecutionReadout.prefixWord CPS1Deamination.Source.originalMinusAligned
        ((CPS1Deamination.Source.sourceProgram edits).steps.take (water+additional))] := by
  have preserved := source_after_capture_genome frame captured edits water additional actions
  have first := congrArg (fun words => words ++
    (CPS1Deamination.Continuation.sourceContinuation edits water additional).stock.filterMap nativeDNA?) empty
  exact preserved.trans (first.trans ((List.nil_append _).trans (continued_genome edits water additional)))

theorem registered_old_genome : registeredOld.current.stock.filterMap deformedDNA? = [registeredDNA] := by
  simpa only [registeredOld,registeredDNA] using source_after_capture_initial_genome
    registeredFrame registeredCaptured registeredEdits registeredWater registeredAdditional registeredBathActions registered_capture_genome

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
