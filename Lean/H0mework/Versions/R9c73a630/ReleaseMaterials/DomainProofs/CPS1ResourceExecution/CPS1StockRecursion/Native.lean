import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1StockRecursion.Stock
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1StockRecursion.RecyclingLift

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1StockRecursion
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
open Dictionary

namespace Native

def recycleInput (frame : CPS1Recycling.Frame) (tail : List AA) : Dictionary.Stock frame :=
  let trna := terminalTrna tail
  [.retained (.abce1 CPS1Reinitiation.Handover.dischargedSites),old frame .atp,old frame .atp,
    old frame (CPS1Recycling.postSpecies trna),.rna Molecules.mrna] ++
    ((RecyclingLift.afterBindingInput frame trna).tail).map (RecyclingLift.encode frame)

def recycleProducts (frame : CPS1Recycling.Frame) (tail : List AA)
    (path : CPS1Recycling.SplitSite) : Dictionary.Stock frame :=
  (CPS1Recycling.coreProducts frame (terminalTrna tail) path).map (RecyclingLift.encode frame) ++
    [.retained .adp,.retained .adp]

theorem execute_cons (frame : CPS1Recycling.Frame) (reaction : Dictionary.Reaction)
    (rest : List Dictionary.Reaction) (stock : Dictionary.Stock frame) :
    Dictionary.execute frame (reaction :: rest) stock =
      match Inventory.fire (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame) reaction stock with
      | .error missing => ⟨[],reaction::rest,stock,some missing⟩
      | .ok next =>
        let after := Dictionary.execute frame rest next
        ⟨reaction::after.fired,after.remaining,after.stock,after.missing⟩ := by
  unfold Dictionary.execute
  rw [Inventory.execute_cons]
  cases Inventory.fire (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame) reaction stock <;> rfl

theorem execute_append_paid (frame : CPS1Recycling.Frame) (first rest : List Dictionary.Reaction)
    (stock : Dictionary.Stock frame) (paid : (Dictionary.execute frame first stock).remaining = [])
    (complete : (Dictionary.execute frame first stock).missing = none) :
    Dictionary.execute frame (first ++ rest) stock =
      let previous := Dictionary.execute frame first stock
      let after := Dictionary.execute frame rest previous.stock
      ⟨previous.fired ++ after.fired,after.remaining,after.stock,after.missing⟩ := by
  induction first generalizing stock with
  | nil => rfl
  | cons reaction first ih =>
    cases action : Inventory.fire (Dictionary.Reaction.reactants frame)
        (Dictionary.Reaction.products frame) reaction stock with
    | error missing =>
      simp only [execute_cons,action] at complete
      contradiction
    | ok next =>
      simp only [execute_cons,action] at paid complete ⊢
      simp only [List.cons_append,execute_cons,action]
      rw [ih next paid complete]

/-- Both exchange events consume actual ATP and return the two previous ADPs.
The paired RNA is reserved together with the new coarse postTC at binding. -/
theorem recycle_complete (frame : CPS1Recycling.Frame) (tail : List AA)
    (path : CPS1Recycling.SplitSite) (surplus stock : Dictionary.Stock frame)
    (inventory : stock.Perm (recycleInput frame tail ++ surplus)) :
    let result := Dictionary.execute frame (recycleProgram tail path) stock
    result.fired = recycleProgram tail path ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm (recycleProducts frame tail path ++ surplus) := by
  let trna := terminalTrna tail
  let remaining : Dictionary.Stock frame :=
    ((RecyclingLift.afterBindingInput frame trna).tail).map (RecyclingLift.encode frame)
  let rest1 : Dictionary.Stock frame := [old frame .atp,old frame (CPS1Recycling.postSpecies trna),
    .rna Molecules.mrna] ++ remaining ++ surplus
  have inv1 : stock.Perm (Dictionary.Reaction.exchangeFirst.reactants frame ++ rest1) := by
    simpa only [recycleInput,Dictionary.Reaction.reactants,trna,remaining,rest1,List.append_assoc,
      List.cons_append,List.nil_append] using inventory
  rcases Inventory.fire_available (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame)
    .exchangeFirst rest1 stock inv1 with ⟨first,paid1,firstInventory⟩
  let rest2 : Dictionary.Stock frame := [old frame (CPS1Recycling.postSpecies trna),.rna Molecules.mrna,
    .retained .adp] ++ remaining ++ surplus
  have inv2 : first.Perm (Dictionary.Reaction.exchangeSecond.reactants frame ++ rest2) := by
    apply firstInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Dictionary.Reaction.reactants,Dictionary.Reaction.products,rest1,rest2,
      List.count_append,List.count_cons,List.count_nil]
    omega
  rcases Inventory.fire_available (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame)
    .exchangeSecond rest2 first inv2 with ⟨second,paid2,secondInventory⟩
  let rest3 : Dictionary.Stock frame := [.retained .adp,.retained .adp] ++ remaining ++ surplus
  have inv3 : second.Perm ((Dictionary.Reaction.bind trna).reactants frame ++ rest3) := by
    apply secondInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Dictionary.Reaction.reactants,Dictionary.Reaction.products,rest2,rest3,
      List.count_append,List.count_cons,List.count_nil]
    omega
  rcases Inventory.fire_available (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame)
    (.bind trna) rest3 second inv3 with ⟨bound,paid3,boundInventory⟩
  have boundInput : bound.Perm ((RecyclingLift.afterBindingInput frame trna).map
      (RecyclingLift.encode frame) ++ ([.retained .adp,.retained .adp] ++ surplus)) := by
    apply boundInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [RecyclingLift.afterBindingInput,RecyclingLift.encode,Dictionary.Reaction.products,
      remaining,rest3,List.cons_append,List.nil_append,List.tail_cons,List.map_cons,List.map_nil,List.map_append,
      List.count_append,List.count_cons,List.count_nil]
    omega
  have later := RecyclingLift.dictionary_after_binding_complete frame trna path
    ([.retained .adp,.retained .adp] ++ surplus) bound boundInput
  let finished := Dictionary.execute frame (RecyclingLift.afterBindingProgram trna path) bound
  have totalExecution : Dictionary.execute frame (recycleProgram tail path) stock =
      ⟨.exchangeFirst :: .exchangeSecond :: .bind trna :: finished.fired,
        finished.remaining,finished.stock,finished.missing⟩ := by
    change Dictionary.execute frame
      (.exchangeFirst :: .exchangeSecond :: .bind trna :: RecyclingLift.afterBindingProgram trna path) stock = _
    rw [execute_cons,paid1]
    dsimp only
    rw [execute_cons,paid2]
    dsimp only
    rw [execute_cons,paid3]
  dsimp only
  rw [totalExecution]
  refine ⟨congrArg (fun trace => Dictionary.Reaction.exchangeFirst :: .exchangeSecond :: .bind trna :: trace) later.1,
    later.2.1,later.2.2.1,?_⟩
  simpa only [recycleProducts,trna,List.append_assoc] using later.2.2.2

/-- Relabel only reactions, keeping the actual stock and reservation unchanged. -/
theorem execute_scan (frame : CPS1Recycling.Frame) (program : List CPS1Reinitiation.Primitive)
    (stock : Dictionary.Stock frame) :
    Dictionary.execute frame (program.map Dictionary.Reaction.scan) stock =
      let original := CPS1Reinitiation.execute frame program stock
      ⟨original.fired.map Dictionary.Reaction.scan,original.remaining.map Dictionary.Reaction.scan,
        original.stock,original.missing⟩ := by
  induction program generalizing stock with
  | nil => rfl
  | cons primitive rest ih =>
    rw [List.map_cons,execute_cons,CPS1Reinitiation.execute_cons]
    have sameFire : Inventory.fire (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame)
        (.scan primitive) stock = Inventory.fire (CPS1Reinitiation.Primitive.reactants frame)
          (CPS1Reinitiation.Primitive.products frame) primitive stock := rfl
    rw [sameFire]
    cases action : Inventory.fire (CPS1Reinitiation.Primitive.reactants frame)
        (CPS1Reinitiation.Primitive.products frame) primitive stock with
    | error missing => rfl
    | ok next =>
      dsimp only
      rw [ih]
      rfl

theorem execute_body (frame : CPS1Recycling.Frame) (program : List CPS1Reinitiation.Handover.Reaction)
    (stock : Dictionary.Stock frame) :
    Dictionary.execute frame (program.map Dictionary.Reaction.body) stock =
      let original := CPS1Reinitiation.Handover.execute frame program stock
      ⟨original.fired.map Dictionary.Reaction.body,original.remaining.map Dictionary.Reaction.body,
        original.stock,original.missing⟩ := by
  induction program generalizing stock with
  | nil => rfl
  | cons primitive rest ih =>
    rw [List.map_cons,execute_cons,CPS1Reinitiation.Handover.execute_cons]
    have sameFire : Inventory.fire (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame)
        (.body primitive) stock = Inventory.fire (CPS1Reinitiation.Handover.Reaction.reactants frame)
          (CPS1Reinitiation.Handover.Reaction.products frame) primitive stock := rfl
    rw [sameFire]
    cases action : Inventory.fire (CPS1Reinitiation.Handover.Reaction.reactants frame)
        (CPS1Reinitiation.Handover.Reaction.products frame) primitive stock with
    | error missing => rfl
    | ok next =>
      dsimp only
      rw [ih]
      rfl

def bodyTrnas (tail : List AA) : CPS1ResourceExecution.Stock :=
  match tail with
  | [] => []
  | _ :: _ => (tail.map CPS1ResourceExecution.Species.tRNA).erase (.tRNA (Peptide.last (.M,tail)))

theorem before_binding_trnas (frame : CPS1Recycling.Frame) (tail : List AA) :
    (freeTrnas tail).map (old frame) =
      (CPS1Recycling.beforeInitiator frame (terminalTrna tail)).map (RecyclingLift.encode frame) ++
        (bodyTrnas tail).map (old frame) := by
  cases tail <;> rfl

theorem after_binding_trnas (frame : CPS1Recycling.Frame) (tail : List AA) :
    ((CPS1Recycling.remainingTrna frame (terminalTrna tail)).map (RecyclingLift.encode frame) ++
      (bodyTrnas tail).map (old frame)).Perm ((tail.map CPS1ResourceExecution.Species.tRNA).map (old frame)) := by
  cases tail with
  | nil => rfl
  | cons aa rest =>
    have paired := (after_return_trnas (aa::rest)).map (old frame)
    apply List.perm_iff_count.mpr
    intro species
    have counted := paired.count_eq species
    simp only [freeTrnas,terminalTrna,CPS1Recycling.returnedTrna,Dictionary.old,
      List.map_append,List.map_cons,List.map_nil,List.count_append,List.count_cons,List.count_nil] at counted
    simp only [CPS1Recycling.remainingTrna,terminalTrna,bodyTrnas,RecyclingLift.encode,Dictionary.old,
      List.map_cons,List.map_nil,List.count_append,List.count_cons,List.count_nil]
    omega

def chargingAtoms (tail : List AA) : CPS1ResourceExecution.Stock :=
  tail.flatMap (fun aa => [.freeAA aa,.atp])

theorem charging_atoms_trnas (tail : List AA) :
    (chargingAtoms tail ++ tail.map CPS1ResourceExecution.Species.tRNA).Perm
      (CPS1EndogenousTranslation.chargingFuel tail) := by
  induction tail with
  | nil => rfl
  | cons aa rest ih =>
    apply List.perm_iff_count.mpr
    intro species
    have counted := ih.count_eq species
    simp only [chargingAtoms,CPS1EndogenousTranslation.chargingFuel,
      CPS1ResourceExecution.Reaction.reactants,List.flatMap_cons,List.map_cons,
      List.count_append,List.count_cons,List.count_nil] at counted ⊢
    omega

theorem raw_body_inventory (frame : CPS1Recycling.Frame) (tail : List AA) :
    (bodyRawFuel tail).map (RawMaterial.species frame) =
      (([.gtp,.water,.water] ++ chargingAtoms tail ++
        CPS1InitiationTermination.NativeComplete.energyFuel tail ++ [.gtp,.water,.water]) :
          CPS1ResourceExecution.Stock).map (old frame) := by
  simp only [bodyRawFuel,chargingAtoms,CPS1InitiationTermination.NativeComplete.energyFuel,
    List.map_append,List.map_flatMap,List.map_cons,List.map_nil,RawMaterial.species]

def recycleSurplus (frame : CPS1Recycling.Frame) (tail : List AA) : Dictionary.Stock frame :=
  (factorStock [.eIF5,.eIF5B,.eRF3]).map (old frame) ++ recruitment frame ++
    (bodyTrnas tail).map (old frame) ++
    List.replicate 151 (old frame .atp) ++ List.replicate 152 (old frame .water) ++
    (bodyRawFuel tail).map (RawMaterial.species frame)

theorem actual_recycle_inventory (frame : CPS1Recycling.Frame) (tail : List AA) :
    (reusable frame tail ++ (rawFuel tail).map (RawMaterial.species frame)).Perm
      (recycleInput frame tail ++ recycleSurplus frame tail) := by
  apply List.perm_iff_count.mpr
  intro species
  have trnas := congrArg (List.count species) (before_binding_trnas frame tail)
  simp only [List.count_append] at trnas
  simp only [reusable,recycleInput,recycleSurplus,actors,recruitment,rawFuel,RawMaterial.species,
    RecyclingLift.afterBindingInput,RecyclingLift.encode,old,factorStock,
    List.cons_append,List.nil_append,List.tail_cons,List.map_append,List.map_cons,List.map_nil,List.map_replicate,
    List.count_append,List.count_cons,List.count_nil] at trnas ⊢
  rw [terminal_trna_actual]
  omega

def scanSurplus (frame : CPS1Recycling.Frame) (tail : List AA) : Dictionary.Stock frame :=
  [old frame .subunit60,old frame (.actor .eRF1),old frame .phosphate,old frame .proton,
    old frame .amp,old frame .ppi,old frame (.actor .metRS),old frame (.actor .eIF5B),
    old frame (.actor .eRF3),.retained .adp,.retained .adp] ++
    (tail.map CPS1ResourceExecution.Species.tRNA).map (old frame) ++
    (bodyRawFuel tail).map (RawMaterial.species frame)

theorem recycled_scan_inventory (frame : CPS1Recycling.Frame) (tail : List AA)
    (path : CPS1Recycling.SplitSite) :
    (recycleProducts frame tail path ++ recycleSurplus frame tail).Perm
      (CPS1Reinitiation.scanInput frame path.after Molecules.mrna 151 ++ scanSurplus frame tail) := by
  apply List.perm_iff_count.mpr
  intro species
  have trnas := (after_binding_trnas frame tail).count_eq species
  simp only [List.count_append] at trnas
  simp only [recycleProducts,recycleSurplus,CPS1Recycling.coreProducts,RecyclingLift.encode,
    CPS1Reinitiation.scanInput,scanSurplus,recruitment,old,factorStock,
    List.map_append,List.map_cons,List.map_nil,List.count_append,List.count_cons,List.count_nil] at trnas ⊢
  simp only [Nat.reduceAdd]
  omega

def bodySurplus (frame : CPS1Recycling.Frame) : Dictionary.Stock frame :=
  [.retained .eIF3j,old frame (.actor .eIF1),old frame .phosphate,old frame .proton] ++
    CPS1Reinitiation.workProducts frame 151 ++
    [old frame .phosphate,old frame .proton,old frame .amp,old frame .ppi,old frame (.actor .metRS),
      .retained .adp,.retained .adp]

theorem scanned_body_inventory (frame : CPS1Recycling.Frame) (tail : List AA)
    (path : CPS1Recycling.SplitSite) :
    (CPS1Reinitiation.scanProducts frame path.after Molecules.mrna 151 ++ scanSurplus frame tail).Perm
      (CPS1Reinitiation.Handover.input frame path Molecules.mrna 151 ++
        (CPS1Reinitiation.Handover.bodyFuel tail).map (old frame) ++ bodySurplus frame) := by
  apply List.perm_iff_count.mpr
  intro species
  have trnas := ((charging_atoms_trnas tail).map (old frame)).count_eq species
  simp only [List.map_append,List.count_append] at trnas
  simp only [scanSurplus]
  rw [raw_body_inventory]
  simp only [CPS1Reinitiation.scanProducts,CPS1Reinitiation.Handover.input,
    CPS1Reinitiation.Handover.bodyFuel,bodySurplus,CPS1Reinitiation.NativeDictionary.embedded,old,
    List.map_append,List.map_cons,List.map_nil,List.count_append,List.count_cons,List.count_nil] at trnas ⊢
  omega

def cycleWaste (frame : CPS1Recycling.Frame) (tail : List AA) : Dictionary.Stock frame :=
  ([.releasedPeptide (.M,tail)] ++ currencyWaste tail ++
    CPS1InitiationTermination.NativeComplete.chargingWaste tail ++
    [.gdp,.phosphate,.proton,.gdp,.phosphate,.proton,.gdp,.phosphate,.proton,
      .phosphate,.proton,.phosphate,.proton,.amp,.ppi] : CPS1ResourceExecution.Stock).map (old frame) ++
    CPS1Reinitiation.workProducts frame 151 ++ [.retained .adp,.retained .adp]

theorem complete_reusable_inventory (frame : CPS1Recycling.Frame) (tail : List AA) :
    ((CPS1Reinitiation.Handover.bodyProducts tail).map (old frame) ++
      CPS1Reinitiation.Handover.joinPassive frame Molecules.mrna ++ bodySurplus frame).Perm
      (reusable frame tail ++ cycleWaste frame tail) := by
  apply List.perm_iff_count.mpr
  intro species
  have trnas := ((free_trnas_partition tail).map (old frame)).count_eq species
  simp only [List.map_append,List.count_append] at trnas
  simp only [CPS1Reinitiation.Handover.bodyProducts,CPS1Reinitiation.Handover.joinPassive,
    CPS1Reinitiation.Handover.retainedAfterJoin,CPS1Reinitiation.Handover.dischargedSites,
    CPS1InitiationTermination.NativeComplete.terminationWaste,bodySurplus,reusable,cycleWaste,
    actors,recruitment,CPS1Reinitiation.NativeDictionary.embedded,old,factorStock,
    List.map_append,List.map_cons,List.map_nil,List.count_append,List.count_cons,List.count_nil] at trnas ⊢
  omega

/-- Actual postTC/RNA/ABCE1-DD and returned actors and fine tRNAs pay the next complete cycle.
Fresh supply contains only amino acids and nucleotides/water, retaining all old surplus. -/
theorem cycle_complete (frame : CPS1Recycling.Frame) (tail : List AA)
    (path : CPS1Recycling.SplitSite) (surplus stock : Dictionary.Stock frame)
    (inventory : stock.Perm (reusable frame tail ++ (rawFuel tail).map (RawMaterial.species frame) ++ surplus)) :
    let result := Dictionary.execute frame (Dictionary.program tail path) stock
    result.fired = Dictionary.program tail path ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm (reusable frame tail ++ cycleWaste frame tail ++ surplus) := by
  have recyclingInput := inventory.trans ((actual_recycle_inventory frame tail).append_right surplus)
  have recycled := recycle_complete frame tail path (recycleSurplus frame tail ++ surplus) stock
    (by simpa only [List.append_assoc] using recyclingInput)
  let previous := Dictionary.execute frame (recycleProgram tail path) stock
  have scanningInput : previous.stock.Perm
      (CPS1Reinitiation.scanInput frame path.after Molecules.mrna 151 ++ (scanSurplus frame tail ++ surplus)) := by
    apply recycled.2.2.2.trans
    simpa only [List.append_assoc] using (recycled_scan_inventory frame tail path).append_right surplus
  have scanned := CPS1Reinitiation.native_scan_complete frame path.after Molecules.mrna 151
    CPS1Reinitiation.Source.original_start_and_context.1 CPS1Reinitiation.Source.original_start_and_context.2
    (scanSurplus frame tail ++ surplus) previous.stock scanningInput
  let afterScan := CPS1Reinitiation.execute frame (CPS1Reinitiation.scanProgram path.after Molecules.mrna) previous.stock
  have handoverInput : afterScan.stock.Perm
      (CPS1Reinitiation.Handover.input frame path Molecules.mrna 151 ++
        (CPS1Reinitiation.Handover.bodyFuel tail).map (CPS1Reinitiation.NativeDictionary.embedded frame) ++
          (bodySurplus frame ++ surplus)) := by
    apply scanned.2.2.2.trans
    change (CPS1Reinitiation.scanProducts frame path.after Molecules.mrna 151 ++
      (scanSurplus frame tail ++ surplus)).Perm
        (CPS1Reinitiation.Handover.input frame path Molecules.mrna 151 ++
          (CPS1Reinitiation.Handover.bodyFuel tail).map (old frame) ++ (bodySurplus frame ++ surplus))
    simpa only [List.append_assoc] using (scanned_body_inventory frame tail path).append_right surplus
  have ended := CPS1Reinitiation.Handover.native_full_complete frame path Molecules.mrna 151 tail
    (bodySurplus frame ++ surplus) afterScan.stock handoverInput
  have scanPaid : (Dictionary.execute frame
      ((CPS1Reinitiation.scanProgram path.after Molecules.mrna).map Dictionary.Reaction.scan) previous.stock).remaining = [] := by
    rw [execute_scan]
    dsimp only
    rw [scanned.2.1]
    rfl
  have scanDone : (Dictionary.execute frame
      ((CPS1Reinitiation.scanProgram path.after Molecules.mrna).map Dictionary.Reaction.scan) previous.stock).missing = none := by
    rw [execute_scan]; exact scanned.2.2.1
  have totalExecution : Dictionary.execute frame (Dictionary.program tail path) stock =
      ⟨previous.fired ++ afterScan.fired.map Dictionary.Reaction.scan ++
          (CPS1Reinitiation.Handover.execute frame
            (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna 151 tail) afterScan.stock).fired.map Dictionary.Reaction.body,
        (CPS1Reinitiation.Handover.execute frame
          (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna 151 tail) afterScan.stock).remaining.map Dictionary.Reaction.body,
        (CPS1Reinitiation.Handover.execute frame
          (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna 151 tail) afterScan.stock).stock,
        (CPS1Reinitiation.Handover.execute frame
          (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna 151 tail) afterScan.stock).missing⟩ := by
    unfold Dictionary.program
    rw [List.append_assoc,execute_append_paid frame _ _ stock recycled.2.1 recycled.2.2.1]
    dsimp only
    rw [execute_append_paid frame _ _ previous.stock scanPaid scanDone,execute_scan]
    dsimp only
    rw [execute_body]
    simp only [previous,afterScan,List.append_assoc]
  dsimp only
  rw [totalExecution]
  refine ⟨?_,?_,ended.2.2.1,?_⟩
  · have firstFired : previous.fired = recycleProgram tail path := recycled.1
    have scanFired : afterScan.fired = CPS1Reinitiation.scanProgram path.after Molecules.mrna := scanned.1
    rw [firstFired,scanFired,ended.1]
    rfl
  · rw [ended.2.1]; rfl
  · apply ended.2.2.2.trans
    change ((CPS1Reinitiation.Handover.bodyProducts tail).map (old frame) ++
      CPS1Reinitiation.Handover.joinPassive frame Molecules.mrna ++ (bodySurplus frame ++ surplus)).Perm _
    simpa only [List.append_assoc] using (complete_reusable_inventory frame tail).append_right surplus

end Native
end CPS1StockRecursion
