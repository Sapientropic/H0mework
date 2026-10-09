import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EndogenousTranslation.Program
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1InitiationTermination.Accounting
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1InitiationTermination.UnifiedBoundary

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1InitiationTermination.NativeComplete
open CPS1ResourceExecution CPS1EndogenousTranslation

def actors : Stock :=
  factorStock [.metRS,.eIF1,.eIF1A,.eIF2,.eIF3,.eIF5,.eIF5B,.eRF1,.eRF3]

def returnedActors : Stock :=
  factorStock [.metRS,.eIF1,.eIF1A,.eIF2,.eIF3,.eIF5,.eIF5B,.eRF3]

def chargingWaste (tail : List AA) : Stock := tail.flatMap (fun _ => [Species.amp,Species.ppi])
def energyFuel (tail : List AA) : Stock :=
  tail.flatMap (fun _ => [Species.gtp,Species.water,Species.gtp,Species.water])

/-- Every ingredient is raw: no PIC, loaded tRNA, nascent chain, or release certificate. -/
def rawFuel (tail : List AA) : Stock :=
  [.freeAA .M,.initiatorTRNA,.atp] ++ chargingFuel tail ++
    [Species.subunit40,Species.subunit60] ++ actors ++ [Species.gtp,Species.water,Species.gtp,Species.water] ++
    energyFuel tail ++ [Species.gtp,Species.water,Species.water]

theorem execute_append_paid (paidBlock rest : List Reaction) (stock : Stock)
    (paid : (execute paidBlock stock).remaining = [])
    (complete : (execute paidBlock stock).missing = none) :
    execute (paidBlock ++ rest) stock =
      let after := execute rest (execute paidBlock stock).stock
      ⟨(execute paidBlock stock).fired ++ after.fired,after.remaining,after.stock,after.missing⟩ := by
  induction paidBlock generalizing stock with
  | nil => rfl
  | cons reaction paidBlock ih =>
    cases action : fire reaction stock with
    | error missing =>
      simp only [CPS1Deamination.ExecutionReadout.execute_cons,action] at complete
      contradiction
    | ok next =>
      simp only [CPS1Deamination.ExecutionReadout.execute_cons,action] at paid complete ⊢
      simp only [List.cons_append,CPS1Deamination.ExecutionReadout.execute_cons,action]
      rw [ih next paid complete]
      simp only [Execution.fired,Execution.remaining,Execution.stock,Execution.missing,List.cons_append]

theorem charging_products_split (tail : List AA) :
    (chargingProducts tail).Perm (tail.map Species.aaTRNA ++ chargingWaste tail) := by
  apply (List.reverse_perm tail).flatMap_right (fun aa => (Reaction.charge aa).products) |>.trans
  simpa only [chargingProducts,Reaction.products,chargingWaste] using
    (List.map_append_flatMap_perm tail Species.aaTRNA (fun _ => [Species.amp,Species.ppi])).symm

theorem charged_energy_split (tail : List AA) :
    (tail.map Species.aaTRNA ++ energyFuel tail).Perm (elongationFuel tail) := by
  exact List.map_append_flatMap_perm tail Species.aaTRNA (fun _ => [Species.gtp,Species.water,Species.gtp,Species.water])

def initializationWaste : Stock :=
  [Species.amp,Species.ppi,.gdp,.phosphate,.proton,.gdp,.phosphate,.proton]

def terminationFuel : Stock := [.ribosome80,Species.gtp,Species.water,.actor .eRF1,.actor .eRF3,Species.water]

def initializationRemainder : Stock :=
  [.ribosome80] ++ initializationWaste ++ actors

theorem native_initiator_charge_load (surplus stock : Stock)
    (inventory : stock.Perm
      ([.freeAA .M,.initiatorTRNA,.atp,Species.subunit40,Species.subunit60] ++ actors ++
        [Species.gtp,Species.water,Species.gtp,Species.water] ++ surplus)) :
    ∃ charged captured joined,
      fire .chargeInitiator stock = .ok charged ∧
      fire .captureInitiator charged = .ok captured ∧
      fire .joinSubunit captured = .ok joined ∧
      joined.Perm (.initiatorPSite :: initializationRemainder ++ surplus) := by
  have firstInventory : stock.Perm
      (Reaction.chargeInitiator.reactants ++
        ([Species.subunit40,Species.subunit60] ++
          factorStock [.eIF1,.eIF1A,.eIF2,.eIF3,.eIF5,.eIF5B,.eRF1,.eRF3] ++
          [Species.gtp,Species.water,Species.gtp,Species.water] ++ surplus)) := by
    apply inventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Reaction.reactants,actors,factorStock,List.map_cons,List.map_nil,
      List.count_cons,List.count_append,List.count_nil,List.append_assoc]
    omega
  rcases fire_available .chargeInitiator _ stock firstInventory with
    ⟨charged,first,chargedInventory⟩
  have secondInventory : charged.Perm
      (Reaction.captureInitiator.reactants ++
        ([Species.subunit60,Species.gtp,Species.water,Species.amp,Species.ppi,.actor .metRS,.actor .eIF5B,.actor .eRF1,.actor .eRF3] ++ surplus)) := by
    apply chargedInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Reaction.reactants,Reaction.products,factorStock,List.map_cons,List.map_nil,
      List.count_cons,List.count_append,List.count_nil,List.append_assoc]
    omega
  rcases fire_available .captureInitiator _ charged secondInventory with
    ⟨captured,second,capturedInventory⟩
  have thirdInventory : captured.Perm
      (Reaction.joinSubunit.reactants ++
        ([Species.amp,Species.ppi,.actor .metRS,.gdp,.phosphate,.proton,.actor .eIF1,.actor .eIF2,
          .actor .eIF3,.actor .eIF5,.actor .eRF1,.actor .eRF3] ++ surplus)) := by
    apply capturedInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Reaction.reactants,Reaction.products,factorStock,List.map_cons,List.map_nil,
      List.count_cons,List.count_append,List.count_nil,List.append_assoc]
    omega
  rcases fire_available .joinSubunit _ captured thirdInventory with
    ⟨joined,third,joinedInventory⟩
  refine ⟨charged,captured,joined,first,second,third,joinedInventory.trans ?_⟩
  apply List.perm_iff_count.mpr
  intro species
  simp only [Reaction.products,initializationRemainder,initializationWaste,actors,factorStock,
    List.map_cons,List.map_nil,List.count_cons,List.count_append,List.count_nil,List.append_assoc]
  omega

def firstCycleWaste : Stock :=
  [.initiatorTRNA,.gdp,.phosphate,.proton,.gdp,.phosphate,.proton]

theorem native_first_cycle (aa : AA) (surplus stock : Stock)
    (inventory : stock.Perm
      (.initiatorPSite :: [.aaTRNA aa,Species.gtp,Species.water,Species.gtp,Species.water] ++ surplus)) :
    ∃ delivered transferred moved,
      fire (.deliverInitiator aa) stock = .ok delivered ∧
      fire (.transferInitiator aa) delivered = .ok transferred ∧
      fire (.translocateInitiator aa) transferred = .ok moved ∧
      moved.Perm (.peptidyl (.M,[aa]) :: firstCycleWaste ++ surplus) := by
  rcases fire_available (.deliverInitiator aa) ([Species.gtp,Species.water] ++ surplus) stock inventory with
    ⟨delivered,first,deliveredInventory⟩
  rcases fire_available (.transferInitiator aa)
      ([.gdp,.phosphate,.proton,Species.gtp,Species.water] ++ surplus) delivered deliveredInventory with
    ⟨transferred,second,transferredInventory⟩
  have translocationInventory : transferred.Perm
      ((Reaction.translocateInitiator aa).reactants ++
        ([.gdp,.phosphate,.proton] ++ surplus)) := by
    apply transferredInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Reaction.products,Reaction.reactants,List.count_cons,List.count_append,
      List.count_nil]
    omega
  rcases fire_available (.translocateInitiator aa) _ transferred translocationInventory with
    ⟨moved,third,movedInventory⟩
  refine ⟨delivered,transferred,moved,first,second,third,movedInventory.trans ?_⟩
  apply List.perm_iff_count.mpr
  intro species
  simp only [Reaction.products,firstCycleWaste,List.count_cons,List.count_append,List.count_nil]
  omega

def terminationWaste : Stock := [.gdp,.phosphate,.proton,.actor .eRF3]

def loadingWaste : Stock := [.gdp,.phosphate,.proton,.gdp,.phosphate,.proton]

theorem native_charged_load (surplus stock : Stock)
    (inventory : stock.Perm
      ([Species.chargedInitiator,Species.subunit40,Species.subunit60] ++ actors ++
        [Species.gtp,Species.water,Species.gtp,Species.water] ++ surplus)) :
    ∃ captured joined,
      fire .captureInitiator stock = .ok captured ∧
      fire .joinSubunit captured = .ok joined ∧
      joined.Perm (.initiatorPSite :: [.ribosome80] ++ loadingWaste ++ actors ++ surplus) := by
  have captureInventory : stock.Perm
      (Reaction.captureInitiator.reactants ++
        ([Species.subunit60,Species.gtp,Species.water,.actor .metRS,.actor .eIF5B,.actor .eRF1,.actor .eRF3] ++ surplus)) := by
    apply inventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Reaction.reactants,actors,factorStock,List.map_cons,List.map_nil,
      List.count_cons,List.count_append,List.count_nil,List.append_assoc]
    omega
  rcases fire_available .captureInitiator _ stock captureInventory with
    ⟨captured,first,capturedInventory⟩
  have joinInventory : captured.Perm
      (Reaction.joinSubunit.reactants ++
        ([.actor .metRS,.gdp,.phosphate,.proton,.actor .eIF1,.actor .eIF2,
          .actor .eIF3,.actor .eIF5,.actor .eRF1,.actor .eRF3] ++ surplus)) := by
    apply capturedInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Reaction.reactants,Reaction.products,factorStock,List.map_cons,List.map_nil,
      List.count_cons,List.count_append,List.count_nil,List.append_assoc]
    omega
  rcases fire_available .joinSubunit _ captured joinInventory with
    ⟨joined,second,joinedInventory⟩
  refine ⟨captured,joined,first,second,joinedInventory.trans ?_⟩
  apply List.perm_iff_count.mpr
  intro species
  simp only [Reaction.products,loadingWaste,actors,factorStock,List.map_cons,List.map_nil,
    List.count_cons,List.count_append,List.count_nil,List.append_assoc]
  omega

theorem native_initiator_release (surplus stock : Stock)
    (inventory : stock.Perm (.initiatorPSite :: terminationFuel ++ surplus)) :
    ∃ stopped released,
      fire .stopInitiator stock = .ok stopped ∧
      fire .releaseInitiator stopped = .ok released ∧
      released.Perm
        ([.releasedPeptide (.M,[]),.postTerminationInitiator] ++ terminationWaste ++ surplus) := by
  rcases fire_available .stopInitiator (Species.water :: surplus) stock inventory with
    ⟨stopped,first,stoppedInventory⟩
  have releaseInventory : stopped.Perm
      (Reaction.releaseInitiator.reactants ++ terminationWaste ++ surplus) := by
    apply stoppedInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Reaction.products,Reaction.reactants,terminationWaste,List.count_cons,
      List.count_append,List.count_nil]
    omega
  rcases fire_available .releaseInitiator (terminationWaste ++ surplus) stopped releaseInventory with
    ⟨released,second,releasedInventory⟩
  exact ⟨stopped,released,first,second,releasedInventory⟩

theorem native_peptidyl_release (chain : Peptide) (surplus stock : Stock)
    (inventory : stock.Perm (.peptidyl chain :: terminationFuel ++ surplus)) :
    ∃ stopped released,
      fire (.stopPeptidyl chain) stock = .ok stopped ∧
      fire (.releasePeptidyl chain) stopped = .ok released ∧
      released.Perm
        ([.releasedPeptide chain,.postTerminationElongator chain.last] ++ terminationWaste ++ surplus) := by
  rcases fire_available (.stopPeptidyl chain) (Species.water :: surplus) stock inventory with
    ⟨stopped,first,stoppedInventory⟩
  have releaseInventory : stopped.Perm
      ((Reaction.releasePeptidyl chain).reactants ++ terminationWaste ++ surplus) := by
    apply stoppedInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Reaction.products,Reaction.reactants,terminationWaste,List.count_cons,
      List.count_append,List.count_nil]
    omega
  rcases fire_available (.releasePeptidyl chain) (terminationWaste ++ surplus) stopped releaseInventory with
    ⟨released,second,releasedInventory⟩
  exact ⟨stopped,released,first,second,releasedInventory⟩

def elongationWasteWithInitiator (tail : List AA) : Stock :=
  match tail with
  | [] => []
  | aa :: rest => elongationWaste (.M,[aa]) rest ++ firstCycleWaste

def terminalComplex (tail : List AA) : Species :=
  match tail with
  | [] => .postTerminationInitiator
  | _ :: _ => .postTerminationElongator (Peptide.last (.M,tail))

theorem execute_nil (stock : Stock) : execute [] stock = ⟨[],[],stock,none⟩ := rfl

theorem advance_exact (aa : AA) (rest : List AA) :
    Program.advancePeptide (.M,[aa]) rest = (.M,aa :: rest) := by
  have word := Program.advance_peptide_word (.M,[aa]) rest
  change (Program.advancePeptide (.M,[aa]) rest).1 ::
    (Program.advancePeptide (.M,[aa]) rest).2 = .M :: aa :: rest at word
  have parts := List.cons.inj word
  exact Prod.ext parts.1 parts.2

theorem native_elongate_release (tail : List AA) (surplus stock : Stock)
    (inventory : stock.Perm
      (.initiatorPSite :: elongationFuel tail ++ terminationFuel ++ surplus)) :
    let program := UnifiedBoundary.elongation tail ++ UnifiedBoundary.termination tail
    let result := execute program stock
    result.fired = program ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm ([.releasedPeptide (.M,tail),terminalComplex tail] ++
        elongationWasteWithInitiator tail ++ terminationWaste ++ surplus) := by
  cases tail with
  | nil =>
      simp only [UnifiedBoundary.elongation,UnifiedBoundary.termination]
      rcases native_initiator_release surplus stock
        (by simpa only [elongationFuel,List.flatMap_nil,List.nil_append,List.cons_append] using inventory) with
        ⟨stopped,released,first,second,finalInventory⟩
      simp only [List.nil_append,CPS1Deamination.ExecutionReadout.execute_cons,first,second,execute_nil]
      exact ⟨by trivial,by trivial,by trivial,by simpa only [terminalComplex,elongationWasteWithInitiator,
        List.append_nil,List.nil_append] using finalInventory⟩
  | cons aa rest =>
      simp only [UnifiedBoundary.elongation,UnifiedBoundary.termination]
      rcases native_first_cycle aa (elongationFuel rest ++ terminationFuel ++ surplus) stock
        (by simpa only [elongationFuel,List.flatMap_cons,List.append_assoc,List.cons_append] using inventory) with
        ⟨delivered,transferred,moved,first,second,third,movedInventory⟩
      have nextInventory : moved.Perm (.peptidyl (.M,[aa]) :: elongationFuel rest ++
          (terminationFuel ++ firstCycleWaste ++ surplus)) := by
        apply movedInventory.trans
        apply List.perm_iff_count.mpr
        intro species
        simp only [List.count_append,List.count_cons]
        omega
      have extended := native_elongation_complete (.M,[aa]) rest
        (terminationFuel ++ firstCycleWaste ++ surplus) moved nextInventory
      rcases extended with ⟨fired,remaining,missing,extendedInventory⟩
      have terminalInventory : (execute (Program.compileElongation (.M,[aa]) rest) moved).stock.Perm
          (.peptidyl (.M,aa :: rest) :: terminationFuel ++
            (elongationWaste (.M,[aa]) rest ++ firstCycleWaste ++ surplus)) := by
        apply extendedInventory.trans
        rw [advance_exact]
        apply List.perm_iff_count.mpr
        intro species
        simp only [List.count_append,List.count_cons]
        omega
      rcases native_peptidyl_release (.M,aa :: rest) _ _ terminalInventory with
        ⟨stopped,released,stopPaid,releasePaid,finalInventory⟩
      simp only [List.cons_append,List.nil_append,List.append_assoc,
        CPS1Deamination.ExecutionReadout.execute_cons,first,second,third]
      rw [execute_append_paid _ _ _ remaining missing]
      simp only [CPS1Deamination.ExecutionReadout.execute_cons,stopPaid,releasePaid,execute_nil,fired]
      refine ⟨by trivial,by trivial,by trivial,finalInventory.trans ?_⟩
      apply List.perm_iff_count.mpr
      intro species
      simp only [terminalComplex,elongationWasteWithInitiator,List.count_append,List.count_cons,List.count_nil]
      omega

def boundarySurplus (tail : List AA) (surplus : Stock) : Stock :=
  [Species.subunit40,Species.subunit60] ++ actors ++ [Species.gtp,Species.water,Species.gtp,Species.water] ++
    energyFuel tail ++ [Species.gtp,Species.water,Species.water] ++ surplus

def passiveActors : Stock :=
  factorStock [.metRS,.eIF1,.eIF1A,.eIF2,.eIF3,.eIF5,.eIF5B]

def finalProducts (tail : List AA) : Stock :=
  [.releasedPeptide (.M,tail),terminalComplex tail] ++ elongationWasteWithInitiator tail ++
    terminationWaste ++ loadingWaste ++ chargingWaste tail ++ [Species.amp,Species.ppi] ++ passiveActors

/-- Raw source-residue inventory drives the one interpreter through charging, loading,
all extension cycles, recognition and hydrolytic release. -/
theorem native_compile_complete (tail : List AA) (surplus stock : Stock)
    (inventory : stock.Perm (rawFuel tail ++ surplus)) :
    let result := execute (UnifiedBoundary.compile tail) stock
    result.fired = UnifiedBoundary.compile tail ∧ result.remaining = [] ∧
      result.missing = none ∧ result.stock.Perm (finalProducts tail ++ surplus) := by
  have firstInventory : stock.Perm
      (Reaction.chargeInitiator.reactants ++ (chargingFuel tail ++
        ([Species.subunit40,Species.subunit60] ++
          factorStock [.eIF1,.eIF1A,.eIF2,.eIF3,.eIF5,.eIF5B,.eRF1,.eRF3] ++
          [Species.gtp,Species.water,Species.gtp,Species.water] ++ energyFuel tail ++ [Species.gtp,Species.water,Species.water] ++ surplus))) := by
    apply inventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [rawFuel,Reaction.reactants,actors,factorStock,List.map_cons,List.map_nil,
      List.count_cons,List.count_append,List.count_nil]
    omega
  rcases fire_available .chargeInitiator _ stock firstInventory with
    ⟨initiatorCharged,initiatorPaid,initiatorInventory⟩
  have chargingInventory : initiatorCharged.Perm
      (chargingFuel tail ++ (Species.chargedInitiator :: [Species.amp,Species.ppi] ++ boundarySurplus tail surplus)) := by
    apply initiatorInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Reaction.products,boundarySurplus,actors,factorStock,List.map_cons,List.map_nil,
      List.count_cons,List.count_append,List.count_nil]
    omega
  have chargingCompleted := native_charging_complete tail
    (Species.chargedInitiator :: [Species.amp,Species.ppi] ++ boundarySurplus tail surplus) initiatorCharged chargingInventory
  rcases chargingCompleted with ⟨chargingFired,chargingRemaining,chargingMissing,chargingInventory⟩
  have rearranged := chargingInventory.trans
    ((charging_products_split tail).append_right
      (Species.chargedInitiator :: [Species.amp,Species.ppi] ++ boundarySurplus tail surplus))
  have poolEnergy : (tail.map Species.aaTRNA ++ chargingWaste tail ++
      (Species.chargedInitiator :: [Species.amp,Species.ppi] ++ boundarySurplus tail surplus)).Perm
      ((tail.map Species.aaTRNA ++ energyFuel tail) ++
        ([Species.chargedInitiator,Species.subunit40,Species.subunit60] ++ actors ++ [Species.gtp,Species.water,Species.gtp,Species.water] ++
          chargingWaste tail ++ [Species.amp,Species.ppi,Species.gtp,Species.water,Species.water] ++ surplus)) := by
    apply List.perm_iff_count.mpr
    intro species
    simp only [boundarySurplus,List.count_cons,List.count_append,List.count_nil]
    omega
  have ready := rearranged.trans (poolEnergy.trans ((charged_energy_split tail).append_right
    ([Species.chargedInitiator,Species.subunit40,Species.subunit60] ++ actors ++ [Species.gtp,Species.water,Species.gtp,Species.water] ++
      chargingWaste tail ++ [Species.amp,Species.ppi,Species.gtp,Species.water,Species.water] ++ surplus)))
  have loadingInventory : (execute (tail.map Reaction.charge) initiatorCharged).stock.Perm
      ([Species.chargedInitiator,Species.subunit40,Species.subunit60] ++ actors ++ [Species.gtp,Species.water,Species.gtp,Species.water] ++
        (elongationFuel tail ++ chargingWaste tail ++ [Species.amp,Species.ppi,Species.gtp,Species.water,Species.water] ++ surplus)) := by
    apply ready.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [List.count_append]
    omega
  rcases native_charged_load _ _ loadingInventory with
    ⟨captured,joined,capturePaid,joinPaid,joinedInventory⟩
  have elongationInventory : joined.Perm
      (.initiatorPSite :: elongationFuel tail ++ terminationFuel ++
        (loadingWaste ++ chargingWaste tail ++ [Species.amp,Species.ppi] ++ passiveActors ++ surplus)) := by
    apply joinedInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [terminationFuel,actors,passiveActors,factorStock,List.map_cons,List.map_nil,
      List.count_cons,List.count_append,List.count_nil]
    omega
  have ended := native_elongate_release tail
    (loadingWaste ++ chargingWaste tail ++ [Species.amp,Species.ppi] ++ passiveActors ++ surplus) joined
    elongationInventory
  change let result := execute (UnifiedBoundary.elongation tail ++ UnifiedBoundary.termination tail) joined
    result.fired = UnifiedBoundary.elongation tail ++ UnifiedBoundary.termination tail ∧
      result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm ([.releasedPeptide (.M,tail),terminalComplex tail] ++
        elongationWasteWithInitiator tail ++ terminationWaste ++
          (loadingWaste ++ chargingWaste tail ++ [Species.amp,Species.ppi] ++ passiveActors ++ surplus)) at ended
  rcases ended with ⟨endingFired,endingRemaining,endingMissing,endingInventory⟩
  simp only [UnifiedBoundary.compile,List.cons_append,List.nil_append,List.append_assoc]
  simp only [CPS1Deamination.ExecutionReadout.execute_cons,initiatorPaid]
  rw [execute_append_paid _ _ _ chargingRemaining chargingMissing]
  simp only [CPS1Deamination.ExecutionReadout.execute_cons,capturePaid,joinPaid]
  refine ⟨?_,endingRemaining,endingMissing,?_⟩
  · simp only [chargingFired,endingFired]
  · simpa only [finalProducts,List.append_assoc] using endingInventory

theorem canonical_raw_complete (tail : List AA) :
    let result := execute (UnifiedBoundary.compile tail) (rawFuel tail)
    result.fired = UnifiedBoundary.compile tail ∧ result.remaining = [] ∧
      result.missing = none ∧ result.stock.Perm (finalProducts tail) := by
  simpa only [List.append_nil] using native_compile_complete tail [] (rawFuel tail) (by simp)

end CPS1InitiationTermination.NativeComplete
