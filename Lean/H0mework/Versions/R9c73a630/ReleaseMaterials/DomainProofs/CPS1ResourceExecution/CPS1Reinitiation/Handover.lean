import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Reinitiation.NativeDictionary

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1Reinitiation.Handover
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

def dischargedSites : CPS1Recycling.Sites := ⟨.adp,.adp⟩

/-- The two registered paths each discharge their own remaining bound ATP, after commitment. -/
inductive Reaction
  | dischargeRemaining (path : CPS1Recycling.SplitSite) (rna : RegisteredRna) (address : Nat)
  | transferTo5B (rna : RegisteredRna) (address : Nat)
  | native (reaction : CPS1ResourceExecution.Reaction)
  deriving DecidableEq

namespace Reaction
def reactants (frame : CPS1Recycling.Frame) : Reaction → Stock frame
  | .dischargeRemaining path rna address =>
    [.committed path.after rna address,NativeDictionary.embedded frame .water]
  | .transferTo5B rna address =>
    [.committed dischargedSites rna address,
      NativeDictionary.embedded frame (.actor .eIF5B),NativeDictionary.embedded frame .gtp]
  | .native reaction => NativeDictionary.nativeReactants frame reaction

/-- Transfer is the post-recognition coarse boundary restriction of the same paid complex.
The native 48S token cannot enter the raw inlet; RNA, ABCE1 and all factors are returned explicitly. -/
def products (frame : CPS1Recycling.Frame) : Reaction → Stock frame
  | .dischargeRemaining _ rna address =>
    [.committed dischargedSites rna address,
      NativeDictionary.embedded frame .phosphate,NativeDictionary.embedded frame .proton]
  | .transferTo5B rna _ =>
    [NativeDictionary.embedded frame .initiator48S,.retained (.abce1 dischargedSites),.rna rna,
      .factor .eIF4A,.factor .eIF4B,.factor .eIF4E,.factor .eIF4G,
      NativeDictionary.embedded frame (.actor .eIF1A),NativeDictionary.embedded frame (.actor .eIF2),
      NativeDictionary.embedded frame (.actor .eIF3),NativeDictionary.embedded frame (.actor .eIF5),
      NativeDictionary.embedded frame .gdp,NativeDictionary.embedded frame (.actor .eIF5B),
      NativeDictionary.embedded frame .gtp]
  | .native reaction => NativeDictionary.nativeProducts frame reaction
end Reaction

abbrev Execution (frame : CPS1Recycling.Frame) := Inventory.Execution (Species frame) Reaction

/-- Another reaction dictionary specializes the same inventory kernel, on the unchanged carrier. -/
def execute (frame : CPS1Recycling.Frame) (program : List Reaction) (stock : Stock frame) : Execution frame :=
  Inventory.execute (Reaction.reactants frame) (Reaction.products frame) program stock

theorem execute_nil (frame : CPS1Recycling.Frame) (stock : Stock frame) :
    execute frame [] stock = ⟨[],[],stock,none⟩ := rfl

theorem execute_cons (frame : CPS1Recycling.Frame) (reaction : Reaction) (rest : List Reaction)
    (stock : Stock frame) : execute frame (reaction :: rest) stock =
    match Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock with
    | .error missing => ⟨[],reaction :: rest,stock,some missing⟩
    | .ok next =>
      let after := execute frame rest next
      ⟨reaction :: after.fired,after.remaining,after.stock,after.missing⟩ := by
  unfold execute
  rw [Inventory.execute_cons]
  cases Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock <;> rfl

def program (path : CPS1Recycling.SplitSite) (rna : RegisteredRna) (address : Nat) : List Reaction :=
  [.dischargeRemaining path rna address,.transferTo5B rna address,.native .joinSubunit]

def input (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (rna : RegisteredRna) (address : Nat) : Stock frame :=
  [.committed path.after rna address,NativeDictionary.embedded frame .subunit60,
    NativeDictionary.embedded frame (.actor .eIF5B),NativeDictionary.embedded frame .gtp,
    NativeDictionary.embedded frame .water,NativeDictionary.embedded frame .water]

def retainedAfterJoin (frame : CPS1Recycling.Frame) (rna : RegisteredRna) : Stock frame :=
  [.retained (.abce1 dischargedSites),.rna rna,
    .factor .eIF4A,.factor .eIF4B,.factor .eIF4E,.factor .eIF4G,
    NativeDictionary.embedded frame (.actor .eIF2),NativeDictionary.embedded frame (.actor .eIF3),
    NativeDictionary.embedded frame (.actor .eIF5),NativeDictionary.embedded frame .gdp,
    NativeDictionary.embedded frame .phosphate,NativeDictionary.embedded frame .proton]

def products (frame : CPS1Recycling.Frame) (rna : RegisteredRna) : Stock frame :=
  (CPS1ResourceExecution.Reaction.joinSubunit.products).map (NativeDictionary.embedded frame) ++
    retainedAfterJoin frame rna

/-- No boundary token or completed handover enters the premise: the committed source complex pays it. -/
theorem native_join_complete (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (rna : RegisteredRna) (address : Nat) (surplus stock : Stock frame)
    (inventory : stock.Perm (input frame path rna address ++ surplus)) :
    let result := execute frame (program path rna address) stock
    result.fired = program path rna address ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm (products frame rna ++ surplus) := by
  let rest1 : Stock frame := [NativeDictionary.embedded frame .subunit60,
    NativeDictionary.embedded frame (.actor .eIF5B),NativeDictionary.embedded frame .gtp,
    NativeDictionary.embedded frame .water] ++ surplus
  have inv1 : stock.Perm ((Reaction.dischargeRemaining path rna address).reactants frame ++ rest1) := by
    apply inventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [input,Reaction.reactants,rest1,List.count_cons,List.count_append,List.count_nil]
    omega
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame)
    (.dischargeRemaining path rna address) rest1 stock inv1 with ⟨discharged,paid1,invDischarged⟩
  let rest2 : Stock frame := [NativeDictionary.embedded frame .subunit60,NativeDictionary.embedded frame .water,
    NativeDictionary.embedded frame .phosphate,NativeDictionary.embedded frame .proton] ++ surplus
  have inv2 : discharged.Perm ((Reaction.transferTo5B rna address).reactants frame ++ rest2) := by
    apply invDischarged.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Reaction.reactants,Reaction.products,rest1,rest2,List.count_cons,List.count_append,List.count_nil]
    omega
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame)
    (.transferTo5B rna address) rest2 discharged inv2 with ⟨ready,paid2,invReady⟩
  have inv3 : ready.Perm ((Reaction.native .joinSubunit).reactants frame ++
      (retainedAfterJoin frame rna ++ surplus)) := by
    apply invReady.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Reaction.reactants,Reaction.products,NativeDictionary.nativeReactants,
      CPS1ResourceExecution.Reaction.reactants,retainedAfterJoin,rest2,
      List.map_cons,List.map_nil,List.count_cons,List.count_append,List.count_nil]
    omega
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame)
    (.native .joinSubunit) (retainedAfterJoin frame rna ++ surplus) ready inv3 with ⟨joined,paid3,invJoined⟩
  dsimp only
  simp only [program,execute_cons,paid1,paid2,paid3,execute_nil]
  refine ⟨by trivial,by trivial,by trivial,?_⟩
  simpa only [products,Reaction.products,NativeDictionary.nativeProducts,List.append_assoc] using invJoined

theorem lift_fire (frame : CPS1Recycling.Frame) (reaction : CPS1ResourceExecution.Reaction)
    (old next : CPS1ResourceExecution.Stock) (paid : CPS1ResourceExecution.fire reaction old = .ok next)
    (surplus stock : Stock frame)
    (inventory : stock.Perm (old.map (NativeDictionary.embedded frame) ++ surplus)) :
    ∃ actual, Inventory.fire (Reaction.reactants frame) (Reaction.products frame) (.native reaction) stock =
      .ok actual ∧ actual.Perm (next.map (NativeDictionary.embedded frame) ++ surplus) := by
  unfold CPS1ResourceExecution.fire Inventory.fire at paid
  cases consumed : Inventory.consume reaction.reactants old with
  | error missing => simp [consumed] at paid
  | ok remainder =>
    simp only [consumed,Except.ok.injEq] at paid
    subst next
    have oldInventory := (Inventory.consume_perm _ _ _ consumed).map (NativeDictionary.embedded frame)
    have aligned : stock.Perm ((Reaction.native reaction).reactants frame ++
        (remainder.map (NativeDictionary.embedded frame) ++ surplus)) := by
      simpa only [Reaction.reactants,NativeDictionary.nativeReactants,List.map_append,List.append_assoc] using
        inventory.trans (oldInventory.append_right surplus)
    rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame)
      (.native reaction) _ stock aligned with ⟨actual,fired,after⟩
    exact ⟨actual,fired,by simpa only [Reaction.products,NativeDictionary.nativeProducts,
      List.map_append,List.append_assoc] using after⟩

/-- The lifted native dictionary consumes the old generated trace without discarding its common-carrier surplus. -/
theorem lift_program (frame : CPS1Recycling.Frame) (program : List CPS1ResourceExecution.Reaction)
    (old : CPS1ResourceExecution.Stock) (surplus stock : Stock frame)
    (inventory : stock.Perm (old.map (NativeDictionary.embedded frame) ++ surplus))
    (complete : (CPS1ResourceExecution.execute program old).missing = none) :
    let result := execute frame (program.map Reaction.native) stock
    result.fired = program.map Reaction.native ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm ((CPS1ResourceExecution.execute program old).stock.map (NativeDictionary.embedded frame) ++ surplus) := by
  induction program generalizing old stock with
  | nil =>
    dsimp only
    simp only [List.map_nil,execute_nil,CPS1InitiationTermination.NativeComplete.execute_nil]
    exact ⟨by trivial,by trivial,by trivial,inventory⟩
  | cons reaction rest ih =>
    cases action : CPS1ResourceExecution.fire reaction old with
    | error missing =>
      simp only [CPS1Deamination.ExecutionReadout.execute_cons,action] at complete
      contradiction
    | ok next =>
      have afterComplete : (CPS1ResourceExecution.execute rest next).missing = none := by
        simpa only [CPS1Deamination.ExecutionReadout.execute_cons,action] using complete
      rcases lift_fire frame reaction old next action surplus stock inventory with ⟨actual,paid,actualInventory⟩
      have later := ih next actual actualInventory afterComplete
      dsimp only at later ⊢
      simp only [List.map_cons,execute_cons,paid,CPS1Deamination.ExecutionReadout.execute_cons,action]
      exact ⟨congrArg (Reaction.native reaction :: ·) later.1,later.2⟩

def bodyInput (tail : List AA) : CPS1ResourceExecution.Stock :=
  .initiatorPSite :: CPS1EndogenousTranslation.chargingFuel tail ++
    CPS1InitiationTermination.NativeComplete.energyFuel tail ++ CPS1InitiationTermination.NativeComplete.terminationFuel

def bodyProgram (tail : List AA) : List CPS1ResourceExecution.Reaction :=
  tail.map CPS1ResourceExecution.Reaction.charge ++
    CPS1InitiationTermination.UnifiedBoundary.elongation tail ++
    CPS1InitiationTermination.UnifiedBoundary.termination tail

def bodyProducts (tail : List AA) : CPS1ResourceExecution.Stock :=
  [.releasedPeptide (.M,tail),CPS1InitiationTermination.NativeComplete.terminalComplex tail] ++
    CPS1InitiationTermination.NativeComplete.elongationWasteWithInitiator tail ++
    CPS1InitiationTermination.NativeComplete.terminationWaste ++
    CPS1InitiationTermination.NativeComplete.chargingWaste tail

/-- The old paid charging and elongation producers consume the newly generated native P-site. -/
theorem body_complete (tail : List AA) (surplus stock : CPS1ResourceExecution.Stock)
    (inventory : stock.Perm (bodyInput tail ++ surplus)) :
    let result := CPS1ResourceExecution.execute (bodyProgram tail) stock
    result.fired = bodyProgram tail ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm (bodyProducts tail ++ surplus) := by
  let rest1 : CPS1ResourceExecution.Stock := .initiatorPSite ::
    CPS1InitiationTermination.NativeComplete.energyFuel tail ++
    CPS1InitiationTermination.NativeComplete.terminationFuel ++ surplus
  have chargingInventory : stock.Perm (CPS1EndogenousTranslation.chargingFuel tail ++ rest1) := by
    apply inventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [bodyInput,rest1,List.count_cons,List.count_append]
    omega
  have charging := CPS1EndogenousTranslation.native_charging_complete tail rest1 stock chargingInventory
  have chargedInventory := charging.2.2.2.trans
    ((CPS1InitiationTermination.NativeComplete.charging_products_split tail).append_right rest1)
  have readyInventory : (CPS1ResourceExecution.execute (tail.map CPS1ResourceExecution.Reaction.charge) stock).stock.Perm
      (.initiatorPSite :: CPS1EndogenousTranslation.elongationFuel tail ++
        CPS1InitiationTermination.NativeComplete.terminationFuel ++
          (CPS1InitiationTermination.NativeComplete.chargingWaste tail ++ surplus)) := by
    have rearranged : (tail.map CPS1ResourceExecution.Species.aaTRNA ++
        CPS1InitiationTermination.NativeComplete.chargingWaste tail ++ rest1).Perm
        (.initiatorPSite :: (tail.map CPS1ResourceExecution.Species.aaTRNA ++
          CPS1InitiationTermination.NativeComplete.energyFuel tail) ++
          (CPS1InitiationTermination.NativeComplete.terminationFuel ++
            (CPS1InitiationTermination.NativeComplete.chargingWaste tail ++ surplus))) := by
      apply List.perm_iff_count.mpr
      intro species
      simp only [rest1,List.count_cons,List.count_append]
      omega
    exact chargedInventory.trans (rearranged.trans (by
      simpa only [List.append_assoc] using
        ((CPS1InitiationTermination.NativeComplete.charged_energy_split tail).cons
          CPS1ResourceExecution.Species.initiatorPSite).append_right
            (CPS1InitiationTermination.NativeComplete.terminationFuel ++
              (CPS1InitiationTermination.NativeComplete.chargingWaste tail ++ surplus))))
  have ended := CPS1InitiationTermination.NativeComplete.native_elongate_release tail
    (CPS1InitiationTermination.NativeComplete.chargingWaste tail ++ surplus) _ readyInventory
  dsimp only
  unfold bodyProgram
  rw [List.append_assoc,CPS1InitiationTermination.NativeComplete.execute_append_paid _ _ _ charging.2.1 charging.2.2.1]
  refine ⟨?_,ended.2.1,ended.2.2.1,?_⟩
  · change (CPS1ResourceExecution.execute (tail.map CPS1ResourceExecution.Reaction.charge) stock).fired ++
      (CPS1ResourceExecution.execute (CPS1InitiationTermination.UnifiedBoundary.elongation tail ++
        CPS1InitiationTermination.UnifiedBoundary.termination tail)
        (CPS1ResourceExecution.execute (tail.map CPS1ResourceExecution.Reaction.charge) stock).stock).fired = _
    rw [charging.1,ended.1]
  · simpa only [bodyProducts,List.append_assoc] using ended.2.2.2

theorem native_body_complete (frame : CPS1Recycling.Frame) (tail : List AA) (surplus stock : Stock frame)
    (inventory : stock.Perm ((bodyInput tail).map (NativeDictionary.embedded frame) ++ surplus)) :
    let result := execute frame ((bodyProgram tail).map Reaction.native) stock
    result.fired = (bodyProgram tail).map Reaction.native ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm ((bodyProducts tail).map (NativeDictionary.embedded frame) ++ surplus) := by
  have old := body_complete tail [] (bodyInput tail) (by simp)
  have actual := lift_program frame (bodyProgram tail) (bodyInput tail) surplus stock inventory old.2.2.1
  refine ⟨actual.1,actual.2.1,actual.2.2.1,?_⟩
  apply actual.2.2.2.trans
  simpa only [List.append_nil] using (old.2.2.2.map (NativeDictionary.embedded frame)).append_right surplus

def bodyFuel (tail : List AA) : CPS1ResourceExecution.Stock :=
  CPS1EndogenousTranslation.chargingFuel tail ++ CPS1InitiationTermination.NativeComplete.energyFuel tail ++
    [.gtp,.water,.water,.actor .eRF1,.actor .eRF3]

def joinPassive (frame : CPS1Recycling.Frame) (rna : RegisteredRna) : Stock frame :=
  [NativeDictionary.embedded frame .gdp,NativeDictionary.embedded frame .phosphate,NativeDictionary.embedded frame .proton,
    NativeDictionary.embedded frame (.actor .eIF1A),NativeDictionary.embedded frame (.actor .eIF5B)] ++
    retainedAfterJoin frame rna

def fullProgram (path : CPS1Recycling.SplitSite) (rna : RegisteredRna) (address : Nat) (tail : List AA) : List Reaction :=
  program path rna address ++ (bodyProgram tail).map Reaction.native

theorem execute_append_paid (frame : CPS1Recycling.Frame) (first rest : List Reaction) (stock : Stock frame)
    (paid : (execute frame first stock).remaining = []) (complete : (execute frame first stock).missing = none) :
    execute frame (first ++ rest) stock =
      let initial := execute frame first stock
      let after := execute frame rest initial.stock
      ⟨initial.fired ++ after.fired,after.remaining,after.stock,after.missing⟩ := by
  induction first generalizing stock with
  | nil => rfl
  | cons reaction first ih =>
    cases action : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock with
    | error missing =>
      simp only [execute_cons,action] at complete
      contradiction
    | ok next =>
      simp only [execute_cons,action] at paid complete ⊢
      simp only [List.cons_append,execute_cons,action]
      rw [ih next paid complete]

theorem native_full_complete (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (rna : RegisteredRna) (address : Nat) (tail : List AA) (surplus stock : Stock frame)
    (inventory : stock.Perm (input frame path rna address ++
      (bodyFuel tail).map (NativeDictionary.embedded frame) ++ surplus)) :
    let result := execute frame (fullProgram path rna address tail) stock
    result.fired = fullProgram path rna address tail ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm ((bodyProducts tail).map (NativeDictionary.embedded frame) ++
        joinPassive frame rna ++ surplus) := by
  have joined := native_join_complete frame path rna address
    ((bodyFuel tail).map (NativeDictionary.embedded frame) ++ surplus) stock
    (by simpa only [List.append_assoc] using inventory)
  have bodyInventory : (execute frame (program path rna address) stock).stock.Perm
      ((bodyInput tail).map (NativeDictionary.embedded frame) ++ (joinPassive frame rna ++ surplus)) := by
    apply joined.2.2.2.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [products,bodyInput,bodyFuel,joinPassive,CPS1ResourceExecution.Reaction.products,
      CPS1InitiationTermination.NativeComplete.terminationFuel,List.map_append,List.map_cons,List.map_nil,
      List.count_cons,List.count_append,List.count_nil]
    omega
  have body := native_body_complete frame tail (joinPassive frame rna ++ surplus) _ bodyInventory
  dsimp only
  unfold fullProgram
  rw [execute_append_paid frame _ _ _ joined.2.1 joined.2.2.1]
  refine ⟨?_,body.2.1,body.2.2.1,?_⟩
  · change (execute frame (program path rna address) stock).fired ++
      (execute frame ((bodyProgram tail).map Reaction.native)
        (execute frame (program path rna address) stock).stock).fired = _
    rw [joined.1,body.1]
  · simpa only [List.append_assoc] using body.2.2.2

inductive RawMaterial
  | aminoAcid (aa : AA) | trna (aa : AA) | atp | gtp | water
  deriving DecidableEq, Repr

def RawMaterial.species (frame : CPS1Recycling.Frame) : RawMaterial → Species frame
  | .aminoAcid aa => NativeDictionary.embedded frame (.freeAA aa)
  | .trna aa => NativeDictionary.embedded frame (.tRNA aa)
  | .atp => NativeDictionary.embedded frame .atp
  | .gtp => NativeDictionary.embedded frame .gtp
  | .water => NativeDictionary.embedded frame .water

def rawFuel (tail : List AA) : List RawMaterial :=
  [.gtp,.water,.water] ++ tail.flatMap (fun aa => [.aminoAcid aa,.trna aa,.atp]) ++
    tail.flatMap (fun _ => [RawMaterial.gtp,.water,.gtp,.water]) ++ [.gtp,.water,.water]

theorem raw_fuel_inventory (frame : CPS1Recycling.Frame) (tail : List AA) :
    (rawFuel tail).map (RawMaterial.species frame) =
      [NativeDictionary.embedded frame .gtp,NativeDictionary.embedded frame .water,NativeDictionary.embedded frame .water] ++
        (CPS1EndogenousTranslation.chargingFuel tail).map (NativeDictionary.embedded frame) ++
        (CPS1InitiationTermination.NativeComplete.energyFuel tail).map (NativeDictionary.embedded frame) ++
        [NativeDictionary.embedded frame .gtp,NativeDictionary.embedded frame .water,NativeDictionary.embedded frame .water] := by
  simp only [rawFuel,CPS1EndogenousTranslation.chargingFuel,CPS1ResourceExecution.Reaction.reactants,
    CPS1InitiationTermination.NativeComplete.energyFuel,List.map_append,List.map_flatMap,
    List.map_cons,List.map_nil,RawMaterial.species]

def programFromRna? (path : CPS1Recycling.SplitSite) (raw : List Char) : Option (List Reaction) := do
  let rna ← Rna.parse raw
  let address ← Coding.firstStart (Rna.template rna)
  let peptide ← Program.peptideFromRna? raw
  if peptide.1 = AA.M then pure (fullProgram path rna address peptide.2) else none

namespace Source

def execution (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (feed : List RawMaterial) : Option (Σ frame : CPS1Recycling.Frame, Execution frame) := do
  let prior ← CPS1Reinitiation.Source.execution edits water additional path recycleFeed scanFeed
  let program ← programFromRna? path
    SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.rawMrna
  pure ⟨prior.1,execute prior.1 program (prior.2.stock ++ feed.map (RawMaterial.species prior.1))⟩

theorem source_program (path : CPS1Recycling.SplitSite) :
    programFromRna? path
      SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.rawMrna =
      some (fullProgram path Molecules.mrna 151 Program.originalPeptide.2) := by
  unfold programFromRna?
  rw [Molecules.complete_original_chemical_words.2]
  change (do
    let address ← Coding.firstStart (Rna.template Molecules.mrna)
    let peptide ← Program.peptideFromRna?
      SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.rawMrna
    if peptide.1 = AA.M then pure (fullProgram path Molecules.mrna address peptide.2) else none) = _
  rw [CPS1Reinitiation.Source.original_start_and_context.1]
  change (do
    let peptide ← Program.peptideFromRna?
      SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.rawMrna
    if peptide.1 = AA.M then pure (fullProgram path Molecules.mrna 151 peptide.2) else none) = _
  rw [Program.original_peptide_generated]
  change (if Program.originalPeptide.1 = .M then _ else none) = _
  rw [if_pos (show Program.originalPeptide.1 = .M from by decide +kernel)]
  rfl

def rawSourceFuel : Option (List RawMaterial) :=
  (Program.peptideFromRna?
    SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.rawMrna).map
      (fun peptide => rawFuel peptide.2)

theorem raw_source_fuel_generated : rawSourceFuel = some (rawFuel Program.originalPeptide.2) := by
  rw [rawSourceFuel,Program.original_peptide_generated]
  rfl

/-- Remove only actors/subunits which the actual next program consumes; every other old product remains. -/
def historicalPassive (frame : CPS1Recycling.Frame) : CPS1Recycling.StockAt frame :=
  [.old .phosphate,.old .proton,.messageCoordinate,.old .amp,.old .ppi,.old (.actor .metRS)] ++
    CPS1Recycling.remainingTrna frame (CPS1Recycling.sourceTrna frame) ++
      (([.releasedPeptide (.M,frame.peptide.2)] ++
        CPS1Recycling.ResidueSplit.remainingElongationWaste frame.peptide.2 ++ [.gdp,.phosphate,.proton] ++
        CPS1InitiationTermination.NativeComplete.loadingWaste ++
        CPS1InitiationTermination.NativeComplete.chargingWaste frame.peptide.2 ++ [.amp,.ppi]) :
          CPS1ResourceExecution.Stock).map CPS1Recycling.Species.old

def surplus (frame : CPS1Recycling.Frame) (recycleExtra : List CPS1Recycling.RawMaterial)
    (scanExtra : List CPS1Reinitiation.RawMaterial) (extra : List RawMaterial) : Stock frame :=
  [.retained .eIF3j,NativeDictionary.embedded frame (.actor .eIF1),NativeDictionary.embedded frame .phosphate,
    NativeDictionary.embedded frame .proton] ++ workProducts frame 151 ++
    (historicalPassive frame ++ recycleExtra.map (CPS1Recycling.RawMaterial.species frame)).map Species.retained ++
    scanExtra.map (CPS1Reinitiation.RawMaterial.species frame) ++ extra.map (RawMaterial.species frame)

theorem actual_full_inventory (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite) (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (feed extra : List RawMaterial) (raw : feed.Perm (rawFuel Program.originalPeptide.2 ++ extra)) :
    let frame := CPS1Recycling.Source.frame edits water additional
    let recycled := CPS1Recycling.run frame (CPS1Recycling.productiveEvents path) recycleFeed
    let prior := CPS1Reinitiation.run frame recycled path.after Molecules.mrna scanFeed
    (prior.stock ++ feed.map (RawMaterial.species frame)).Perm
      (input frame path Molecules.mrna 151 ++
        (bodyFuel Program.originalPeptide.2).map (NativeDictionary.embedded frame) ++
        surplus frame recycleExtra scanExtra extra) := by
  let frame := CPS1Recycling.Source.frame edits water additional
  have previous := (CPS1Reinitiation.Source.native_complete edits water additional path
    recycleFeed recycleExtra recyclingRaw scanFeed scanExtra scanningRaw).2.2.2
  have fresh := raw.map (RawMaterial.species frame)
  apply (previous.append fresh).trans
  apply List.perm_iff_count.mpr
  intro species
  dsimp only [frame]
  simp only [List.map_append,raw_fuel_inventory,input,bodyFuel,scanProducts,surplus,
    CPS1Reinitiation.Source.surplus,CPS1Reinitiation.Source.passiveOld,CPS1Reinitiation.Source.nativeRemainder,
    historicalPassive,CPS1InitiationTermination.NativeComplete.terminationWaste,
    factorStock,NativeDictionary.embedded,List.map_append,List.map_cons,List.map_nil,
    List.count_append,List.count_cons,List.count_nil]
  omega

/-- The complete original raw editor RNA, actual recycled stock and raw amino acids/NTPs generate the next release. -/
theorem native_complete (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite) (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (feed extra : List RawMaterial) (raw : feed.Perm (rawFuel Program.originalPeptide.2 ++ extra)) :
    let frame := CPS1Recycling.Source.frame edits water additional
    let recycled := CPS1Recycling.run frame (CPS1Recycling.productiveEvents path) recycleFeed
    let prior := CPS1Reinitiation.run frame recycled path.after Molecules.mrna scanFeed
    let result := execute frame (fullProgram path Molecules.mrna 151 Program.originalPeptide.2)
      (prior.stock ++ feed.map (RawMaterial.species frame))
    result.fired = fullProgram path Molecules.mrna 151 Program.originalPeptide.2 ∧
      result.remaining = [] ∧ result.missing = none ∧ result.stock.Perm
        ((bodyProducts Program.originalPeptide.2).map (NativeDictionary.embedded frame) ++
          joinPassive frame Molecules.mrna ++ surplus frame recycleExtra scanExtra extra) :=
  native_full_complete _ path Molecules.mrna 151 Program.originalPeptide.2 _ _
    (actual_full_inventory edits water additional path recycleFeed recycleExtra recyclingRaw
      scanFeed scanExtra scanningRaw feed extra raw)

theorem execution_from_actual_stock (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite) (recycleFeed : List CPS1Recycling.RawMaterial)
    (scanFeed : List CPS1Reinitiation.RawMaterial) (feed : List RawMaterial) :
    let frame := CPS1Recycling.Source.frame edits water additional
    let recycled := CPS1Recycling.run frame (CPS1Recycling.productiveEvents path) recycleFeed
    let prior := CPS1Reinitiation.run frame recycled path.after Molecules.mrna scanFeed
    execution edits water additional path recycleFeed scanFeed feed =
      some ⟨frame,execute frame (fullProgram path Molecules.mrna 151 Program.originalPeptide.2)
        (prior.stock ++ feed.map (RawMaterial.species frame))⟩ := by
  dsimp only
  rw [execution,CPS1Reinitiation.Source.execution_from_actual_stock]
  change (do
    let plan ← programFromRna? path
      SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.rawMrna
    pure (⟨CPS1Recycling.Source.frame edits water additional,
      execute (CPS1Recycling.Source.frame edits water additional) plan
        ((CPS1Reinitiation.run (CPS1Recycling.Source.frame edits water additional)
          (CPS1Recycling.run (CPS1Recycling.Source.frame edits water additional)
            (CPS1Recycling.productiveEvents path) recycleFeed) path.after Molecules.mrna scanFeed).stock ++
          feed.map (RawMaterial.species (CPS1Recycling.Source.frame edits water additional)))⟩ :
            Σ frame : CPS1Recycling.Frame, Execution frame)) = _
  rw [source_program]
  rfl

theorem released_editor_next_postTC_and_both_RNAs (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite) (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (feed extra : List RawMaterial) (raw : feed.Perm (rawFuel Program.originalPeptide.2 ++ extra)) :
    let frame := CPS1Recycling.Source.frame edits water additional
    let recycled := CPS1Recycling.run frame (CPS1Recycling.productiveEvents path) recycleFeed
    let prior := CPS1Reinitiation.run frame recycled path.after Molecules.mrna scanFeed
    let result := execute frame (fullProgram path Molecules.mrna 151 Program.originalPeptide.2)
      (prior.stock ++ feed.map (RawMaterial.species frame))
    NativeDictionary.embedded frame (.releasedPeptide (.M,Program.originalPeptide.2)) ∈ result.stock ∧
      NativeDictionary.embedded frame
        (CPS1InitiationTermination.NativeComplete.terminalComplex Program.originalPeptide.2) ∈ result.stock ∧
      Species.rna Molecules.mrna ∈ result.stock ∧
      Species.retained (.abce1 dischargedSites) ∈ result.stock ∧
      Species.retained .messageCoordinate ∈ result.stock ∧
      (.M :: Program.originalPeptide.2).length = 1605 := by
  have produced := (native_complete edits water additional path recycleFeed recycleExtra recyclingRaw
    scanFeed scanExtra scanningRaw feed extra raw).2.2.2
  refine ⟨produced.mem_iff.mpr ?_,produced.mem_iff.mpr ?_,produced.mem_iff.mpr ?_,
    produced.mem_iff.mpr ?_,produced.mem_iff.mpr ?_,?_⟩
  · simp [bodyProducts,NativeDictionary.embedded]
  · simp [bodyProducts,NativeDictionary.embedded]
  · simp [joinPassive,retainedAfterJoin]
  · simp [joinPassive,retainedAfterJoin]
  · simp [surplus,historicalPassive]
  · simp only [List.length_cons,Program.original_core_lengths.2.2.1]

end Source
end CPS1Reinitiation.Handover
