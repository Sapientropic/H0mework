import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1StockRecursion.Stock

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1StockRecursion.RecyclingLift
open CPS1ResourceExecution
open CPS1Recycling
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

def reactants (frame : CPS1Recycling.Frame) (reaction : CPS1Recycling.Primitive) :
    CPS1Reinitiation.Stock frame :=
  (reaction.reactants frame).map CPS1Reinitiation.Species.retained

def products (frame : CPS1Recycling.Frame) (reaction : CPS1Recycling.Primitive) :
    CPS1Reinitiation.Stock frame :=
  (reaction.products frame).map CPS1Reinitiation.Species.retained

abbrev Execution (frame : CPS1Recycling.Frame) :=
  Inventory.Execution (CPS1Reinitiation.Species frame) CPS1Recycling.Primitive

/-- Recycling uses the retained dictionary on the unchanged common stock carrier. -/
def execute (frame : CPS1Recycling.Frame) (program : List CPS1Recycling.Primitive)
    (stock : CPS1Reinitiation.Stock frame) : Execution frame :=
  Inventory.execute (reactants frame) (products frame) program stock

theorem lift_fire (frame : CPS1Recycling.Frame) (reaction : CPS1Recycling.Primitive)
    (old next : CPS1Recycling.StockAt frame)
    (paid : Inventory.fire (CPS1Recycling.Primitive.reactants frame)
      (CPS1Recycling.Primitive.products frame) reaction old = .ok next)
    (surplus stock : CPS1Reinitiation.Stock frame)
    (inventory : stock.Perm (old.map CPS1Reinitiation.Species.retained ++ surplus)) :
    ∃ actual, Inventory.fire (reactants frame) (products frame) reaction stock = .ok actual ∧
      actual.Perm (next.map CPS1Reinitiation.Species.retained ++ surplus) := by
  unfold Inventory.fire at paid
  cases consumed : Inventory.consume (reaction.reactants frame) old with
  | error missing => simp [consumed] at paid
  | ok remainder =>
    simp only [consumed,Except.ok.injEq] at paid
    subst next
    have oldInventory := (Inventory.consume_perm _ _ _ consumed).map
      (CPS1Reinitiation.Species.retained (frame := frame))
    have aligned : stock.Perm (reactants frame reaction ++
        (remainder.map CPS1Reinitiation.Species.retained ++ surplus)) := by
      simpa only [reactants,List.map_append,List.append_assoc] using
        inventory.trans (oldInventory.append_right surplus)
    rcases Inventory.fire_available (reactants frame) (products frame) reaction _ stock aligned with
      ⟨actual,fired,after⟩
    exact ⟨actual,fired,by simpa only [products,List.map_append,List.append_assoc] using after⟩

/-- A paid recycling trace lifts into the actual common stock and retains every surplus species. -/
theorem lift_program (frame : CPS1Recycling.Frame) (program : List CPS1Recycling.Primitive)
    (old : CPS1Recycling.StockAt frame) (surplus stock : CPS1Reinitiation.Stock frame)
    (inventory : stock.Perm (old.map CPS1Reinitiation.Species.retained ++ surplus))
    (complete : (Inventory.execute (CPS1Recycling.Primitive.reactants frame)
      (CPS1Recycling.Primitive.products frame) program old).missing = none) :
    let result := execute frame program stock
    result.fired = program ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm ((Inventory.execute (CPS1Recycling.Primitive.reactants frame)
        (CPS1Recycling.Primitive.products frame) program old).stock.map
          CPS1Reinitiation.Species.retained ++ surplus) := by
  induction program generalizing old stock with
  | nil =>
    dsimp only [execute,Inventory.execute]
    exact ⟨rfl,rfl,rfl,inventory⟩
  | cons reaction rest ih =>
    cases action : Inventory.fire (CPS1Recycling.Primitive.reactants frame)
        (CPS1Recycling.Primitive.products frame) reaction old with
    | error missing =>
      simp only [Inventory.execute,action] at complete
      contradiction
    | ok next =>
      have afterComplete : (Inventory.execute (CPS1Recycling.Primitive.reactants frame)
          (CPS1Recycling.Primitive.products frame) rest next).missing = none := by
        simpa only [Inventory.execute,action] using complete
      rcases lift_fire frame reaction old next action surplus stock inventory with
        ⟨actual,paid,actualInventory⟩
      have later := ih next actual actualInventory afterComplete
      dsimp only at later ⊢
      simp only [execute,Inventory.execute,paid,action]
      exact ⟨congrArg (reaction :: ·) later.1,later.2⟩

/-- The supplied tRNA determines this next recycling occurrence; the old source tRNA is unused. -/
theorem native_core_complete (frame : CPS1Recycling.Frame) (trna : CPS1Recycling.Trna)
    (path : CPS1Recycling.SplitSite) (surplus stock : CPS1Reinitiation.Stock frame)
    (inventory : stock.Perm ((CPS1Recycling.coreInput frame trna).map
      CPS1Reinitiation.Species.retained ++ surplus)) :
    let result := execute frame (CPS1Recycling.coreProgram trna path) stock
    result.fired = CPS1Recycling.coreProgram trna path ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm ((CPS1Recycling.coreProducts frame trna path).map
        CPS1Reinitiation.Species.retained ++ surplus) := by
  have old := CPS1Recycling.native_core_complete frame trna path []
    (CPS1Recycling.coreInput frame trna) (by simp)
  have actual := lift_program frame (CPS1Recycling.coreProgram trna path)
    (CPS1Recycling.coreInput frame trna) surplus stock inventory old.2.2.1
  refine ⟨actual.1,actual.2.1,actual.2.2.1,?_⟩
  apply actual.2.2.2.trans
  simpa only [List.append_nil] using
    (old.2.2.2.map CPS1Reinitiation.Species.retained).append_right surplus

def afterBindingInput (frame : CPS1Recycling.Frame) (trna : CPS1Recycling.Trna) : StockAt frame :=
  [.preSplit trna doubleATP,.old .water,.old (.actor .eIF1),
    .old (.actor .eIF1A),.old (.actor .eIF3),.eIF3j] ++ beforeInitiator frame trna ++
      [.old (.freeAA .M),.old .atp,.old (.actor .metRS),.old .gtp,.old (.actor .eIF2)]

/-- The actual loaded complex pays the remaining five original recycling actions. -/
theorem native_after_binding_complete (frame : CPS1Recycling.Frame) (trna : CPS1Recycling.Trna)
    (path : CPS1Recycling.SplitSite) (surplus stock : StockAt frame)
    (inventory : stock.Perm (afterBindingInput frame trna ++ surplus)) :
    let program := (CPS1Recycling.coreProgram trna path).drop 2
    let result := Inventory.execute (CPS1Recycling.Primitive.reactants frame)
      (CPS1Recycling.Primitive.products frame) program stock
    result.fired = program ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm (CPS1Recycling.coreProducts frame trna path ++ surplus) := by
  let rest3 : StockAt frame := [.old (.actor .eIF1),.old (.actor .eIF1A),
    .old (.actor .eIF3),.eIF3j] ++ beforeInitiator frame trna ++
      [.old (.freeAA .M),.old .atp,.old (.actor .metRS),.old .gtp,.old (.actor .eIF2)] ++ surplus
  have inv3 : stock.Perm ((splitPrimitive trna path).reactants frame ++ rest3) := by
    cases path <;> simpa only [afterBindingInput,splitPrimitive,CPS1Recycling.Primitive.reactants,
      rest3,List.append_assoc,List.cons_append,List.nil_append] using inventory
  rcases Inventory.fire_available (CPS1Recycling.Primitive.reactants frame)
    (CPS1Recycling.Primitive.products frame) (splitPrimitive trna path) rest3 stock inv3 with
      ⟨split,paid3,splitInventory⟩
  let rest4 : StockAt frame := [.old .subunit60,.old (.actor .eRF1),.old .phosphate,
    .old .proton,.eIF3j] ++ beforeInitiator frame trna ++
      [.old (.freeAA .M),.old .atp,.old (.actor .metRS),.old .gtp,.old (.actor .eIF2)] ++ surplus
  have inv4 : split.Perm ((CPS1Recycling.Primitive.removeTrna trna path.after).reactants frame ++ rest4) := by
    apply splitInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    cases path <;> simp only [splitPrimitive,SplitSite.after,CPS1Recycling.Primitive.reactants,
      CPS1Recycling.Primitive.products,rest3,rest4,List.count_cons,List.count_append,List.count_nil] <;> omega
  rcases Inventory.fire_available (CPS1Recycling.Primitive.reactants frame)
    (CPS1Recycling.Primitive.products frame) (.removeTrna trna path.after) rest4 split inv4 with
      ⟨deacylated,paid4,deacylatedInventory⟩
  let rest5 : StockAt frame := [.old (returnedTrna trna),.old .subunit60,
    .old (.actor .eRF1),.old .phosphate,.old .proton] ++ beforeInitiator frame trna ++
      [.old (.freeAA .M),.old .atp,.old (.actor .metRS),.old .gtp,.old (.actor .eIF2)] ++ surplus
  have inv5 : deacylated.Perm ((CPS1Recycling.Primitive.removeMessage path.after).reactants frame ++ rest5) := by
    apply deacylatedInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [CPS1Recycling.Primitive.reactants,CPS1Recycling.Primitive.products,rest4,rest5,
      List.count_cons,List.count_append,List.count_nil]
    omega
  rcases Inventory.fire_available (CPS1Recycling.Primitive.reactants frame)
    (CPS1Recycling.Primitive.products frame) (.removeMessage path.after) rest5 deacylated inv5 with
      ⟨primed,paid5,primedInventory⟩
  let rest6 : StockAt frame := [.primedSmall path.after,.messageCoordinate,.old .subunit60,
    .old (.actor .eRF1),.old .phosphate,.old .proton,.old .gtp,.old (.actor .eIF2)] ++
      remainingTrna frame trna ++ surplus
  have inv6 : primed.Perm (CPS1Recycling.Primitive.chargeNextInitiator.reactants frame ++ rest6) := by
    apply primedInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    have init := (returned_initiator_partition frame trna).count_eq species
    simp only [List.count_cons] at init
    simp only [CPS1Recycling.Primitive.reactants,CPS1Recycling.Primitive.products,Reaction.reactants,
      List.map_cons,List.map_nil,rest5,rest6,List.count_cons,List.count_append,List.count_nil]
    omega
  rcases Inventory.fire_available (CPS1Recycling.Primitive.reactants frame)
    (CPS1Recycling.Primitive.products frame) .chargeNextInitiator rest6 primed inv6 with
      ⟨charged,paid6,chargedInventory⟩
  let rest7 : StockAt frame := [.old .subunit60,.old (.actor .eRF1),.old .phosphate,.old .proton,
    .messageCoordinate,.old .amp,.old .ppi,.old (.actor .metRS)] ++ remainingTrna frame trna ++ surplus
  have inv7 : charged.Perm ((CPS1Recycling.Primitive.captureNext path.after).reactants frame ++ rest7) := by
    apply chargedInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [CPS1Recycling.Primitive.reactants,CPS1Recycling.Primitive.products,Reaction.products,
      List.map_cons,List.map_nil,rest6,rest7,List.count_cons,List.count_append,List.count_nil]
    omega
  rcases Inventory.fire_available (CPS1Recycling.Primitive.reactants frame)
    (CPS1Recycling.Primitive.products frame) (.captureNext path.after) rest7 charged inv7 with
      ⟨captured,paid7,capturedInventory⟩
  dsimp only [CPS1Recycling.coreProgram,List.drop]
  simp only [Inventory.execute,paid3,paid4,paid5,paid6,paid7]
  refine ⟨by trivial,by trivial,by trivial,?_⟩
  simpa only [CPS1Recycling.Primitive.products,CPS1Recycling.coreProducts,rest7,List.append_assoc,
    List.cons_append,List.nil_append] using capturedInventory

theorem retained_after_binding_complete (frame : CPS1Recycling.Frame) (trna : CPS1Recycling.Trna)
    (path : CPS1Recycling.SplitSite) (surplus stock : CPS1Reinitiation.Stock frame)
    (inventory : stock.Perm ((afterBindingInput frame trna).map
      CPS1Reinitiation.Species.retained ++ surplus)) :
    let program := (CPS1Recycling.coreProgram trna path).drop 2
    let result := execute frame program stock
    result.fired = program ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm ((CPS1Recycling.coreProducts frame trna path).map
        CPS1Reinitiation.Species.retained ++ surplus) := by
  have old := native_after_binding_complete frame trna path []
    (afterBindingInput frame trna) (by simp)
  have actual := lift_program frame ((CPS1Recycling.coreProgram trna path).drop 2)
    (afterBindingInput frame trna) surplus stock inventory old.2.2.1
  refine ⟨actual.1,actual.2.1,actual.2.2.1,?_⟩
  apply actual.2.2.2.trans
  simpa only [List.append_nil] using
    (old.2.2.2.map CPS1Reinitiation.Species.retained).append_right surplus

def encode (frame : CPS1Recycling.Frame) : CPS1Recycling.Species frame → CPS1Reinitiation.Species frame
  | .messageCoordinate => .rna Molecules.mrna
  | species => .retained species

/-- Exactly the original five post-binding actions have a source-faithful dictionary image. -/
inductive Supported
  | split (trna : CPS1Recycling.Trna) (path : CPS1Recycling.SplitSite)
  | returnTrna (trna : CPS1Recycling.Trna) (sites : CPS1Recycling.Sites)
  | dischargeRna (sites : CPS1Recycling.Sites)
  | chargeInitiator
  | capture (sites : CPS1Recycling.Sites)

namespace Supported
def primitive : Supported → CPS1Recycling.Primitive
  | .split trna path => CPS1Recycling.splitPrimitive trna path
  | .returnTrna trna sites => .removeTrna trna sites
  | .dischargeRna sites => .removeMessage sites
  | .chargeInitiator => .chargeNextInitiator
  | .capture sites => .captureNext sites

def reaction : Supported → Dictionary.Reaction
  | .split trna path => .split trna path
  | .returnTrna trna sites => .returnTrna trna sites
  | .dischargeRna sites => .dischargeRna sites
  | .chargeInitiator => .chargeInitiator
  | .capture sites => .capture sites
end Supported

theorem supported_reactants (frame : CPS1Recycling.Frame) (step : Supported) :
    step.reaction.reactants frame = (step.primitive.reactants frame).map (encode frame) := by
  cases step with
  | split trna path => cases path <;> rfl
  | returnTrna trna sites => rfl
  | dischargeRna sites => rfl
  | chargeInitiator => rfl
  | capture sites => rfl

theorem supported_products (frame : CPS1Recycling.Frame) (step : Supported) :
    step.reaction.products frame = (step.primitive.products frame).map (encode frame) := by
  cases step with
  | split trna path => cases path <;> rfl
  | returnTrna trna sites => rfl
  | dischargeRna sites => rfl
  | chargeInitiator => rfl
  | capture sites => rfl

theorem lift_dictionary_fire (frame : CPS1Recycling.Frame) (step : Supported)
    (old next : CPS1Recycling.StockAt frame)
    (paid : Inventory.fire (CPS1Recycling.Primitive.reactants frame)
      (CPS1Recycling.Primitive.products frame) step.primitive old = .ok next)
    (surplus stock : CPS1Reinitiation.Stock frame)
    (inventory : stock.Perm (old.map (encode frame) ++ surplus)) :
    ∃ actual, Inventory.fire (Dictionary.Reaction.reactants frame)
      (Dictionary.Reaction.products frame) step.reaction stock = .ok actual ∧
      actual.Perm (next.map (encode frame) ++ surplus) := by
  unfold Inventory.fire at paid
  cases consumed : Inventory.consume (step.primitive.reactants frame) old with
  | error missing => simp [consumed] at paid
  | ok remainder =>
    simp only [consumed,Except.ok.injEq] at paid
    subst next
    have oldInventory := (Inventory.consume_perm _ _ _ consumed).map (encode frame)
    have aligned : stock.Perm (step.reaction.reactants frame ++
        (remainder.map (encode frame) ++ surplus)) := by
      simpa only [supported_reactants,List.map_append,List.append_assoc] using
        inventory.trans (oldInventory.append_right surplus)
    rcases Inventory.fire_available (Dictionary.Reaction.reactants frame)
      (Dictionary.Reaction.products frame) step.reaction _ stock aligned with ⟨actual,fired,after⟩
    exact ⟨actual,fired,by simpa only [supported_products,List.map_append,List.append_assoc] using after⟩

/-- The new dictionary executes the transported paid trace on the actual stock. -/
theorem lift_dictionary_program (frame : CPS1Recycling.Frame) (program : List Supported)
    (old : CPS1Recycling.StockAt frame) (surplus stock : CPS1Reinitiation.Stock frame)
    (inventory : stock.Perm (old.map (encode frame) ++ surplus))
    (complete : (Inventory.execute (CPS1Recycling.Primitive.reactants frame)
      (CPS1Recycling.Primitive.products frame) (program.map Supported.primitive) old).missing = none) :
    let result := Dictionary.execute frame (program.map Supported.reaction) stock
    result.fired = program.map Supported.reaction ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm ((Inventory.execute (CPS1Recycling.Primitive.reactants frame)
        (CPS1Recycling.Primitive.products frame) (program.map Supported.primitive) old).stock.map
          (encode frame) ++ surplus) := by
  induction program generalizing old stock with
  | nil =>
    dsimp only [List.map,Dictionary.execute,Inventory.execute]
    exact ⟨rfl,rfl,rfl,inventory⟩
  | cons step rest ih =>
    cases action : Inventory.fire (CPS1Recycling.Primitive.reactants frame)
        (CPS1Recycling.Primitive.products frame) step.primitive old with
    | error missing =>
      simp only [List.map_cons,Inventory.execute,action] at complete
      contradiction
    | ok next =>
      have afterComplete : (Inventory.execute (CPS1Recycling.Primitive.reactants frame)
          (CPS1Recycling.Primitive.products frame) (rest.map Supported.primitive) next).missing = none := by
        simpa only [List.map_cons,Inventory.execute,action] using complete
      rcases lift_dictionary_fire frame step old next action surplus stock inventory with
        ⟨actual,paid,actualInventory⟩
      have later := ih next actual actualInventory afterComplete
      dsimp only at later ⊢
      simp only [Dictionary.execute,List.map_cons,Inventory.execute,paid,action]
      exact ⟨congrArg (step.reaction :: ·) later.1,later.2⟩

def afterBindingSupported (trna : CPS1Recycling.Trna) (path : CPS1Recycling.SplitSite) : List Supported :=
  [.split trna path,.returnTrna trna path.after,.dischargeRna path.after,.chargeInitiator,.capture path.after]

def afterBindingProgram (trna : CPS1Recycling.Trna) (path : CPS1Recycling.SplitSite) : List Dictionary.Reaction :=
  [.split trna path,.returnTrna trna path.after,.dischargeRna path.after,.chargeInitiator,.capture path.after]

/-- Discharge is an actual new-dictionary firing that returns the same paired editor RNA. -/
theorem dictionary_after_binding_complete (frame : CPS1Recycling.Frame) (trna : CPS1Recycling.Trna)
    (path : CPS1Recycling.SplitSite) (surplus stock : CPS1Reinitiation.Stock frame)
    (inventory : stock.Perm ((afterBindingInput frame trna).map (encode frame) ++ surplus)) :
    let program := afterBindingProgram trna path
    let result := Dictionary.execute frame program stock
    result.fired = program ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm ((CPS1Recycling.coreProducts frame trna path).map (encode frame) ++ surplus) := by
  have old := native_after_binding_complete frame trna path []
    (afterBindingInput frame trna) (by simp)
  have sourceProgram : ((afterBindingSupported trna path).map Supported.primitive) =
      (CPS1Recycling.coreProgram trna path).drop 2 := rfl
  have complete : (Inventory.execute (CPS1Recycling.Primitive.reactants frame)
      (CPS1Recycling.Primitive.products frame)
      ((afterBindingSupported trna path).map Supported.primitive) (afterBindingInput frame trna)).missing = none := by
    rw [sourceProgram]
    exact old.2.2.1
  have actual := lift_dictionary_program frame (afterBindingSupported trna path)
    (afterBindingInput frame trna) surplus stock inventory complete
  refine ⟨actual.1,actual.2.1,actual.2.2.1,?_⟩
  apply actual.2.2.2.trans
  rw [sourceProgram]
  simpa only [List.append_nil] using (old.2.2.2.map (encode frame)).append_right surplus

end CPS1StockRecursion.RecyclingLift
