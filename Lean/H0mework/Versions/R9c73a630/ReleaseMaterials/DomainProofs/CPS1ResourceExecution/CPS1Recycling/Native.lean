import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Recycling.Program

set_option autoImplicit false
set_option maxHeartbeats 0

namespace CPS1Recycling
open CPS1ResourceExecution

def beforeInitiator (frame : Frame) : Trna → StockAt frame
  | .initiator => []
  | .elongator _ => [.old .initiatorTRNA]

def remainingTrna (frame : Frame) : Trna → StockAt frame
  | .initiator => []
  | .elongator aa => [.old (.tRNA aa)]

def splitPrimitive (trna : Trna) : SplitSite → Primitive
  | .first => .splitHydrolyzingFirst trna
  | .second => .splitHydrolyzingSecond trna

def coreProgram (trna : Trna) (site : SplitSite) : List Primitive :=
  [.engageControl trna,.engageWork trna,splitPrimitive trna site,
    .removeTrna trna site.after,.removeMessage site.after,
    .chargeNextInitiator,.captureNext site.after]

def coreInput (frame : Frame) (trna : Trna) : StockAt frame :=
  [.old (postSpecies trna),.abce1 emptySites,.old .atp,.old .atp,.old .water,
    .old (.actor .eIF1),.old (.actor .eIF1A),.old (.actor .eIF3),.eIF3j] ++
      beforeInitiator frame trna ++
        [.old (.freeAA .M),.old .atp,.old (.actor .metRS),.old .gtp,.old (.actor .eIF2)]

def coreProducts (frame : Frame) (trna : Trna) (site : SplitSite) : StockAt frame :=
  [.next43 site.after,.old .subunit60,.old (.actor .eRF1),.old .phosphate,.old .proton,
    .messageCoordinate,.old .amp,.old .ppi,.old (.actor .metRS)] ++ remainingTrna frame trna

theorem productive_compiles (frame : Frame) (site : SplitSite) :
    compile frame (productiveEvents site) = coreProgram (sourceTrna frame) site := by
  cases site <;> rfl

theorem returned_initiator_partition (frame : Frame) (trna : Trna) :
    ((Species.old (returnedTrna trna) : Species frame) :: beforeInitiator frame trna).Perm
      (.old .initiatorTRNA :: remainingTrna frame trna) := by
  cases trna with
  | initiator => exact List.Perm.refl _
  | elongator aa => exact List.Perm.swap _ _ []

/-- A raw postTC and raw resources pay all seven actions, for either registered ATPase-site path. -/
theorem native_core_complete (frame : Frame) (trna : Trna) (site : SplitSite)
    (surplus stock : StockAt frame) (inventory : stock.Perm (coreInput frame trna ++ surplus)) :
    let result := Inventory.execute (Primitive.reactants frame) (Primitive.products frame)
      (coreProgram trna site) stock
    result.fired = coreProgram trna site ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm (coreProducts frame trna site ++ surplus) := by
  let rest1 : StockAt frame := [.old .atp,.old .water,.old (.actor .eIF1),
    .old (.actor .eIF1A),.old (.actor .eIF3),.eIF3j] ++ beforeInitiator frame trna ++
      [.old (.freeAA .M),.old .atp,.old (.actor .metRS),.old .gtp,.old (.actor .eIF2)] ++ surplus
  have inv1 : stock.Perm ((Primitive.engageControl trna).reactants frame ++ rest1) := by
    simpa only [coreInput,Primitive.reactants,rest1,List.append_assoc,List.cons_append,List.nil_append] using inventory
  rcases Inventory.fire_available (Primitive.reactants frame) (Primitive.products frame)
    (.engageControl trna) rest1 stock inv1 with ⟨bound,paid1,boundInventory⟩
  let rest2 : StockAt frame := [.old .water,.old (.actor .eIF1),
    .old (.actor .eIF1A),.old (.actor .eIF3),.eIF3j] ++ beforeInitiator frame trna ++
      [.old (.freeAA .M),.old .atp,.old (.actor .metRS),.old .gtp,.old (.actor .eIF2)] ++ surplus
  have inv2 : bound.Perm ((Primitive.engageWork trna).reactants frame ++ rest2) := by
    simpa only [Primitive.reactants,Primitive.products,rest1,rest2,List.append_assoc,
      List.cons_append,List.nil_append] using boundInventory
  rcases Inventory.fire_available (Primitive.reactants frame) (Primitive.products frame)
    (.engageWork trna) rest2 bound inv2 with ⟨closed,paid2,closedInventory⟩
  let rest3 : StockAt frame := [.old (.actor .eIF1),.old (.actor .eIF1A),
    .old (.actor .eIF3),.eIF3j] ++ beforeInitiator frame trna ++
      [.old (.freeAA .M),.old .atp,.old (.actor .metRS),.old .gtp,.old (.actor .eIF2)] ++ surplus
  have inv3 : closed.Perm ((splitPrimitive trna site).reactants frame ++ rest3) := by
    cases site <;> simpa only [splitPrimitive,Primitive.reactants,Primitive.products,rest2,rest3,
      List.append_assoc,List.cons_append,List.nil_append] using closedInventory
  rcases Inventory.fire_available (Primitive.reactants frame) (Primitive.products frame)
    (splitPrimitive trna site) rest3 closed inv3 with ⟨split,paid3,splitInventory⟩
  let rest4 : StockAt frame := [.old .subunit60,.old (.actor .eRF1),.old .phosphate,
    .old .proton,.eIF3j] ++ beforeInitiator frame trna ++
      [.old (.freeAA .M),.old .atp,.old (.actor .metRS),.old .gtp,.old (.actor .eIF2)] ++ surplus
  have inv4 : split.Perm ((Primitive.removeTrna trna site.after).reactants frame ++ rest4) := by
    apply splitInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    cases site <;> simp only [splitPrimitive,SplitSite.after,Primitive.reactants,Primitive.products,
      rest3,rest4,List.count_cons,List.count_append,List.count_nil] <;> omega
  rcases Inventory.fire_available (Primitive.reactants frame) (Primitive.products frame)
    (.removeTrna trna site.after) rest4 split inv4 with ⟨deacylated,paid4,deacylatedInventory⟩
  let rest5 : StockAt frame := [.old (returnedTrna trna),.old .subunit60,
    .old (.actor .eRF1),.old .phosphate,.old .proton] ++ beforeInitiator frame trna ++
      [.old (.freeAA .M),.old .atp,.old (.actor .metRS),.old .gtp,.old (.actor .eIF2)] ++ surplus
  have inv5 : deacylated.Perm ((Primitive.removeMessage site.after).reactants frame ++ rest5) := by
    apply deacylatedInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Primitive.reactants,Primitive.products,rest4,rest5,List.count_cons,List.count_append,List.count_nil]
    omega
  rcases Inventory.fire_available (Primitive.reactants frame) (Primitive.products frame)
    (.removeMessage site.after) rest5 deacylated inv5 with ⟨primed,paid5,primedInventory⟩
  let rest6 : StockAt frame := [.primedSmall site.after,.messageCoordinate,.old .subunit60,
    .old (.actor .eRF1),.old .phosphate,.old .proton,.old .gtp,.old (.actor .eIF2)] ++
      remainingTrna frame trna ++ surplus
  have inv6 : primed.Perm (Primitive.chargeNextInitiator.reactants frame ++ rest6) := by
    apply primedInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    have init := (returned_initiator_partition frame trna).count_eq species
    simp only [List.count_cons] at init
    simp only [Primitive.reactants,Primitive.products,Reaction.reactants,List.map_cons,List.map_nil,
      rest5,rest6,List.count_cons,List.count_append,List.count_nil]
    omega
  rcases Inventory.fire_available (Primitive.reactants frame) (Primitive.products frame)
    .chargeNextInitiator rest6 primed inv6 with ⟨charged,paid6,chargedInventory⟩
  let rest7 : StockAt frame := [.old .subunit60,.old (.actor .eRF1),.old .phosphate,.old .proton,
    .messageCoordinate,.old .amp,.old .ppi,.old (.actor .metRS)] ++ remainingTrna frame trna ++ surplus
  have inv7 : charged.Perm ((Primitive.captureNext site.after).reactants frame ++ rest7) := by
    apply chargedInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Primitive.reactants,Primitive.products,Reaction.products,List.map_cons,List.map_nil,
      rest6,rest7,List.count_cons,List.count_append,List.count_nil]
    omega
  rcases Inventory.fire_available (Primitive.reactants frame) (Primitive.products frame)
    (.captureNext site.after) rest7 charged inv7 with ⟨captured,paid7,capturedInventory⟩
  simp only [coreProgram,Inventory.execute,paid1,paid2,paid3,paid4,paid5,paid6,paid7]
  refine ⟨by trivial,by trivial,by trivial,?_⟩
  simpa only [Inventory.execute,Primitive.products,coreProducts,rest7,List.append_assoc,
    List.cons_append,List.nil_append] using capturedInventory

end CPS1Recycling
