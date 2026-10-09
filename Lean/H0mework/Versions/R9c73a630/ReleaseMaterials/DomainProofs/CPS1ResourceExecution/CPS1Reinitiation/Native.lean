import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Reinitiation.Program

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1Reinitiation
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

theorem execute_append_paid (frame : CPS1Recycling.Frame) (paidBlock rest : List Primitive)
    (stock : Stock frame)
    (paid : (execute frame paidBlock stock).remaining = [])
    (complete : (execute frame paidBlock stock).missing = none) :
    execute frame (paidBlock ++ rest) stock =
      let first := execute frame paidBlock stock
      let after := execute frame rest first.stock
      ⟨first.fired ++ after.fired,after.remaining,after.stock,after.missing⟩ := by
  induction paidBlock generalizing stock with
  | nil => rfl
  | cons reaction paidBlock ih =>
    cases action : Inventory.fire (Primitive.reactants frame) (Primitive.products frame) reaction stock with
    | error missing =>
      simp only [execute_cons,action] at complete
      contradiction
    | ok next =>
      simp only [execute_cons,action] at paid complete ⊢
      simp only [List.cons_append,execute_cons,action]
      rw [ih next paid complete]

theorem advance_steps_complete (frame : CPS1Recycling.Frame) (sites : CPS1Recycling.Sites)
    (rna : RegisteredRna) (address steps : Nat) (surplus stock : Stock frame)
    (inventory : stock.Perm (.scanning sites rna address ::
      (List.replicate steps (.retained (.old .atp)) ++
        List.replicate steps (.retained (.old .water)) ++ surplus))) :
    let program := (List.range' address steps).map (Primitive.advance sites rna)
    let result := execute frame program stock
    result.fired = program ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm (.scanning sites rna (address+steps) :: workProducts frame steps ++ surplus) := by
  induction steps generalizing address surplus stock with
  | zero =>
    dsimp only
    simp only [List.range'_zero,List.map_nil,execute,Inventory.execute]
    refine ⟨True.intro,True.intro,True.intro,?_⟩
    simpa only [workProducts,Nat.add_zero,List.replicate_zero,List.nil_append,List.append_nil,
      List.singleton_append] using inventory
  | succ steps ih =>
    let remainder : Stock frame := List.replicate steps (.retained (.old .atp)) ++
      List.replicate steps (.retained (.old .water)) ++ surplus
    have firstInventory : stock.Perm ((Primitive.advance sites rna address).reactants frame ++ remainder) := by
      apply inventory.trans
      apply List.perm_iff_count.mpr
      intro species
      simp only [Primitive.reactants,remainder,List.replicate_succ,List.count_cons,List.count_append,List.count_nil]
      omega
    rcases Inventory.fire_available (Primitive.reactants frame) (Primitive.products frame)
      (.advance sites rna address) remainder stock firstInventory with ⟨next,paid,nextInventory⟩
    let waste : Stock frame := [.adp,.retained (.old .phosphate),.retained (.old .proton)]
    have laterInventory : next.Perm (.scanning sites rna (address+1) ::
        (List.replicate steps (.retained (.old .atp)) ++
          List.replicate steps (.retained (.old .water)) ++ (waste ++ surplus))) := by
      apply nextInventory.trans
      apply List.perm_iff_count.mpr
      intro species
      simp only [Primitive.products,remainder,waste,List.count_cons,List.count_append,List.count_nil]
      omega
    have later := ih (address+1) (waste ++ surplus) next laterInventory
    dsimp only at later ⊢
    rw [List.range'_succ,List.map_cons,execute_cons,paid]
    refine ⟨congrArg (Primitive.advance sites rna address :: ·) later.1,later.2.1,later.2.2.1,?_⟩
    apply later.2.2.2.trans
    apply List.perm_iff_count.mpr
    intro species
    have offset : address + 1 + steps = address + (steps+1) := by omega
    rw [offset]
    simp only [workProducts,waste,List.replicate_succ,List.count_cons,List.count_append,List.count_nil]
    omega

def scanInput (frame : CPS1Recycling.Frame) (sites : CPS1Recycling.Sites)
    (rna : RegisteredRna) (address : Nat) : Stock frame :=
  [.retained (.next43 sites),.rna rna,.factor .eIF4A,.factor .eIF4B,.factor .eIF4E,.factor .eIF4G] ++
    List.replicate address (.retained (.old .atp)) ++
    List.replicate (address+1) (.retained (.old .water)) ++ [.retained (.old (.actor .eIF5))]

def scanProducts (frame : CPS1Recycling.Frame) (sites : CPS1Recycling.Sites)
    (rna : RegisteredRna) (address : Nat) : Stock frame :=
  [.committed sites rna address,.retained .eIF3j,.retained (.old (.actor .eIF1)),
    .retained (.old .phosphate),.retained (.old .proton)] ++ workProducts frame address

theorem native_scan_complete (frame : CPS1Recycling.Frame) (sites : CPS1Recycling.Sites)
    (rna : RegisteredRna) (address : Nat)
    (start : Coding.firstStart (Rna.template rna) = some address)
    (codon : startCodonAt rna address = true) (surplus stock : Stock frame)
    (inventory : stock.Perm (scanInput frame sites rna address ++ surplus)) :
    let program := scanProgram sites rna
    let result := execute frame program stock
    result.fired = program ∧ result.remaining = [] ∧ result.missing = none ∧
      result.stock.Perm (scanProducts frame sites rna address ++ surplus) := by
  let rest1 : Stock frame := List.replicate address (.retained (.old .atp)) ++
    List.replicate (address+1) (.retained (.old .water)) ++ [.retained (.old (.actor .eIF5))] ++ surplus
  have inv1 : stock.Perm ((Primitive.recruit sites rna).reactants frame ++ rest1) := by
    simpa only [scanInput,Primitive.reactants,rest1,List.append_assoc] using inventory
  rcases Inventory.fire_available (Primitive.reactants frame) (Primitive.products frame)
    (.recruit sites rna) rest1 stock inv1 with ⟨loaded,paid1,loadedInventory⟩
  let afterScanning : Stock frame := [.retained (.old .water),.retained (.old (.actor .eIF5)),
    .retained .eIF3j] ++ surplus
  have scanInventory : loaded.Perm (.scanning sites rna 0 ::
      (List.replicate address (.retained (.old .atp)) ++
        List.replicate address (.retained (.old .water)) ++ afterScanning)) := by
    apply loadedInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Primitive.products,rest1,afterScanning,List.replicate_succ,
      List.count_cons,List.count_append,List.count_nil]
    omega
  have scanning := advance_steps_complete frame sites rna 0 address afterScanning loaded scanInventory
  let scanned := execute frame
    ((List.range' 0 address).map (Primitive.advance sites rna)) loaded
  let rest2 : Stock frame := [.retained (.old .water),.retained .eIF3j] ++ workProducts frame address ++ surplus
  have inv2 : scanned.stock.Perm ((Primitive.recognize sites rna address).reactants frame ++ rest2) := by
    apply scanning.2.2.2.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Nat.zero_add,Primitive.reactants,codon,ite_true,rest2,afterScanning,
      List.append_nil,List.count_cons,List.count_append,List.count_nil]
    omega
  rcases Inventory.fire_available (Primitive.reactants frame) (Primitive.products frame)
    (.recognize sites rna address) rest2 scanned.stock inv2 with ⟨recognized,paid2,recognizedInventory⟩
  let rest3 : Stock frame := [.retained .eIF3j,.retained (.old (.actor .eIF1))] ++
    workProducts frame address ++ surplus
  have inv3 : recognized.Perm ((Primitive.commit sites rna address).reactants frame ++ rest3) := by
    apply recognizedInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Primitive.reactants,Primitive.products,rest2,rest3,List.count_cons,List.count_append,List.count_nil]
    omega
  rcases Inventory.fire_available (Primitive.reactants frame) (Primitive.products frame)
    (.commit sites rna address) rest3 recognized inv3 with ⟨committed,paid3,committedInventory⟩
  have closing : execute frame [.recognize sites rna address,.commit sites rna address] scanned.stock =
      ⟨[.recognize sites rna address,.commit sites rna address],[],committed,none⟩ := by
    rw [execute_cons,paid2]
    simp only [execute_cons,paid3]
    rfl
  dsimp only
  unfold scanProgram
  rw [start]
  simp only [List.cons_append,List.nil_append,List.range_eq_range']
  simp only [execute_cons,paid1]
  rw [execute_append_paid frame _ _ loaded scanning.2.1 scanning.2.2.1]
  change (Primitive.recruit sites rna :: (scanned.fired ++
      (execute frame [.recognize sites rna address,.commit sites rna address] scanned.stock).fired)) =
      Primitive.recruit sites rna :: ((List.range' 0 address).map (Primitive.advance sites rna) ++
        [.recognize sites rna address,.commit sites rna address]) ∧
    (execute frame [.recognize sites rna address,.commit sites rna address] scanned.stock).remaining = [] ∧
    (execute frame [.recognize sites rna address,.commit sites rna address] scanned.stock).missing = none ∧
    (execute frame [.recognize sites rna address,.commit sites rna address] scanned.stock).stock.Perm
      (scanProducts frame sites rna address ++ surplus)
  rw [closing]
  refine ⟨?_,rfl,rfl,?_⟩
  · rw [scanning.1]
  · apply committedInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Primitive.products,rest3,scanProducts,List.count_cons,List.count_append,List.count_nil]
    omega

end CPS1Reinitiation
