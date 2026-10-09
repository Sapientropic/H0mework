import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.Dictionary
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.Dynamics

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1LocalChemicalExecution.Source
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

inductive RawMaterial
  | molecule (kind : Chemistry.Molecule)
  | processor
  deriving DecidableEq

def RawMaterial.species (frame : CPS1Recycling.Frame) : RawMaterial → Species frame
  | .molecule kind => CPS1LocalChemicalExecution.molecule frame kind
  | .processor => .processor

/-- Local inputs contain an address and a measured row or an applied impulse.
They never contain a chain, contact list, folded state or activity certificate. -/
inductive LocalAction
  | report (address : Nat) (r p : Vec)
  | drive (address : Nat) (force : Vec) (dt mass : ℚ)
  | hydrolyseBond (address : Nat)
  | chemical (step : Chemistry.Step)
  deriving DecidableEq

def LocalAction.material (frame : CPS1Recycling.Frame) : LocalAction → Stock frame
  | .report address r p => [.localRow address r p]
  | .drive address force dt mass => [.impulse address force dt mass]
  | .hydrolyseBond _ => []
  | .chemical _ => []

def LocalAction.reaction (frame : CPS1Recycling.Frame) (state : Chain frame) :
    LocalAction → Reaction frame
  | .report address r p => .report state address r p
  | .drive address force dt mass => .drive state address force dt mass
  | .hydrolyseBond address => .hydrolyseBond state address
  | .chemical step => .chemical step

def LocalAction.next (frame : CPS1Recycling.Frame) (state : Chain frame) : LocalAction → Chain frame
  | .report address r p => state.report frame address r p
  | .drive address force dt mass => ((state.drive? frame address force dt mass).getD (state,0)).1
  | .hydrolyseBond address => state.cleave frame address
  | .chemical _ => state

def chemicalActions : List LocalAction :=
  [.chemical .phosphorylateBicarbonate,.chemical .formCarbamate,.chemical .phosphorylateCarbamate]

def localProgram (frame : CPS1Recycling.Frame) (state : Chain frame)
    (actions : List LocalAction) : List (Reaction frame) :=
  List.rec (motive := fun _ => Chain frame → List (Reaction frame)) (fun _ => [])
    (fun action _ recur current => action.reaction frame current :: recur (action.next frame current)) actions state

def heldChain (frame : CPS1Recycling.Frame) (stock : Stock frame) : Option (Chain frame) :=
  List.rec none (fun species _ found => match species with | .chain state => some state | _ => found) stock

structure Cursor (frame : CPS1Recycling.Frame) where
  stock : Stock frame
  captureRemaining : List (Reaction frame)
  pending : List LocalAction
  stages : List (Execution frame)
  cut : Option (Species frame)

def start (frame : CPS1Recycling.Frame) (actual : CPS1Reinitiation.Stock frame) : Cursor frame :=
  let capture := execute frame [.capture] (actual.map Species.retained)
  ⟨capture.stock,capture.remaining,[],[capture],capture.missing⟩

/-- New local source actions may pay the prerequisite of an old cut. The failed
old action stays pending, and its already supplied material is not fed twice. -/
def advance (frame : CPS1Recycling.Frame) (cursor : Cursor frame)
    (actions : List LocalAction) (feed : List RawMaterial) : Cursor frame :=
  let available := cursor.stock ++ feed.map (RawMaterial.species frame) ++
    actions.flatMap (LocalAction.material frame)
  let state := (heldChain frame available).getD (Chain.initial frame)
  let requested := actions ++ cursor.pending
  let program := cursor.captureRemaining ++ localProgram frame state requested
  let result := execute frame program available
  let localPaid := result.fired.length - cursor.captureRemaining.length
  ⟨result.stock,cursor.captureRemaining.drop result.fired.length,
    requested.drop localPaid,cursor.stages ++ [result],result.missing⟩

structure Occurrence (frame : CPS1Recycling.Frame) where
  previous : CPS1StockRecursion.Source.Observation frame
  current : Cursor frame

def fromCurrent (frame : CPS1Recycling.Frame)
    (previous : CPS1StockRecursion.Source.Observation frame) : Occurrence frame :=
  ⟨previous,start frame previous.current.stock⟩

def actualCapture (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite) (recycleFeed : List CPS1Recycling.RawMaterial)
    (scanFeed : List CPS1Reinitiation.RawMaterial) (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial)
    (depth : Nat) : Option (Σ frame : CPS1Recycling.Frame, Occurrence frame) := do
  let previous ← CPS1StockRecursion.Source.actualRequested edits water additional path
    recycleFeed scanFeed bodyFeed depth
  pure ⟨previous.1,fromCurrent previous.1 previous.2⟩

def execution (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite) (recycleFeed : List CPS1Recycling.RawMaterial)
    (scanFeed : List CPS1Reinitiation.RawMaterial) (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial)
    (depth : Nat) (actions : List LocalAction) (feed : List RawMaterial) :
    Option (Σ frame : CPS1Recycling.Frame, Occurrence frame) := do
  let previous ← actualCapture edits water additional path recycleFeed scanFeed bodyFeed depth
  pure ⟨previous.1,{previous.2 with
    current := advance previous.1 previous.2.current (actions ++ chemicalActions) feed}⟩

theorem start_consumes_current (frame : CPS1Recycling.Frame) (actual : CPS1Reinitiation.Stock frame)
    (present : Actual.species frame ∈ actual) :
    (start frame actual).stock.Perm (.chain (Chain.initial frame) ::
      (actual.erase (Actual.species frame)).map Species.retained) ∧
    (start frame actual).captureRemaining = [] ∧ (start frame actual).cut = none := by
  have paid := capture_from_actual frame actual present
  exact ⟨paid.2.2.2,paid.2.1,paid.2.2.1⟩

theorem actual_capture_complete (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite)
    (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (bodyFeed bodyExtra : List CPS1Reinitiation.Handover.RawMaterial)
    (bodyRaw : bodyFeed.Perm (CPS1Reinitiation.Handover.rawFuel Program.originalPeptide.2 ++ bodyExtra))
    (depth : Nat) :
    let frame := CPS1Recycling.Source.frame edits water additional
    let recycled := CPS1Recycling.run frame (CPS1Recycling.productiveEvents path) recycleFeed
    let prior := CPS1Reinitiation.run frame recycled path.after Molecules.mrna scanFeed
    let previous := CPS1Reinitiation.Handover.execute frame
      (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna 151 Program.originalPeptide.2)
      (prior.stock ++ bodyFeed.map (CPS1Reinitiation.Handover.RawMaterial.species frame))
    let result := CPS1StockRecursion.Source.requested frame path depth previous.stock
    actualCapture edits water additional path recycleFeed scanFeed bodyFeed depth =
      some ⟨frame,fromCurrent frame result⟩ ∧
    (start frame result.current.stock).stock.Perm (.chain (Chain.initial frame) ::
      (result.current.stock.erase (Actual.species frame)).map Species.retained) ∧
    (start frame result.current.stock).captureRemaining = [] ∧
    (start frame result.current.stock).cut = none := by
  have previous := CPS1StockRecursion.Source.actual_requested_complete edits water additional path
    recycleFeed recycleExtra recyclingRaw scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw depth
  have present := Actual.current_free_cps1 edits water additional path
    recycleFeed recycleExtra recyclingRaw scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw depth
  dsimp only
  refine ⟨?_,start_consumes_current _ _ present⟩
  rw [actualCapture,previous.1]
  rfl

def chemistryProgram (frame : CPS1Recycling.Frame) : List (Reaction frame) :=
  [.chemical .phosphorylateBicarbonate,.chemical .formCarbamate,.chemical .phosphorylateCarbamate]

def chemistryInput (frame : CPS1Recycling.Frame) : Stock frame :=
  Chemistry.ammoniaInput.map (molecule frame)

def chemistryProducts (frame : CPS1Recycling.Frame) : Stock frame :=
  Chemistry.ammoniaProducts.map (molecule frame)

theorem execute_cons (frame : CPS1Recycling.Frame) (reaction : Reaction frame)
    (rest : List (Reaction frame)) (stock : Stock frame) :
    execute frame (reaction :: rest) stock =
      match Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock with
      | .error missing => ⟨[],reaction::rest,stock,some missing⟩
      | .ok next =>
        let after := execute frame rest next
        ⟨reaction::after.fired,after.remaining,after.stock,after.missing⟩ := by
  unfold execute
  rw [Inventory.execute_cons]
  cases Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock <;> rfl

/-- The three registered small-molecule reactions are subordinate to the
physical processing mouth. No enzyme state is manufactured by this theorem. -/
theorem chemistry_complete (frame : CPS1Recycling.Frame) (surplus stock : Stock frame)
    (inventory : stock.Perm (chemistryInput frame ++ surplus)) :
    let result := execute frame (chemistryProgram frame) stock
    result.fired = chemistryProgram frame ∧ result.remaining = [] ∧ result.missing = none ∧
    result.stock.Perm (chemistryProducts frame ++ surplus) := by
  let rest1 : Stock frame := [molecule frame .atp,molecule frame .ammonia] ++ surplus
  have inv1 : stock.Perm ((Reaction.chemical .phosphorylateBicarbonate).reactants frame ++ rest1) := by
    apply inventory.trans
    simp only [chemistryInput,Chemistry.ammoniaInput,List.map_cons,List.map_nil,
      Reaction.reactants,Chemistry.Step.reactants,rest1]
    apply List.perm_iff_count.mpr
    intro s
    simp only [List.count_cons,List.count_append,List.count_nil]
    omega
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame)
    (.chemical .phosphorylateBicarbonate) rest1 stock inv1 with ⟨first,paid1,gen1⟩
  let rest2 : Stock frame := [molecule frame .adp,molecule frame .atp] ++ surplus
  have inv2 : first.Perm ((Reaction.chemical .formCarbamate).reactants frame ++ rest2) := by
    apply gen1.trans
    simp only [Reaction.products,Reaction.reactants,Chemistry.Step.products,Chemistry.Step.reactants,
      List.map_cons,List.map_nil,rest1,rest2]
    apply List.perm_iff_count.mpr
    intro s
    simp only [List.count_cons,List.count_append,List.count_nil]
    omega
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame)
    (.chemical .formCarbamate) rest2 first inv2 with ⟨second,paid2,gen2⟩
  let rest3 : Stock frame := [molecule frame .phosphate,molecule frame .proton,molecule frame .adp] ++ surplus
  have inv3 : second.Perm ((Reaction.chemical .phosphorylateCarbamate).reactants frame ++ rest3) := by
    apply gen2.trans
    simp only [Reaction.products,Reaction.reactants,Chemistry.Step.products,Chemistry.Step.reactants,
      List.map_cons,List.map_nil,rest2,rest3]
    apply List.perm_iff_count.mpr
    intro s
    simp only [List.count_cons,List.count_append,List.count_nil]
    omega
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame)
    (.chemical .phosphorylateCarbamate) rest3 second inv3 with ⟨third,paid3,gen3⟩
  have resultStock : third.Perm (chemistryProducts frame ++ surplus) := by
    apply gen3.trans
    simp only [Reaction.products,Chemistry.Step.products,List.map_cons,List.map_nil,
      chemistryProducts,Chemistry.ammoniaProducts,rest3]
    apply List.perm_iff_count.mpr
    intro s
    simp only [List.count_cons,List.count_append,List.count_nil]
    omega
  dsimp only
  simp only [chemistryProgram,execute_cons,paid1,paid2,paid3]
  exact ⟨rfl,rfl,rfl,resultStock⟩

def chemicalAdvance (frame : CPS1Recycling.Frame) (cursor : Cursor frame)
    (feed : List RawMaterial) : Execution frame :=
  execute frame (chemistryProgram frame) (cursor.stock ++ feed.map (RawMaterial.species frame))

theorem chemistry_from_actual_chain (frame : CPS1Recycling.Frame)
    (actual : CPS1Reinitiation.Stock frame) (present : Actual.species frame ∈ actual) :
    let result := execute frame (chemistryProgram frame) ((start frame actual).stock ++ chemistryInput frame)
    result.fired = chemistryProgram frame ∧ result.remaining = [] ∧ result.missing = none ∧
    result.stock.Perm (chemistryProducts frame ++ .chain (Chain.initial frame) ::
      (actual.erase (Actual.species frame)).map Species.retained) := by
  have captured := start_consumes_current frame actual present
  let surplus := .chain (Chain.initial frame) :: (actual.erase (Actual.species frame)).map Species.retained
  have inventory : ((start frame actual).stock ++ chemistryInput frame).Perm
      (chemistryInput frame ++ surplus) :=
    (captured.1.append_right _).trans (List.perm_append_comm)
  exact chemistry_complete frame surplus _ inventory

theorem localProgram_cons (frame : CPS1Recycling.Frame) (state : Chain frame)
    (action : LocalAction) (rest : List LocalAction) :
    localProgram frame state (action :: rest) =
      action.reaction frame state :: localProgram frame (action.next frame state) rest := rfl

theorem localProgram_chemical (frame : CPS1Recycling.Frame) (state : Chain frame) :
    localProgram frame state chemicalActions = chemistryProgram frame := rfl

def localActions (address bond : Nat) (r p force : Vec) (dt mass : ℚ) : List LocalAction :=
  [.report address r p,.drive address force dt mass,.hydrolyseBond bond] ++ chemicalActions

def localInput (frame : CPS1Recycling.Frame) (address : Nat) (r p force : Vec) (dt mass : ℚ) : Stock frame :=
  [.localRow address r p,.impulse address force dt mass,molecule frame .water,.processor] ++ chemistryInput frame

def driven (frame : CPS1Recycling.Frame) (address : Nat) (r p force : Vec) (dt mass : ℚ) : Chain frame :=
  let nextP := p.add (force.scale dt)
  let nextR := (r.add (p.scale (dt/mass))).add (force.scale (dt*dt/(2*mass)))
  ((Chain.initial frame).report frame address nextR nextP).recordInertia frame address mass

def localProducts (frame : CPS1Recycling.Frame) (address bond : Nat)
    (r p force : Vec) (dt mass : ℚ) : Stock frame :=
  let nextR := (r.add (p.scale (dt/mass))).add (force.scale (dt*dt/(2*mass)))
  [.chain ((driven frame address r p force dt mass).cleave frame bond),.processor,
    .spentImpulse address force dt mass (force.dot (nextR.sub r))] ++ chemistryProducts frame

theorem reported_position (frame : CPS1Recycling.Frame) (state : Chain frame)
    (address : Nat) (r p : Vec) :
    (state.report frame address r p).position frame address = some r ∧
      (state.report frame address r p).momentum frame address = some p := by
  constructor <;> simp [Chain.report,Chain.position,Chain.momentum]

/-- The reported initial restriction, actual impulse and paid source-bond cleavage
are followed by the three chemical reactions in one inventory execution. -/
theorem local_update_complete (frame : CPS1Recycling.Frame) (actual : CPS1Reinitiation.Stock frame)
    (present : Actual.species frame ∈ actual) (address bond : Nat)
    (residue : address < (Actual.cps1 frame).word.length)
    (bondPresent : bond < (Actual.cps1 frame).2.length)
    (r p force : Vec) (dt mass : ℚ) (positive : 0 < mass) (forward : 0 ≤ dt)
    (extra stock : Stock frame)
    (input : stock.Perm ((start frame actual).stock ++ localInput frame address r p force dt mass ++ extra)) :
    let result := execute frame (localProgram frame (Chain.initial frame) (localActions address bond r p force dt mass))
      stock
    result.fired = localProgram frame (Chain.initial frame) (localActions address bond r p force dt mass) ∧
    result.remaining = [] ∧ result.missing = none ∧
    result.stock.Perm (localProducts frame address bond r p force dt mass ++
      (actual.erase (Actual.species frame)).map Species.retained ++ extra) := by
  let state := (Chain.initial frame).report frame address r p
  let afterDrive := driven frame address r p force dt mass
  let work := force.dot (((r.add (p.scale (dt/mass))).add (force.scale (dt*dt/(2*mass)))).sub r)
  let old := (actual.erase (Actual.species frame)).map Species.retained
  let rest1 : Stock frame := [.impulse address force dt mass,molecule frame .water,.processor] ++
    chemistryInput frame ++ old ++ extra
  have captured := start_consumes_current frame actual present
  have inv1 : stock.Perm
      ((Reaction.report (Chain.initial frame) address r p).reactants frame ++ rest1) := by
    apply input.trans
    apply ((captured.1.append_right _).append_right _).trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Reaction.reactants,if_pos residue,Chain.reportConsistent,Chain.position,Chain.momentum,
      Chain.initial,List.find?_nil,Option.map_none,Option.isNone_none,Bool.true_or,Bool.and_self,
      ite_true,List.append_nil,localInput,rest1,old,List.count_append,List.count_cons,List.count_nil]
    omega
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame)
    (.report (Chain.initial frame) address r p) rest1 _ inv1 with ⟨reported,paid1,gen1⟩
  have coordinates := reported_position frame (Chain.initial frame) address r p
  have action := Dynamics.source_drive frame state address r p force dt mass positive forward rfl
    coordinates.1 coordinates.2
  let rest2 : Stock frame := [molecule frame .water,.processor] ++ chemistryInput frame ++ old ++ extra
  have inv2 : reported.Perm ((Reaction.drive state address force dt mass).reactants frame ++ rest2) := by
    apply gen1.trans
    simp only [Reaction.products,Reaction.reactants,action,Option.isSome_some,ite_true,List.append_nil]
    exact List.Perm.refl _
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame)
    (.drive state address force dt mass) rest2 reported inv2 with ⟨moved,paid2,gen2⟩
  let rest3 : Stock frame := [.spentImpulse address force dt mass work] ++ chemistryInput frame ++ old ++ extra
  have actualBond : bond ∈ afterDrive.bonds := List.mem_range.mpr bondPresent
  have inv3 : moved.Perm ((Reaction.hydrolyseBond afterDrive bond).reactants frame ++ rest3) := by
    apply gen2.trans
    simp only [Reaction.products,Reaction.reactants,action,Option.getD_some,if_pos actualBond,List.append_nil,
      rest2,rest3]
    have sameState : (state.report frame address
        ((r.add (p.scale (dt/mass))).add (force.scale (dt*dt/(2*mass))))
        (p.add (force.scale dt))).recordInertia frame address mass = afterDrive := by
      simp [state,afterDrive,driven,Chain.report,List.filter_filter]
    rw [sameState]
    apply List.perm_iff_count.mpr
    intro species
    simp only [work,List.count_append,List.count_cons,List.count_nil]
    omega
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame)
    (.hydrolyseBond afterDrive bond) rest3 moved inv3 with ⟨processed,paid3,gen3⟩
  let surplus : Stock frame := [.chain (afterDrive.cleave frame bond),.processor,
    .spentImpulse address force dt mass work] ++ old ++ extra
  have inv4 : processed.Perm (chemistryInput frame ++ surplus) := by
    apply gen3.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Reaction.products,rest3,surplus,List.count_append,List.count_cons,List.count_nil]
    omega
  have chemistry := chemistry_complete frame surplus processed inv4
  have program : localProgram frame (Chain.initial frame) (localActions address bond r p force dt mass) =
      [.report (Chain.initial frame) address r p,.drive state address force dt mass,
        .hydrolyseBond afterDrive bond] ++ chemistryProgram frame := by
    simp only [localActions,List.cons_append,List.nil_append,localProgram_cons,
      LocalAction.reaction,LocalAction.next,localProgram_chemical]
    change .report (Chain.initial frame) address r p :: .drive state address force dt mass ::
      .hydrolyseBond ((state.drive? frame address force dt mass).getD (state,0)).1 bond ::
      chemistryProgram frame = _
    rw [action]
    simp only [Option.getD_some]
    simp [state,afterDrive,driven,Chain.report,List.filter_filter]
  dsimp only
  rw [program]
  simp only [List.cons_append,execute_cons,paid1,paid2,paid3]
  refine ⟨congrArg (fun trace => .report (Chain.initial frame) address r p ::
    .drive state address force dt mass :: .hydrolyseBond afterDrive bond :: trace) chemistry.1,
    chemistry.2.1,chemistry.2.2.1,?_⟩
  apply chemistry.2.2.2.trans
  apply List.perm_iff_count.mpr
  intro species
  simp only [localProducts,surplus,afterDrive,work,old,List.count_append,List.count_cons,List.count_nil]
  omega

theorem local_stock_balance (frame : CPS1Recycling.Frame) (state : Chain frame)
    (actions : List LocalAction) (stock : Stock frame) (species : Species frame) :
    let result := execute frame (localProgram frame state actions) stock
    stock.count species + (Inventory.credit (Reaction.products frame) result.fired).count species =
      result.stock.count species + (Inventory.debit (Reaction.reactants frame) result.fired).count species :=
  Inventory.execution_balance (Reaction.reactants frame) (Reaction.products frame) _ stock species

theorem heldChain_append (frame : CPS1Recycling.Frame) (state : Chain frame)
    (stock extra : Stock frame) (held : heldChain frame stock = some state) :
    heldChain frame (stock ++ extra) = some state := by
  induction stock with
  | nil => cases held
  | cons species rest ih => cases species <;> first | exact held | exact ih held

theorem heldChain_start (frame : CPS1Recycling.Frame) (actual : CPS1Reinitiation.Stock frame)
    (present : Actual.species frame ∈ actual) :
    heldChain frame (start frame actual).stock = some (Chain.initial frame) := by
  have stock := (List.perm_cons_erase present).map (Species.retained (frame := frame))
  have aligned : (actual.map Species.retained).Perm
      ((Reaction.capture).reactants frame ++ (actual.erase (Actual.species frame)).map Species.retained) := by
    simpa only [Reaction.reactants,List.map_cons,List.singleton_append] using stock
  rcases Inventory.fire_available (Reaction.reactants frame) (Reaction.products frame) .capture
    ((actual.erase (Actual.species frame)).map Species.retained) (actual.map Species.retained) aligned with
      ⟨next,paid,_⟩
  have head : heldChain frame next = some (Chain.initial frame) := by
    unfold Inventory.fire at paid
    cases consumed : Inventory.consume (Reaction.capture.reactants frame) (actual.map Species.retained) with
    | error missing => simp [consumed] at paid
    | ok remainder =>
      simp only [consumed,Except.ok.injEq] at paid
      subst next
      rfl
  change heldChain frame (execute frame [.capture] (actual.map Species.retained)).stock = _
  simp only [execute,Inventory.execute,paid]
  exact head

def localFuel : List RawMaterial :=
  [.molecule .water,.processor] ++ Chemistry.ammoniaInput.map RawMaterial.molecule

theorem localFuel_species (frame : CPS1Recycling.Frame) :
    localFuel.map (RawMaterial.species frame) =
      [molecule frame .water,.processor] ++ chemistryInput frame := rfl

theorem actual_local_update (frame : CPS1Recycling.Frame) (actual : CPS1Reinitiation.Stock frame)
    (present : Actual.species frame ∈ actual) (address bond : Nat)
    (residue : address < (Actual.cps1 frame).word.length)
    (bondPresent : bond < (Actual.cps1 frame).2.length)
    (r p force : Vec) (dt mass : ℚ) (positive : 0 < mass) (forward : 0 ≤ dt)
    (feed rawExtra : List RawMaterial) (raw : feed.Perm (localFuel ++ rawExtra)) :
    let result := advance frame (start frame actual) (localActions address bond r p force dt mass) feed
    result.stock.Perm (localProducts frame address bond r p force dt mass ++
      (actual.erase (Actual.species frame)).map Species.retained ++ rawExtra.map (RawMaterial.species frame)) ∧
    result.captureRemaining = [] ∧ result.pending = [] ∧ result.cut = none ∧
    result.stages = (start frame actual).stages ++
      [execute frame (localProgram frame (Chain.initial frame) (localActions address bond r p force dt mass))
        ((start frame actual).stock ++ feed.map (RawMaterial.species frame) ++
          (localActions address bond r p force dt mass).flatMap (LocalAction.material frame))] := by
  let available := (start frame actual).stock ++ feed.map (RawMaterial.species frame) ++
    (localActions address bond r p force dt mass).flatMap (LocalAction.material frame)
  have captured := start_consumes_current frame actual present
  have held : heldChain frame available = some (Chain.initial frame) :=
    heldChain_append frame _ _ _ (heldChain_append frame _ _ _ (heldChain_start frame actual present))
  have input : available.Perm ((start frame actual).stock ++ localInput frame address r p force dt mass ++
      rawExtra.map (RawMaterial.species frame)) := by
    apply (((raw.map (RawMaterial.species frame)).append_left _).append_right _).trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [List.map_append,localFuel_species,localActions,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,chemicalActions,LocalAction.material,List.append_nil,
      localInput,List.count_append,List.count_cons,List.count_nil]
    omega
  have paid := local_update_complete frame actual present address bond residue bondPresent r p force dt mass
    positive forward (rawExtra.map (RawMaterial.species frame)) available input
  have initialPending : (start frame actual).pending = [] := rfl
  dsimp only [available] at held
  dsimp only
  simp only [advance,held,Option.getD_some,captured.2.1,initialPending,List.append_nil,List.nil_append]
  refine ⟨paid.2.2.2,?_,?_,paid.2.2.1,?_⟩
  · exact List.drop_nil
  · rw [paid.1]
    simp only [List.length_nil,Nat.sub_zero,localActions,List.cons_append,List.nil_append,
      localProgram_cons,localProgram_chemical,chemistryProgram,List.length_cons,List.length_nil,
      List.drop_succ_cons]
    rfl
  · exact True.intro

theorem local_cut_preserves_remaining (frame : CPS1Recycling.Frame) (state : Chain frame)
    (actions : List LocalAction) (stock : Stock frame) (missing : Species frame)
    (cut : (execute frame (localProgram frame state actions) stock).missing = some missing) :
    ∃ reaction rest, (execute frame (localProgram frame state actions) stock).remaining = reaction :: rest ∧
      (execute frame (localProgram frame state actions) stock).stock.count missing <
        (reaction.reactants frame).count missing :=
  Inventory.execution_cut (Reaction.reactants frame) (Reaction.products frame) _ stock missing cut

structure LocalChemicalContract : Prop where
  actualCapture : type_of% actual_capture_complete
  localUpdate : type_of% actual_local_update
  sourceBond : type_of% hydrolyse_source_bond
  work : type_of% Dynamics.source_drive
  chemistry : type_of% chemistry_complete
  chemistryBalance : type_of% Chemistry.atomic_charge_balance
  fragments : type_of% components_all_material
  inventory : type_of% local_stock_balance
  cut : type_of% local_cut_preserves_remaining

theorem sourceGeneratedLocalChemical : LocalChemicalContract :=
  ⟨actual_capture_complete,actual_local_update,hydrolyse_source_bond,Dynamics.source_drive,
    chemistry_complete,Chemistry.atomic_charge_balance,components_all_material,
    local_stock_balance,local_cut_preserves_remaining⟩

end CPS1LocalChemicalExecution.Source
