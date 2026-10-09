import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1StockRecursion.Native
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1StockRecursion.Initial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1StockRecursion.Source
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

/-- The canonical one-cycle word is decoded from the actual registered raw RNA. -/
def programFromSource? (path : CPS1Recycling.SplitSite) : Option (List Dictionary.Reaction) := do
  let rna ← Rna.parse SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.rawMrna
  let address ← Coding.firstStart (Rna.template rna)
  let peptide ← CPS1ResourceExecution.Program.peptideFromRna?
    SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.rawMrna
  if peptide.1 = AA.M then pure (Dictionary.recycleProgram peptide.2 path ++
    (CPS1Reinitiation.scanProgram path.after rna).map Dictionary.Reaction.scan ++
    (CPS1Reinitiation.Handover.fullProgram path rna address peptide.2).map Dictionary.Reaction.body)
  else none

def program (path : CPS1Recycling.SplitSite) : List Dictionary.Reaction :=
  (programFromSource? path).getD []

def rawSourceFuel? : Option (List Dictionary.RawMaterial) :=
  (CPS1ResourceExecution.Program.peptideFromRna?
    SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.rawMrna).map
      (fun peptide => Dictionary.rawFuel peptide.2)

def rawSourceFuel : List Dictionary.RawMaterial := rawSourceFuel?.getD []

theorem source_program (path : CPS1Recycling.SplitSite) :
    programFromSource? path = some (Dictionary.program CPS1ResourceExecution.Program.originalPeptide.2 path) := by
  unfold programFromSource?
  rw [Molecules.complete_original_chemical_words.2]
  change (do
    let address ← Coding.firstStart (Rna.template Molecules.mrna)
    let peptide ← CPS1ResourceExecution.Program.peptideFromRna?
      SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.rawMrna
    if peptide.1 = AA.M then pure (Dictionary.recycleProgram peptide.2 path ++
      (CPS1Reinitiation.scanProgram path.after Molecules.mrna).map Dictionary.Reaction.scan ++
      (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna address peptide.2).map Dictionary.Reaction.body)
    else none) = _
  rw [CPS1Reinitiation.Source.original_start_and_context.1,CPS1ResourceExecution.Program.original_peptide_generated]
  change (if CPS1ResourceExecution.Program.originalPeptide.1 = AA.M then _ else none) = _
  rw [if_pos (show CPS1ResourceExecution.Program.originalPeptide.1 = AA.M from by decide +kernel)]
  rfl

theorem source_program_generated (path : CPS1Recycling.SplitSite) :
    program path = Dictionary.program CPS1ResourceExecution.Program.originalPeptide.2 path := by
  rw [program,source_program]; rfl

theorem raw_source_fuel_generated :
    rawSourceFuel? = some (Dictionary.rawFuel CPS1ResourceExecution.Program.originalPeptide.2) := by
  rw [rawSourceFuel?,CPS1ResourceExecution.Program.original_peptide_generated]
  rfl

theorem source_fuel_generated :
    rawSourceFuel = Dictionary.rawFuel CPS1ResourceExecution.Program.originalPeptide.2 := by
  rw [rawSourceFuel,raw_source_fuel_generated]; rfl

structure Cursor (frame : CPS1Recycling.Frame) where
  stock : Dictionary.Stock frame
  pending : List Dictionary.Reaction
  completed : Nat
  cut : Option (CPS1Reinitiation.Species frame)

def start (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (actualStock : Dictionary.Stock frame) : Cursor frame :=
  ⟨actualStock,program path,0,none⟩

def supplied (frame : CPS1Recycling.Frame) (current : Cursor frame)
    (feed : List Dictionary.RawMaterial) : Dictionary.Stock frame :=
  current.stock ++ feed.map (Dictionary.RawMaterial.species frame)

def execution (frame : CPS1Recycling.Frame) (current : Cursor frame)
    (feed : List Dictionary.RawMaterial) : Dictionary.Execution frame :=
  Dictionary.execute frame current.pending (supplied frame current feed)

/-- Short supply retains the actual cut stock and pending suffix; completion generates the
next source-decoded one-cycle word, with no fresh protein or recycled carrier. -/
def advance (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite) (current : Cursor frame)
    (feed : List Dictionary.RawMaterial) : Cursor frame :=
  let result := execution frame current feed
  ⟨result.stock,if result.missing = none then program path else result.remaining,
    current.completed + (if result.missing = none then 1 else 0),result.missing⟩

structure Stage (frame : CPS1Recycling.Frame) where
  before : Cursor frame
  feed : List Dictionary.RawMaterial
  actual : Dictionary.Execution frame
  next : Cursor frame

structure Observation (frame : CPS1Recycling.Frame) where
  current : Cursor frame
  fired : List Dictionary.Reaction
  rawSupply : List Dictionary.RawMaterial
  stages : List (Stage frame)

/-- Requested finite observations generate their own stages from the actual current.
A current contains only its pending source word, never a completed future history. -/
def observe (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (feeds : List (List Dictionary.RawMaterial)) (current : Cursor frame) : Observation frame :=
  List.rec (motive := fun _ => Cursor frame → Observation frame)
    (fun cursor => ⟨cursor,[],[],[]⟩)
    (fun feed _ later cursor =>
      let actual := execution frame cursor feed
      let next := advance frame path cursor feed
      let generated := later next
      ⟨generated.current,actual.fired ++ generated.fired,feed ++ generated.rawSupply,
        ⟨cursor,feed,actual,next⟩ :: generated.stages⟩) feeds current

def requested (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (depth : Nat) (actualStock : Dictionary.Stock frame) : Observation frame :=
  observe frame path (List.replicate depth rawSourceFuel) (start frame path actualStock)

/-- The inlet is the prior actual execution, rather than a genotype terminal-stock reload. -/
def fromActual (path : CPS1Recycling.SplitSite)
    (previous : Σ frame : CPS1Recycling.Frame, CPS1Reinitiation.Handover.Execution frame)
    (feeds : List (List Dictionary.RawMaterial)) : Σ frame : CPS1Recycling.Frame, Observation frame :=
  ⟨previous.1,observe previous.1 path feeds (start previous.1 path previous.2.stock)⟩

theorem actual_next (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (current : Cursor frame) (feed : List Dictionary.RawMaterial) :
    (advance frame path current feed).stock = (execution frame current feed).stock ∧
      (advance frame path current feed).cut = (execution frame current feed).missing ∧
      (execution frame current feed).fired ++ (execution frame current feed).remaining = current.pending :=
  ⟨rfl,rfl,Inventory.execution_decomposes _ _ _ _⟩

theorem cut_continuation (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (current : Cursor frame) (feed : List Dictionary.RawMaterial)
    (missing : CPS1Reinitiation.Species frame) (cut : (execution frame current feed).missing = some missing) :
    (advance frame path current feed).stock = (execution frame current feed).stock ∧
      (advance frame path current feed).pending = (execution frame current feed).remaining ∧
      (advance frame path current feed).completed = current.completed ∧
      (advance frame path current feed).cut = some missing ∧
      ∃ reaction rest, (execution frame current feed).remaining = reaction :: rest ∧
        (execution frame current feed).stock.count missing < (reaction.reactants frame).count missing := by
  refine ⟨rfl,?_,?_,cut,Dictionary.Accounting.execution_cut frame current.pending
    (supplied frame current feed) missing cut⟩
  · simp only [advance,cut,Option.some_ne_none,ite_false]
  · simp only [advance,cut,Option.some_ne_none,ite_false,Nat.add_zero]

theorem tick_inventory_balance (frame : CPS1Recycling.Frame) (current : Cursor frame)
    (feed : List Dictionary.RawMaterial) (species : CPS1Reinitiation.Species frame) :
    (supplied frame current feed).count species +
      (Inventory.credit (Dictionary.Reaction.products frame) (execution frame current feed).fired).count species =
    (execution frame current feed).stock.count species +
      (Inventory.debit (Dictionary.Reaction.reactants frame) (execution frame current feed).fired).count species :=
  Dictionary.Accounting.execution_inventory_balance _ _ _ _

theorem observe_cons (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (feed : List Dictionary.RawMaterial) (rest : List (List Dictionary.RawMaterial)) (current : Cursor frame) :
    observe frame path (feed::rest) current =
      let generated := observe frame path rest (advance frame path current feed)
      ⟨generated.current,(execution frame current feed).fired ++ generated.fired,
        feed ++ generated.rawSupply,⟨current,feed,execution frame current feed,advance frame path current feed⟩ :: generated.stages⟩ := rfl

theorem observation_stage_count (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (feeds : List (List Dictionary.RawMaterial)) (current : Cursor frame) :
    (observe frame path feeds current).stages.length = feeds.length := by
  induction feeds generalizing current with
  | nil => rfl
  | cons feed rest ih =>
    change (observe frame path rest (advance frame path current feed)).stages.length + 1 = rest.length + 1
    rw [ih]

theorem observation_inventory_balance (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (feeds : List (List Dictionary.RawMaterial)) (current : Cursor frame)
    (species : CPS1Reinitiation.Species frame) :
    current.stock.count species +
      ((observe frame path feeds current).rawSupply.map (Dictionary.RawMaterial.species frame)).count species +
      (Inventory.credit (Dictionary.Reaction.products frame) (observe frame path feeds current).fired).count species =
    (observe frame path feeds current).current.stock.count species +
      (Inventory.debit (Dictionary.Reaction.reactants frame) (observe frame path feeds current).fired).count species := by
  induction feeds generalizing current with
  | nil => simp only [observe,Inventory.credit,Inventory.debit,List.flatMap_nil,List.map_nil,List.count_nil,Nat.add_zero]
  | cons feed rest ih =>
    have paid := tick_inventory_balance frame current feed species
    have later := ih (advance frame path current feed)
    have nextStock : (advance frame path current feed).stock = (execution frame current feed).stock := rfl
    rw [nextStock] at later
    rw [observe_cons]
    dsimp only
    simp only [supplied,Inventory.credit,Inventory.debit,List.flatMap_append,List.map_append,List.count_append] at paid later ⊢
    omega


theorem value_append (frame : CPS1Recycling.Frame) (μ : CPS1Reinitiation.Species frame → ℚ)
    (left right : Dictionary.Stock frame) :
    Inventory.value μ (left ++ right) = Inventory.value μ left + Inventory.value μ right := by
  simp only [Inventory.value,List.map_append,List.sum_append]

theorem affinity_append (frame : CPS1Recycling.Frame) (μ : CPS1Reinitiation.Species frame → ℚ)
    (left right : List Dictionary.Reaction) :
    Inventory.affinity μ (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame) (left ++ right) =
      Inventory.affinity μ (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame) left +
      Inventory.affinity μ (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame) right := by
  simp only [Inventory.affinity,List.map_append,List.sum_append]

theorem observation_potential (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (feeds : List (List Dictionary.RawMaterial)) (current : Cursor frame)
    (μ : CPS1Reinitiation.Species frame → ℚ) :
    Inventory.value μ current.stock +
      Inventory.value μ ((observe frame path feeds current).rawSupply.map (Dictionary.RawMaterial.species frame)) =
    Inventory.value μ (observe frame path feeds current).current.stock +
      Inventory.affinity μ (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame)
        (observe frame path feeds current).fired := by
  induction feeds generalizing current with
  | nil => simp only [observe,Inventory.value,Inventory.affinity,List.map_nil,List.sum_nil,add_zero]
  | cons feed rest ih =>
    have paid := Dictionary.Accounting.execution_potential frame current.pending (supplied frame current feed) μ
    have later := ih (advance frame path current feed)
    have nextStock : (advance frame path current feed).stock = (execution frame current feed).stock := rfl
    rw [nextStock] at later
    change Inventory.value μ (supplied frame current feed) =
      Inventory.value μ (execution frame current feed).stock +
        Inventory.affinity μ (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame)
          (execution frame current feed).fired at paid
    rw [supplied,value_append] at paid
    rw [observe_cons]
    dsimp only
    rw [List.map_append,value_append,affinity_append]
    calc
      _ = (Inventory.value μ current.stock + Inventory.value μ (feed.map (Dictionary.RawMaterial.species frame))) +
          Inventory.value μ ((observe frame path rest (advance frame path current feed)).rawSupply.map
            (Dictionary.RawMaterial.species frame)) := by ring
      _ = (Inventory.value μ (execution frame current feed).stock +
          Inventory.affinity μ (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame)
            (execution frame current feed).fired) +
          Inventory.value μ ((observe frame path rest (advance frame path current feed)).rawSupply.map
            (Dictionary.RawMaterial.species frame)) := by rw [paid]
      _ = (Inventory.value μ (execution frame current feed).stock +
          Inventory.value μ ((observe frame path rest (advance frame path current feed)).rawSupply.map
            (Dictionary.RawMaterial.species frame))) +
          Inventory.affinity μ (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame)
            (execution frame current feed).fired := by ring
      _ = (Inventory.value μ (observe frame path rest (advance frame path current feed)).current.stock +
          Inventory.affinity μ (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame)
            (observe frame path rest (advance frame path current feed)).fired) +
          Inventory.affinity μ (Dictionary.Reaction.reactants frame) (Dictionary.Reaction.products frame)
            (execution frame current feed).fired := by rw [later]
      _ = _ := by ring

theorem observation_conservation (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (feeds : List (List Dictionary.RawMaterial)) (current : Cursor frame)
    (channel : Dictionary.Accounting.Channel) :
    Dictionary.Accounting.total frame channel current.stock +
      Dictionary.Accounting.total frame channel
        ((observe frame path feeds current).rawSupply.map (Dictionary.RawMaterial.species frame)) =
    Dictionary.Accounting.total frame channel (observe frame path feeds current).current.stock := by
  induction feeds generalizing current with
  | nil => simp only [observe,Dictionary.Accounting.total,List.map_nil,List.sum_nil,Nat.add_zero]
  | cons feed rest ih =>
    have paid := Dictionary.Accounting.execution_conservation frame current.pending (supplied frame current feed) channel
    have later := ih (advance frame path current feed)
    have nextStock : (advance frame path current feed).stock = (execution frame current feed).stock := rfl
    rw [nextStock] at later
    change Dictionary.Accounting.total frame channel (supplied frame current feed) =
      Dictionary.Accounting.total frame channel (execution frame current feed).stock at paid
    rw [observe_cons]
    dsimp only
    simp only [supplied,Dictionary.Accounting.total,List.map_append,List.sum_append] at paid later ⊢
    omega

def wastes (frame : CPS1Recycling.Frame) (depth : Nat) : Dictionary.Stock frame :=
  (List.replicate depth (Native.cycleWaste frame CPS1ResourceExecution.Program.originalPeptide.2)).flatten

theorem full_step (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (current : Cursor frame) (surplus : Dictionary.Stock frame)
    (pending : current.pending = program path)
    (inventory : current.stock.Perm (Native.reusable frame CPS1ResourceExecution.Program.originalPeptide.2 ++ surplus)) :
    (execution frame current rawSourceFuel).fired = program path ∧
      (execution frame current rawSourceFuel).remaining = [] ∧
      (execution frame current rawSourceFuel).missing = none ∧
      (advance frame path current rawSourceFuel).stock.Perm
        (Native.reusable frame CPS1ResourceExecution.Program.originalPeptide.2 ++
          Native.cycleWaste frame CPS1ResourceExecution.Program.originalPeptide.2 ++ surplus) ∧
      (advance frame path current rawSourceFuel).pending = program path ∧
      (advance frame path current rawSourceFuel).completed = current.completed + 1 ∧
      (advance frame path current rawSourceFuel).cut = none := by
  have inputs : (supplied frame current rawSourceFuel).Perm
      (Native.reusable frame CPS1ResourceExecution.Program.originalPeptide.2 ++
        (Dictionary.rawFuel CPS1ResourceExecution.Program.originalPeptide.2).map (Dictionary.RawMaterial.species frame) ++ surplus) := by
    unfold supplied
    rw [source_fuel_generated]
    apply (inventory.append_right _).trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [List.count_append]
    omega
  have paid := Native.cycle_complete frame CPS1ResourceExecution.Program.originalPeptide.2 path surplus
    (supplied frame current rawSourceFuel) inputs
  have actual : execution frame current rawSourceFuel = Dictionary.execute frame
      (Dictionary.program CPS1ResourceExecution.Program.originalPeptide.2 path) (supplied frame current rawSourceFuel) := by
    rw [execution,pending,source_program_generated]
  have complete : (execution frame current rawSourceFuel).missing = none := by rw [actual]; exact paid.2.2.1
  refine ⟨?_,?_,complete,?_,?_,?_,?_⟩
  · rw [actual,source_program_generated]; exact paid.1
  · rw [actual]; exact paid.2.1
  · change (execution frame current rawSourceFuel).stock.Perm _
    rw [actual]; exact paid.2.2.2
  · simp only [advance,complete,ite_true]
  · simp only [advance,complete,ite_true]
  · exact complete

/-- Every new round consumes the preceding actual balance. No return to the genesis stock
or new actor/tRNA/ABCE1 inlet occurs at a successor depth. -/
theorem full_depth (frame : CPS1Recycling.Frame) (path : CPS1Recycling.SplitSite)
    (depth : Nat) (current : Cursor frame) (surplus : Dictionary.Stock frame)
    (pending : current.pending = program path) (cut : current.cut = none)
    (inventory : current.stock.Perm (Native.reusable frame CPS1ResourceExecution.Program.originalPeptide.2 ++ surplus)) :
    let result := observe frame path (List.replicate depth rawSourceFuel) current
    result.current.stock.Perm (Native.reusable frame CPS1ResourceExecution.Program.originalPeptide.2 ++
      wastes frame depth ++ surplus) ∧ result.current.pending = program path ∧
      result.current.completed = current.completed + depth ∧ result.current.cut = none ∧
      result.fired = (List.replicate depth (program path)).flatten := by
  induction depth generalizing current surplus with
  | zero =>
    dsimp only [List.replicate_zero,observe,wastes,List.flatten_nil]
    refine ⟨?_,pending,?_,cut,rfl⟩
    · simpa only [List.nil_append,List.append_nil] using inventory
    · exact Nat.add_zero _
  | succ depth ih =>
    have step := full_step frame path current surplus pending inventory
    have later := ih (advance frame path current rawSourceFuel)
      (Native.cycleWaste frame CPS1ResourceExecution.Program.originalPeptide.2 ++ surplus)
      step.2.2.2.2.1 step.2.2.2.2.2.2
      (by simpa only [List.append_assoc] using step.2.2.2.1)
    dsimp only at later ⊢
    rw [List.replicate_succ,observe_cons]
    dsimp only
    refine ⟨?_,later.2.1,?_,later.2.2.2.1,?_⟩
    · apply later.1.trans
      apply List.perm_iff_count.mpr
      intro species
      simp only [wastes,List.replicate_succ,List.flatten_cons,List.count_append]
      omega
    · rw [later.2.2.1,step.2.2.2.2.2.1]
      omega
    · rw [step.1,later.2.2.2.2,List.replicate_succ,List.flatten_cons]

def actualObservation (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite) (recycleFeed : List CPS1Recycling.RawMaterial)
    (scanFeed : List CPS1Reinitiation.RawMaterial) (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial)
    (feeds : List (List Dictionary.RawMaterial)) :
    Option (Σ frame : CPS1Recycling.Frame, Observation frame) := do
  let previous ← CPS1Reinitiation.Handover.Source.execution edits water additional path recycleFeed scanFeed bodyFeed
  pure (fromActual path previous feeds)

def actualRequested (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite) (recycleFeed : List CPS1Recycling.RawMaterial)
    (scanFeed : List CPS1Reinitiation.RawMaterial) (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial)
    (depth : Nat) : Option (Σ frame : CPS1Recycling.Frame, Observation frame) :=
  actualObservation edits water additional path recycleFeed scanFeed bodyFeed (List.replicate depth rawSourceFuel)

theorem actual_observation_from_handover (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite) (recycleFeed : List CPS1Recycling.RawMaterial)
    (scanFeed : List CPS1Reinitiation.RawMaterial) (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial)
    (feeds : List (List Dictionary.RawMaterial)) :
    let frame := CPS1Recycling.Source.frame edits water additional
    let recycled := CPS1Recycling.run frame (CPS1Recycling.productiveEvents path) recycleFeed
    let prior := CPS1Reinitiation.run frame recycled path.after Molecules.mrna scanFeed
    let previous := CPS1Reinitiation.Handover.execute frame
      (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna 151 CPS1ResourceExecution.Program.originalPeptide.2)
      (prior.stock ++ bodyFeed.map (CPS1Reinitiation.Handover.RawMaterial.species frame))
    actualObservation edits water additional path recycleFeed scanFeed bodyFeed feeds =
      some ⟨frame,observe frame path feeds (start frame path previous.stock)⟩ := by
  dsimp only
  rw [actualObservation,CPS1Reinitiation.Handover.Source.execution_from_actual_stock]
  rfl

theorem requested_from_reusable (frame : CPS1Recycling.Frame)
    (path : CPS1Recycling.SplitSite) (depth : Nat)
    (actualStock surplus : Dictionary.Stock frame)
    (inventory : actualStock.Perm
      (Native.reusable frame Program.originalPeptide.2 ++ surplus)) :
    let result := requested frame path depth actualStock
    result.current.stock.Perm (Native.reusable frame Program.originalPeptide.2 ++
      wastes frame depth ++ surplus) ∧
    result.current.pending = program path ∧ result.current.completed = depth ∧
    result.current.cut = none ∧
    result.fired = (List.replicate depth (program path)).flatten ∧
    result.stages.length = depth := by
  have paid := full_depth frame path depth (start frame path actualStock) surplus rfl rfl inventory
  refine ⟨paid.1,paid.2.1,?_,paid.2.2.2.1,paid.2.2.2.2,?_⟩
  · exact paid.2.2.1.trans (Nat.zero_add depth)
  · exact (observation_stage_count frame path (List.replicate depth rawSourceFuel)
      (start frame path actualStock)).trans List.length_replicate


theorem actual_requested_complete (edits : Target.Edits) (water additional : Nat)
    (path : CPS1Recycling.SplitSite)
    (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (bodyFeed bodyExtra : List CPS1Reinitiation.Handover.RawMaterial)
    (bodyRaw : bodyFeed.Perm (CPS1Reinitiation.Handover.rawFuel CPS1ResourceExecution.Program.originalPeptide.2 ++ bodyExtra))
    (depth : Nat) :
    let frame := CPS1Recycling.Source.frame edits water additional
    let recycled := CPS1Recycling.run frame (CPS1Recycling.productiveEvents path) recycleFeed
    let prior := CPS1Reinitiation.run frame recycled path.after Molecules.mrna scanFeed
    let previous := CPS1Reinitiation.Handover.execute frame
      (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna 151 CPS1ResourceExecution.Program.originalPeptide.2)
      (prior.stock ++ bodyFeed.map (CPS1Reinitiation.Handover.RawMaterial.species frame))
    let result := requested frame path depth previous.stock
    actualRequested edits water additional path recycleFeed scanFeed bodyFeed depth = some ⟨frame,result⟩ ∧
      result.current.stock.Perm (Native.reusable frame CPS1ResourceExecution.Program.originalPeptide.2 ++
        wastes frame depth ++ Initial.surplus frame CPS1ResourceExecution.Program.originalPeptide.2 recycleExtra scanExtra bodyExtra) ∧
      result.current.pending = program path ∧ result.current.completed = depth ∧ result.current.cut = none ∧
      result.fired = (List.replicate depth (program path)).flatten ∧ result.stages.length = depth  := by
  dsimp only
  let frame := CPS1Recycling.Source.frame edits water additional
  let recycled := CPS1Recycling.run frame (CPS1Recycling.productiveEvents path) recycleFeed
  let prior := CPS1Reinitiation.run frame recycled path.after Molecules.mrna scanFeed
  let previous := CPS1Reinitiation.Handover.execute frame
    (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna 151 CPS1ResourceExecution.Program.originalPeptide.2)
    (prior.stock ++ bodyFeed.map (CPS1Reinitiation.Handover.RawMaterial.species frame))
  exact ⟨actual_observation_from_handover edits water additional path recycleFeed scanFeed bodyFeed
    (List.replicate depth rawSourceFuel),
    requested_from_reusable frame path depth previous.stock
      (Initial.surplus frame CPS1ResourceExecution.Program.originalPeptide.2 recycleExtra scanExtra bodyExtra)
      (Initial.actual_stock edits water additional path recycleFeed recycleExtra recyclingRaw
        scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw)⟩


structure RecursionContract : Prop where
  initial : type_of% Initial.actual_stock
  nativeCycle : type_of% Native.cycle_complete
  rawProgram : type_of% source_program
  rawFuel : type_of% raw_source_fuel_generated
  actualSource : type_of% actual_observation_from_handover
  actualRequested : type_of% actual_requested_complete
  generatedNext : type_of% actual_next
  cutResume : type_of% cut_continuation
  fullDepth : type_of% full_depth
  stages : type_of% observation_stage_count
  conservation : type_of% observation_conservation
  siteEffect : type_of% Dictionary.Accounting.execution_site_effect_computed
  inventory : type_of% observation_inventory_balance
  potential : type_of% observation_potential

theorem sourceGeneratedRecursion : RecursionContract :=
  ⟨Initial.actual_stock,Native.cycle_complete,source_program,raw_source_fuel_generated,
    actual_observation_from_handover,actual_requested_complete,actual_next,cut_continuation,
    full_depth,observation_stage_count,observation_conservation,
    Dictionary.Accounting.execution_site_effect_computed,observation_inventory_balance,observation_potential⟩

end CPS1StockRecursion.Source
