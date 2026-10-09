import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedChemicalReaction.Execution
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.Source

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 600000

namespace CPS1AddressedChemicalReaction.Source
open CPS1LocalChemicalExecution
variable {frame : CPS1Recycling.Frame}

abbrev LocalMaterial (frame : CPS1Recycling.Frame) :=
  CPS1AddressedChemicalReaction.Material (Species frame) (Reaction frame)

abbrev LocalExecution (frame : CPS1Recycling.Frame) :=
  CPS1AddressedChemicalReaction.Execution (Species frame) (Reaction frame)

structure Occurrence (frame : CPS1Recycling.Frame) where
  prior : CPS1LocalChemicalExecution.Source.Occurrence frame
  stock : List (LocalMaterial frame)
  captureRemaining : List (Reaction frame)
  pending : List CPS1LocalChemicalExecution.Source.LocalAction
  runs : List (LocalExecution frame)
  cut : Option (Species frame)
  nextBatch : Nat
  nextEvent : Nat

def Occurrence.forget (current : Occurrence frame) : CPS1LocalChemicalExecution.Source.Occurrence frame :=
  {current.prior with current :=
    ⟨CPS1AddressedChemicalReaction.forget current.stock,current.captureRemaining,current.pending,
      current.prior.current.stages ++ current.runs.map Execution.forget,current.cut⟩}

/-- Prior source material remains explicitly unresolved. This activation does
not allocate new identities to already finished material or old history. -/
def start (prior : CPS1LocalChemicalExecution.Source.Occurrence frame) : Occurrence frame :=
  ⟨prior,prior.current.stock.map Material.inherited,prior.current.captureRemaining,
    prior.current.pending,[],prior.current.cut,0,0⟩

theorem start_project (prior : CPS1LocalChemicalExecution.Source.Occurrence frame) :
    (start prior).forget = prior := by
  cases prior with
  | mk previous current =>
    cases current
    simp only [start,Occurrence.forget,forget,List.map_map,Material.species,Function.comp_def,
      List.map_id_fun',List.map_nil,List.append_nil]
    rfl

def packet (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) : List (Species frame) :=
  feed.map (CPS1LocalChemicalExecution.Source.RawMaterial.species frame) ++
    actions.flatMap (CPS1LocalChemicalExecution.Source.LocalAction.material frame)

def available (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) : List (LocalMaterial frame) :=
  current.stock ++ rawPacket current.nextBatch (packet actions feed)

def requestedProgram (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) : List (Reaction frame) :=
  let state := (CPS1LocalChemicalExecution.Source.heldChain frame
    (forget (available current actions feed))).getD (Chain.initial frame)
  current.captureRemaining ++
    CPS1LocalChemicalExecution.Source.localProgram frame state (actions ++ current.pending)

def execution (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) : LocalExecution frame :=
  run (Reaction.reactants frame) (Reaction.products frame) current.nextEvent
    (requestedProgram current actions feed) (available current actions feed)

def next (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) : Occurrence frame :=
  let result := execution current actions feed
  {current with
    stock := result.stock
    captureRemaining := current.captureRemaining.drop result.fired.length
    pending := (actions ++ current.pending).drop (result.fired.length-current.captureRemaining.length)
    runs := current.runs ++ [result]
    cut := result.missing
    nextBatch := current.nextBatch+1
    nextEvent := result.nextEvent}

theorem available_project (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) :
    forget (available current actions feed) = current.forget.current.stock ++
      feed.map (CPS1LocalChemicalExecution.Source.RawMaterial.species frame) ++
      actions.flatMap (CPS1LocalChemicalExecution.Source.LocalAction.material frame) := by
  simp only [available,forget_append,raw_packet_forget,packet,Occurrence.forget]
  exact List.append_assoc _ _ _ |>.symm

theorem execution_project (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) :
    (execution current actions feed).forget = execute frame
      (requestedProgram current actions feed) (forget (available current actions feed)) :=
  run_project _ _ _ _ _

theorem next_project (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) :
    (next current actions feed).forget =
      {current.forget with current := (CPS1LocalChemicalExecution.Source.advance frame
        current.forget.current actions feed)} := by
  have projected := execution_project current actions feed
  have allMaterial := available_project current actions feed
  unfold CPS1LocalChemicalExecution.Source.advance
  rw [← allMaterial]
  change _ = {current.forget with current := (
    let result := execute frame (requestedProgram current actions feed) (forget (available current actions feed))
    ⟨result.stock,current.captureRemaining.drop result.fired.length,
      (actions ++ current.pending).drop (result.fired.length-current.captureRemaining.length),
      current.forget.current.stages ++ [result],result.missing⟩)}
  rw [← projected]
  simp only [next,Occurrence.forget,Execution.forget,List.map_append,List.map_cons,List.map_nil,
    List.length_map,List.append_assoc]

theorem consumed_source (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) :
    Path (Reaction.reactants frame) (Reaction.products frame) current.nextEvent
      (available current actions feed) (execution current actions feed).fired
      (next current actions feed).stock ∧
    (∀ event ∈ (execution current actions feed).fired,
      event.Valid (Reaction.reactants frame) (Reaction.products frame)) ∧
    ((available current actions feed) ++
      (execution current actions feed).fired.flatMap (Event.created (Reaction.products frame))).Perm
      ((next current actions feed).stock ++ (execution current actions feed).fired.flatMap Event.consumed) ∧
    (next current actions feed).nextEvent =
      current.nextEvent+(execution current actions feed).fired.length ∧
    (next current actions feed).prior = current.prior := by
  have actual := run_path (Reaction.reactants frame) (Reaction.products frame) current.nextEvent
    (requestedProgram current actions feed) (available current actions feed)
  exact ⟨actual,path_events_valid _ _ _ _ _ _ actual,path_whole _ _ _ _ _ _ actual,
    run_next_event _ _ _ _ _,rfl⟩

abbrev Input :=
  List CPS1LocalChemicalExecution.Source.LocalAction ×
    List CPS1LocalChemicalExecution.Source.RawMaterial

def advanceAll (current : Occurrence frame) (inputs : List Input) : Occurrence frame :=
  List.rec (motive := fun _ => Occurrence frame → Occurrence frame)
    (fun current => current)
    (fun input _ recur current => recur (next current input.1 input.2)) inputs current

theorem advance_all_nil (current : Occurrence frame) : advanceAll current [] = current := rfl

theorem advance_all_cons (current : Occurrence frame) (input : Input) (rest : List Input) :
    advanceAll current (input :: rest) = advanceAll (next current input.1 input.2) rest := rfl

theorem advance_all_project (current : Occurrence frame) (inputs : List Input) :
    (advanceAll current inputs).forget = inputs.foldl
      (fun old input => {old with current :=
        (CPS1LocalChemicalExecution.Source.advance frame old.current input.1 input.2)}) current.forget := by
  induction inputs generalizing current with
  | nil => rfl
  | cons input rest ih =>
    simp only [advance_all_cons,List.foldl_cons,ih,next_project]

theorem advance_all_batches (current : Occurrence frame) (inputs : List Input) :
    (advanceAll current inputs).nextBatch = current.nextBatch+inputs.length := by
  induction inputs generalizing current with
  | nil => rfl
  | cons input rest ih =>
    simp only [advance_all_cons,ih,next,List.length_cons,Nat.add_comm,Nat.add_left_comm]

theorem next_event_account (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (generated : current.nextEvent = (current.runs.flatMap Execution.fired).length) :
    (next current actions feed).nextEvent =
      ((next current actions feed).runs.flatMap Execution.fired).length := by
  have eventNumber := (consumed_source current actions feed).2.2.2.1
  rw [eventNumber,generated]
  simp only [next,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append]

theorem advance_all_event_account (current : Occurrence frame) (inputs : List Input)
    (generated : current.nextEvent = (current.runs.flatMap Execution.fired).length) :
    (advanceAll current inputs).nextEvent =
      ((advanceAll current inputs).runs.flatMap Execution.fired).length := by
  induction inputs generalizing current with
  | nil => exact generated
  | cons input rest ih =>
    exact ih _ (next_event_account current input.1 input.2 generated)

def requested (prior : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (inputs : List Input) : Occurrence frame := advanceAll (start prior) inputs

theorem requested_generates_counters (prior : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (inputs : List Input) :
    (requested prior inputs).nextBatch = inputs.length ∧
      (requested prior inputs).nextEvent =
        ((requested prior inputs).runs.flatMap Execution.fired).length :=
  ⟨by simpa only [requested,start,Nat.zero_add] using advance_all_batches (start prior) inputs,
   advance_all_event_account (start prior) inputs rfl⟩

/-- These bounds concern newly recorded material birth labels. Existing source
graphs remain inside their complete species payload. -/
inductive Bounded (batch event : Nat) : LocalMaterial frame → Prop
  | inherited (species) : Bounded batch event (.inherited species)
  | raw {born ordinal species} (earlier : born < batch) :
      Bounded batch event (.raw born ordinal species)
  | product {born ordinal reaction species consumed} (earlier : born < event)
      (parents : ∀ material ∈ consumed, Bounded batch event material) :
      Bounded batch event (.product born ordinal reaction species consumed)

theorem bounded_mono (batch event nextBatch nextEvent : Nat) (material : LocalMaterial frame)
    (generated : Bounded batch event material) (batches : batch ≤ nextBatch) (events : event ≤ nextEvent) :
    Bounded nextBatch nextEvent material := by
  induction generated with
  | inherited => exact .inherited _
  | raw earlier => exact .raw (lt_of_lt_of_le earlier batches)
  | product earlier parents ih => exact .product (lt_of_lt_of_le earlier events) ih

def Fresh (current : Occurrence frame) : Prop :=
  (∀ material ∈ current.stock, Bounded current.nextBatch current.nextEvent material) ∧
    (∀ event ∈ current.runs.flatMap Execution.fired, event.index < current.nextEvent)

theorem start_fresh (prior : CPS1LocalChemicalExecution.Source.Occurrence frame) : Fresh (start prior) := by
  constructor
  · intro material member
    rcases List.mem_map.mp member with ⟨species,_,rfl⟩
    exact .inherited _
  · simp only [start,List.flatMap_nil,List.not_mem_nil,IsEmpty.forall_iff,implies_true]

theorem available_bounded (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) (fresh : Fresh current) :
    ∀ material ∈ available current actions feed,
      Bounded (current.nextBatch+1) current.nextEvent material := by
  intro material member
  rcases List.mem_append.mp member with old | raw
  · exact bounded_mono _ _ _ _ _ (fresh.1 _ old) (by omega) (Nat.le_refl _)
  · rcases List.mem_map.mp raw with ⟨item,_,rfl⟩
    exact .raw (by omega)

theorem run_bounded (batch index : Nat) (program : List (Reaction frame)) (stock : List (LocalMaterial frame))
    (initial : ∀ material ∈ stock, Bounded batch index material) :
    ∀ material ∈ (run (Reaction.reactants frame) (Reaction.products frame) index program stock).stock,
      Bounded batch (run (Reaction.reactants frame) (Reaction.products frame) index program stock).nextEvent material := by
  induction program generalizing index stock with
  | nil => exact initial
  | cons reaction rest ih =>
    cases fired : fire? (Reaction.reactants frame) index reaction stock with
    | error missing => simpa only [run_cons,fired] using initial
    | ok event =>
      have facts := fire_paid (Reaction.reactants frame) (Reaction.products frame) index reaction stock event fired
      have partition := facts.2.2.2.2.1
      rw [facts.2.2.1] at partition
      have oldParents : ∀ material ∈ event.consumed, Bounded batch index material := by
        intro material member
        exact initial _ (partition.mem_iff.mpr (List.mem_append_left _ member))
      have nextStock : ∀ material ∈ event.after (Reaction.products frame), Bounded batch (index+1) material := by
        intro material member
        rcases List.mem_append.mp member with new | old
        · rcases List.mem_map.mp new with ⟨item,_,rfl⟩
          exact .product (by rw [facts.1]; omega)
            (fun parent held => bounded_mono _ _ _ _ _ (oldParents _ held) (Nat.le_refl _) (by omega))
        · exact bounded_mono _ _ _ _ _
            (initial _ (partition.mem_iff.mpr (List.mem_append_right _ old))) (Nat.le_refl _) (by omega)
      simpa only [run_cons,fired] using ih (index+1) (event.after (Reaction.products frame)) nextStock

theorem next_fresh (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) (fresh : Fresh current) :
    Fresh (next current actions feed) := by
  have bounded := run_bounded (current.nextBatch+1) current.nextEvent
    (requestedProgram current actions feed) (available current actions feed)
      (available_bounded current actions feed fresh)
  have numbered := path_event_indices _ _ _ _ _ _ (consumed_source current actions feed).1
  have nextIndex := (consumed_source current actions feed).2.2.2.1
  constructor
  · exact bounded
  · intro event member
    change event ∈ (current.runs ++ [execution current actions feed]).flatMap Execution.fired at member
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] at member
    rw [nextIndex]
    rcases List.mem_append.mp member with old | new
    · exact lt_of_lt_of_le (fresh.2 _ old) (by omega)
    · have contained : event.index ∈ List.range' current.nextEvent (execution current actions feed).fired.length := by
        rw [← numbered]
        exact List.mem_map.mpr ⟨event,new,rfl⟩
      rcases List.mem_range'.mp contained with ⟨offset,inside,same⟩
      simp only [Nat.one_mul] at same
      omega

theorem advance_all_fresh (current : Occurrence frame) (inputs : List Input) (fresh : Fresh current) :
    Fresh (advanceAll current inputs) := by
  induction inputs generalizing current with
  | nil => exact fresh
  | cons input rest ih => exact ih _ (next_fresh current input.1 input.2 fresh)

theorem requested_fresh (prior : CPS1LocalChemicalExecution.Source.Occurrence frame) (inputs : List Input) :
    Fresh (requested prior inputs) := advance_all_fresh _ _ (start_fresh prior)

def fromSource
    (edits : SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) :
    Option (Σ frame : CPS1Recycling.Frame, Occurrence frame) := do
  let previous ← CPS1LocalChemicalExecution.Source.actualCapture edits water additional path
    recycleFeed scanFeed bodyFeed depth
  pure ⟨previous.1,next (start previous.2)
    (actions ++ CPS1LocalChemicalExecution.Source.chemicalActions) feed⟩

theorem from_source_project
    (edits : SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) :
    (fromSource edits water additional path recycleFeed scanFeed bodyFeed depth actions feed).map
      (fun current => ⟨current.1,current.2.forget⟩) =
      CPS1LocalChemicalExecution.Source.execution edits water additional path
        recycleFeed scanFeed bodyFeed depth actions feed := by
  unfold fromSource CPS1LocalChemicalExecution.Source.execution
  cases CPS1LocalChemicalExecution.Source.actualCapture edits water additional path
    recycleFeed scanFeed bodyFeed depth with
  | none => rfl
  | some generated =>
    change some (⟨generated.1,(next (start generated.2)
      (actions ++ CPS1LocalChemicalExecution.Source.chemicalActions) feed).forget⟩ :
        Σ frame : CPS1Recycling.Frame, CPS1LocalChemicalExecution.Source.Occurrence frame) = _
    rw [next_project,start_project]
    rfl

theorem from_source_fresh
    (edits : SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) :
    match fromSource edits water additional path recycleFeed scanFeed bodyFeed depth actions feed with
    | none => True
    | some generated => Fresh generated.2 := by
  unfold fromSource
  cases CPS1LocalChemicalExecution.Source.actualCapture edits water additional path
    recycleFeed scanFeed bodyFeed depth with
  | none => trivial
  | some generated =>
    exact next_fresh _ _ _ (start_fresh generated.2)

end CPS1AddressedChemicalReaction.Source
