import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedHydrolysis.Update

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace CPS1AddressedHydrolysis
open CPS1LocalChemicalExecution CPS1AtomicSource
variable {frame : CPS1Recycling.Frame}

abbrev LocalMaterial (frame : CPS1Recycling.Frame) := CPS1AddressedChemicalReaction.Source.LocalMaterial frame
abbrev LocalEvent (frame : CPS1Recycling.Frame) :=
  CPS1AddressedChemicalReaction.Event (Species frame) (Reaction frame)

def Valid (word : List CPS1ResourceExecution.AA) (edges : List Nat) (edge : Nat) : Prop :=
  edges.Nodup ∧ (∀ address ∈ edges, address+1 < word.length) ∧ edge ∈ edges

instance (word : List CPS1ResourceExecution.AA) (edges : List Nat) (edge : Nat) :
    Decidable (Valid word edges edge) := by
  unfold Valid
  infer_instance

def preparedWater (stock : List (LocalMaterial frame)) : List Water := stock.filterMap waterSource?

theorem prepared_water (stock : List (LocalMaterial frame)) (material : LocalMaterial frame)
    (member : material ∈ stock) (water : Water) (actual : waterSource? material = some water) :
    water ∈ preparedWater stock := List.mem_filterMap.mpr ⟨material,member,actual⟩

structure Renewal (frame : CPS1Recycling.Frame) where
  event : LocalEvent frame
  chain : Chain frame
  edge : Nat
  chainMaterial : LocalMaterial frame
  processorMaterial : LocalMaterial frame
  water : Water

def Renewal.atoms (renewal : Renewal frame) : List Atom :=
  producedAtoms renewal.water (Actual.cps1 frame).word renewal.chain.bonds renewal.edge

def Renewal.sourceGraph (renewal : Renewal frame) : Graph.Molecule :=
  Graph.fromChain frame (renewal.chain.cleave frame renewal.edge)

def Renewal.bonds (renewal : Renewal frame) : List Bond :=
  renewal.sourceGraph.bonds.filterMap (resolveBond? renewal.atoms)

def Renewal.inputs (renewal : Renewal frame) : Prop :=
  Valid (Actual.cps1 frame).word renewal.chain.bonds renewal.edge ∧
    renewal.event.reaction = .hydrolyseBond renewal.chain renewal.edge ∧
    renewal.event.consumed = [renewal.chainMaterial,renewal.processorMaterial,renewal.water.material frame] ∧
    renewal.chainMaterial.species = .chain renewal.chain ∧
    renewal.processorMaterial.species = .processor

def Renewal.outputMaterial (renewal : Renewal frame) : LocalMaterial frame :=
  .product renewal.event.index 0 renewal.event.reaction (.chain (renewal.chain.cleave frame renewal.edge))
    renewal.event.consumed

theorem output_is_actual (renewal : Renewal frame) (inputs : renewal.inputs) :
    renewal.outputMaterial ∈ renewal.event.created (Reaction.products frame) ∧
      renewal.outputMaterial ∈ renewal.event.after (Reaction.products frame) ∧
      renewal.outputMaterial.species = .chain (renewal.chain.cleave frame renewal.edge) := by
  have made : renewal.event.created (Reaction.products frame) =
      [renewal.outputMaterial,
        .product renewal.event.index 1 renewal.event.reaction .processor renewal.event.consumed] := by
    unfold CPS1AddressedChemicalReaction.Event.created CPS1AddressedChemicalReaction.generatedProducts
    unfold Renewal.outputMaterial
    simp only [inputs.2.1,Reaction.products]
    rfl
  have created : renewal.outputMaterial ∈ renewal.event.created (Reaction.products frame) := by
    rw [made]
    simp
  exact ⟨created,List.mem_append_left _ created,rfl⟩

inductive Residual (frame : CPS1Recycling.Frame)
  | otherReaction
  | invalidEdges (chain : Chain frame) (edge : Nat)
  | consumedShape
  | consumedKinds
  | waterSourceMissing (material : LocalMaterial frame)

inductive Outcome (frame : CPS1Recycling.Frame)
  | renewed (renewal : Renewal frame)
  | residual (event : LocalEvent frame) (reason : Residual frame)

/-- The endpoint and old chain come from this already fired source reaction.
The consumed water is the actual third reserved occurrence, not a later feed. -/
def classify (event : LocalEvent frame) : Outcome frame :=
  match event.reaction with
  | .hydrolyseBond chain edge =>
    if Valid (Actual.cps1 frame).word chain.bonds edge then
      match event.consumed with
      | [chainMaterial,processorMaterial,waterMaterial] =>
        if chainMaterial.species = .chain chain ∧ processorMaterial.species = .processor then
          match waterSource? waterMaterial with
          | some water => .renewed ⟨event,chain,edge,chainMaterial,processorMaterial,water⟩
          | none => .residual event (.waterSourceMissing waterMaterial)
        else .residual event .consumedKinds
      | _ => .residual event .consumedShape
    else .residual event (.invalidEdges chain edge)
  | _ => .residual event .otherReaction

theorem classified_inputs (event : LocalEvent frame) (renewal : Renewal frame)
    (actual : classify event = .renewed renewal) : renewal.event = event ∧ renewal.inputs := by
  unfold classify at actual
  cases reaction : event.reaction <;> try (simp [reaction] at actual)
  rename_i chain edge
  split at actual
  · rename_i valid
    cases consumed : event.consumed with
    | nil => simp [consumed] at actual
    | cons chainMaterial rest =>
      cases rest with
      | nil => simp [consumed] at actual
      | cons processorMaterial rest =>
        cases rest with
        | nil => simp [consumed] at actual
        | cons waterMaterial rest =>
          cases rest with
          | cons => simp [consumed] at actual
          | nil =>
            simp only [consumed] at actual
            split at actual
            · rename_i matched
              cases waterSource : waterSource? waterMaterial with
              | none => simp [waterSource] at actual
              | some water =>
                simp only [waterSource,Outcome.renewed.injEq] at actual
                subst renewal
                refine ⟨rfl,valid,reaction,?_,matched.1,matched.2⟩
                have same := water_source_exact waterMaterial water waterSource
                simpa only [same] using consumed
            · cases actual
  · cases actual

def MaterialProperties (renewal : Renewal frame) : Prop :=
  (renewal.atoms.map Atom.origin).Perm
    ((List.range (Graph.fromChain frame renewal.chain).atoms.length).map Origin.old ++
      waterAtoms.map (Origin.water renewal.water)) ∧
  (renewal.atoms.map Atom.origin).Nodup ∧
  (renewal.atoms.map Atom.descriptor).Perm renewal.sourceGraph.atoms ∧
  (renewal.atoms.map (fun atom => atom.descriptor.address)).Nodup ∧
  (∀ atom ∈ waterAtomsAt renewal.water (Actual.cps1 frame).word renewal.edge,
    ∃ slot, atom.origin = .water renewal.water slot ∧ slot.element = atom.descriptor.source.element ∧
      slot.charge = atom.descriptor.source.charge) ∧
  Graph.peptideBond renewal.edge ∈ (Graph.fromChain frame renewal.chain).bonds ∧
  Graph.peptideBond renewal.edge ∉ renewal.sourceGraph.bonds ∧
  (∀ bond ∈ (Graph.fromChain frame renewal.chain).bonds, bond ≠ Graph.peptideBond renewal.edge →
    bond ∈ renewal.sourceGraph.bonds) ∧
  (∀ source ∈ renewal.sourceGraph.bonds, ∃ bond ∈ renewal.bonds,
    bond.source = source ∧
    (∃ atom ∈ renewal.atoms, atom.origin = bond.left ∧ atom.descriptor.address = source.left) ∧
    (∃ atom ∈ renewal.atoms, atom.origin = bond.right ∧ atom.descriptor.address = source.right))

theorem material_generated (renewal : Renewal frame) (inputs : renewal.inputs) : MaterialProperties renewal := by
  have valid := inputs.1
  have inside := valid.2.1 _ valid.2.2
  have removed := peptide_removed (Actual.cps1 frame).word renewal.chain.bonds valid.1 valid.2.1 renewal.edge valid.2.2
  refine ⟨produced_partition _ _ _ _ inside,produced_origins_unique _ _ _ _ inside,
    produced_descriptors _ _ _ valid.1 valid.2.1 _ valid.2.2,
    produced_addresses_unique _ _ _ valid.1 valid.2.1 _ valid.2.2,?_,removed.1,removed.2,?_,?_⟩
  · intro atom member
    rcases List.mem_map.mp member with ⟨source,held,same⟩
    subst atom
    exact ⟨sourceWaterSlot source,rfl,(gained_payload _ _ _ held).2⟩
  · intro bond member different
    exact other_bonds_preserved _ _ valid.1 valid.2.1 _ valid.2.2 bond member different
  · intro source member
    rcases resolve_bond_generated renewal.water (Actual.cps1 frame).word renewal.chain.bonds
      valid.1 valid.2.1 renewal.edge valid.2.2 source member with ⟨bond,resolved,identity,left,right⟩
    exact ⟨bond,List.mem_filterMap.mpr ⟨source,member,resolved⟩,identity,left,right⟩

theorem water_before_fire (event : LocalEvent frame) (renewal : Renewal frame)
    (actual : classify event = .renewed renewal)
    (paid : event.Valid (Reaction.reactants frame) (Reaction.products frame)) :
    renewal.water.material frame ∈ event.consumed ∧
      renewal.water.material frame ∈ event.before ∧
      renewal.water ∈ preparedWater event.before := by
  have inputs := (classified_inputs event renewal actual).2
  have sameEvent := (classified_inputs event renewal actual).1
  have consumed : renewal.water.material frame ∈ event.consumed := by
    rw [← sameEvent,inputs.2.2.1]
    simp
  have before := paid.2.1.mem_iff.mpr (List.mem_append_left _ consumed)
  exact ⟨consumed,before,prepared_water _ _ before _ (raw_water_source frame renewal.water)⟩

theorem raw_not_created (event : LocalEvent frame) (water : Water) :
    water.material frame ∉ event.created (Reaction.products frame) := by
  intro member
  rcases List.mem_map.mp member with ⟨item,_,same⟩
  cases same

theorem path_raw_before (index : Nat) (initial : List (LocalMaterial frame))
    (trace : List (LocalEvent frame)) (final : List (LocalMaterial frame))
    (path : CPS1AddressedChemicalReaction.Path (Reaction.reactants frame) (Reaction.products frame)
      index initial trace final) :
    ∀ event ∈ trace, ∀ water : Water, water.material frame ∈ event.before → water.material frame ∈ initial := by
  induction path with
  | nil => simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | @cons index stock first trace final fired rest ih =>
    have facts := CPS1AddressedChemicalReaction.fire_paid (Reaction.reactants frame) (Reaction.products frame)
      _ _ _ _ fired
    have partition := facts.2.2.2.2.1
    rw [facts.2.2.1] at partition
    intro event member water available
    rcases List.mem_cons.mp member with same | later
    · subst event
      simpa only [facts.2.2.1] using available
    · have held := ih event later water available
      rcases List.mem_append.mp held with generated | left
      · exact False.elim (raw_not_created first water generated)
      · exact partition.mem_iff.mpr (List.mem_append_right _ left)

structure Continuation (frame : CPS1Recycling.Frame) where
  prepared : List Water
  events : List (Outcome frame)
  next : CPS1AddressedChemicalReaction.Source.Occurrence frame

def fromCurrent (current : CPS1AddressedChemicalReaction.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) : Continuation frame :=
  let input := CPS1AddressedChemicalReaction.Source.available current actions feed
  let prepared := preparedWater input
  let result := CPS1AddressedChemicalReaction.Source.execution current actions feed
  ⟨prepared,result.fired.map classify,CPS1AddressedChemicalReaction.Source.next current actions feed⟩

theorem source_generated_hydrolysis (current : CPS1AddressedChemicalReaction.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) :
    type_of% (CPS1AddressedChemicalReaction.Source.consumed_source current actions feed) ∧
    (fromCurrent current actions feed).next = CPS1AddressedChemicalReaction.Source.next current actions feed ∧
    (fromCurrent current actions feed).prepared =
      preparedWater (CPS1AddressedChemicalReaction.Source.available current actions feed) ∧
    (∀ renewal, Outcome.renewed renewal ∈ (fromCurrent current actions feed).events →
      renewal.inputs ∧ MaterialProperties renewal ∧
      renewal.water.material frame ∈ renewal.event.consumed ∧
      renewal.water.material frame ∈ renewal.event.before ∧
      renewal.water ∈ preparedWater renewal.event.before ∧
      renewal.water ∈ (fromCurrent current actions feed).prepared) := by
  have source := CPS1AddressedChemicalReaction.Source.consumed_source current actions feed
  refine ⟨source,rfl,rfl,?_⟩
  intro renewal member
  rcases List.mem_map.mp member with ⟨event,paidEvent,classified⟩
  have inputs := (classified_inputs event renewal classified).2
  have paid := source.2.1 _ paidEvent
  have water := water_before_fire event renewal classified paid
  have sameEvent := (classified_inputs event renewal classified).1
  have originallyHeld := path_raw_before _ _ _ _ source.1 event paidEvent renewal.water water.2.1
  refine ⟨inputs,material_generated renewal inputs,?_,?_,?_,?_⟩
  · simpa only [sameEvent] using water.1
  · simpa only [sameEvent] using water.2.1
  · simpa only [sameEvent] using water.2.2
  · exact prepared_water _ _ originallyHeld _ (raw_water_source frame renewal.water)

end CPS1AddressedHydrolysis
