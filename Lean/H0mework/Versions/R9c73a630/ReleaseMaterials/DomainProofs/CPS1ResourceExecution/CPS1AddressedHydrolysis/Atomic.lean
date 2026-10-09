import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedHydrolysis.Current

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace CPS1AddressedHydrolysis.Atomic
open CPS1LocalChemicalExecution CPS1AtomicSource
variable {frame : CPS1Recycling.Frame}

structure Carrier (frame : CPS1Recycling.Frame) where
  material : LocalMaterial frame
  chain : Chain frame
  atoms : List Atom
  bonds : List Bond

inductive BirthKey | product (event ordinal : Nat) deriving DecidableEq

def key? (material : LocalMaterial frame) : Option BirthKey :=
  match material with
  | .product event ordinal _ _ _ => some (.product event ordinal)
  | _ => none

def carrierAt? (history : List (Carrier frame)) (material : LocalMaterial frame) : Option (Carrier frame) :=
  match key? material with
  | none => none
  | some key => history.find? (fun carrier => key? carrier.material = some key)

def Aligned (atoms : List Atom) (chain : Chain frame) : Prop :=
  (atoms.map Atom.descriptor).Perm (Graph.fromChain frame chain).atoms ∧
    (atoms.map Atom.origin).Nodup ∧
    (atoms.map (fun atom => atom.descriptor.address)).Nodup

def CompleteBonds (carrier : Carrier frame) : Prop :=
  carrier.bonds.map Bond.source = (Graph.fromChain frame carrier.chain).bonds ∧
    (∀ bond ∈ carrier.bonds,
      (∃ atom ∈ carrier.atoms, atom.origin = bond.left ∧ atom.descriptor.address = bond.source.left) ∧
      (∃ atom ∈ carrier.atoms, atom.origin = bond.right ∧ atom.descriptor.address = bond.source.right))

instance (atoms : List Atom) (chain : Chain frame) : Decidable (Aligned atoms chain) := by
  unfold Aligned
  infer_instance

def FreshWater (atoms : List Atom) (water : Water) : Prop :=
  List.Disjoint (atoms.map Atom.origin) (waterAtoms.map (Origin.water water))

instance (atoms : List Atom) (water : Water) : Decidable (FreshWater atoms water) := by
  unfold FreshWater
  change Decidable (∀ origin ∈ atoms.map Atom.origin, origin ∉ waterAtoms.map (Origin.water water))
  infer_instance

def grownAtoms (atoms : List Atom) (renewal : Renewal frame) : List Atom :=
  atoms ++ waterAtomsAt renewal.water (Actual.cps1 frame).word renewal.edge

def grown (atoms : List Atom) (renewal : Renewal frame) : Carrier frame :=
  let nextAtoms := grownAtoms atoms renewal
  ⟨renewal.outputMaterial,renewal.chain.cleave frame renewal.edge,nextAtoms,
    renewal.sourceGraph.bonds.filterMap (resolveBond? nextAtoms)⟩

theorem grown_preserves (atoms : List Atom) (renewal : Renewal frame) :
    (grown atoms renewal).material = renewal.outputMaterial ∧
    atoms.Sublist (grown atoms renewal).atoms ∧
    (∀ atom ∈ atoms, atom ∈ (grown atoms renewal).atoms) :=
  ⟨rfl,List.sublist_append_left _ _,fun _ member => List.mem_append_left _ member⟩

theorem grown_aligned (atoms : List Atom) (renewal : Renewal frame)
    (inputs : renewal.inputs) (aligned : Aligned atoms renewal.chain)
    (fresh : FreshWater atoms renewal.water) : Aligned (grown atoms renewal).atoms
      (grown atoms renewal).chain := by
  have valid := inputs.1
  have inside := valid.2.1 _ valid.2.2
  have descriptors : ((grown atoms renewal).atoms.map Atom.descriptor).Perm renewal.sourceGraph.atoms := by
    have incoming : (waterAtomsAt renewal.water (Actual.cps1 frame).word renewal.edge).map Atom.descriptor =
        gainedAtoms (Actual.cps1 frame).word renewal.edge := by
      simp only [waterAtomsAt,List.map_map,Function.comp_def,List.map_id_fun',id_eq]
    have combined := aligned.1.append_right (gainedAtoms (Actual.cps1 frame).word renewal.edge)
    have changed := graph_atom_update (Actual.cps1 frame).word renewal.chain.bonds
      valid.1 valid.2.1 renewal.edge valid.2.2
    simpa only [grown,grownAtoms,List.map_append,incoming,Renewal.sourceGraph,Graph.fromChain,Chain.cleave]
      using combined.trans changed.symm
  refine ⟨descriptors,?_,?_⟩
  · have incoming : ((waterAtomsAt renewal.water (Actual.cps1 frame).word renewal.edge).map Atom.origin).Perm
        (waterAtoms.map (Origin.water renewal.water)) := by
      simpa only [waterAtomsAt,List.map_map,Function.comp_def,sourceWaterSlot] using
        (gained_slots_partition (Actual.cps1 frame).word renewal.edge inside).map (Origin.water renewal.water)
    have joined := incoming.append_left (atoms.map Atom.origin)
    simp only [grown,grownAtoms,List.map_append]
    apply joined.nodup_iff.mpr
    apply List.nodup_append.mpr
    refine ⟨aligned.2.1,(water_rule .H).2.2.1.map (fun _ _ same => (Origin.water.inj same).2),?_⟩
    intro left held right incoming same
    apply fresh held
    rw [same]
    exact incoming
  · have addressPermutation := descriptors.map Graph.Atom.address
    simpa only [List.map_map,Function.comp_def] using
      addressPermutation.nodup_iff.mpr (graph_addresses_unique (Actual.cps1 frame).word (renewal.chain.bonds.erase renewal.edge))

theorem grown_bonds (atoms : List Atom) (renewal : Renewal frame)
    (inputs : renewal.inputs) (aligned : Aligned atoms renewal.chain)
    (fresh : FreshWater atoms renewal.water) : CompleteBonds (grown atoms renewal) := by
  have descriptors := (grown_aligned atoms renewal inputs aligned fresh).1
  have paid (source : Graph.Bond) (member : source ∈ renewal.sourceGraph.bonds) :
      ∃ bond, resolveBond? (grownAtoms atoms renewal) source = some bond ∧ bond.source = source ∧
        (∃ atom ∈ grownAtoms atoms renewal, atom.origin = bond.left ∧ atom.descriptor.address = source.left) ∧
        (∃ atom ∈ grownAtoms atoms renewal, atom.origin = bond.right ∧ atom.descriptor.address = source.right) :=
    resolve_bond_in_carrier _ (Actual.cps1 frame).word (renewal.chain.bonds.erase renewal.edge)
      descriptors source member
  have all (sources : List Graph.Bond)
      (available : ∀ source ∈ sources, ∃ bond,
        resolveBond? (grownAtoms atoms renewal) source = some bond ∧ bond.source = source) :
      (sources.filterMap (resolveBond? (grownAtoms atoms renewal))).map Bond.source = sources := by
    induction sources with
    | nil => rfl
    | cons source rest ih =>
      rcases available source List.mem_cons_self with ⟨bond,resolved,identity⟩
      rw [List.filterMap_cons,resolved,List.map_cons,identity]
      exact congrArg (List.cons source) (ih (fun source member => available source (List.mem_cons_of_mem _ member)))
  refine ⟨all renewal.sourceGraph.bonds (fun source member => ?_),?_⟩
  · rcases paid source member with ⟨bond,resolved,identity,_,_⟩
    exact ⟨bond,resolved,identity⟩
  · intro bond member
    rcases List.mem_filterMap.mp member with ⟨source,held,resolved⟩
    rcases paid source held with ⟨generated,actual,identity,left,right⟩
    have same : generated = bond := Option.some.inj (actual.symm.trans resolved)
    subst bond
    simpa only [grown,identity] using And.intro left right

inductive Residual (frame : CPS1Recycling.Frame)
  | source (outcome : Outcome frame)
  | missingAtomicHistory (renewal : Renewal frame)
  | carrierMismatch (renewal : Renewal frame) (atoms : List Atom)
  | reusedWater (renewal : Renewal frame) (atoms : List Atom)

inductive Step (frame : CPS1Recycling.Frame)
  | updated (renewal : Renewal frame) (before : List Atom) (carrier : Carrier frame)
  | transported (carrier : Carrier frame)
  | residual (reason : Residual frame)

def preserving (reaction : Reaction frame) : Bool :=
  match reaction with | .report .. | .drive .. => true | _ => false

def preservedChain? (history : List (Carrier frame)) (event : LocalEvent frame) : Option (Carrier frame) :=
  if preserving event.reaction then
    match event.consumed.head? with
    | none => none
    | some input =>
      match carrierAt? history input with
      | none => none
      | some previous =>
        match (event.created (Reaction.products frame)).head? with
        | none => none
        | some output =>
          match output.species with
          | .chain chain =>
            if Aligned previous.atoms chain then some ⟨output,chain,previous.atoms,previous.bonds⟩ else none
          | _ => none
  else none

theorem preserved_chain_generated (history : List (Carrier frame)) (event : LocalEvent frame)
    (carrier : Carrier frame) (actual : preservedChain? history event = some carrier) :
    carrier.material ∈ event.created (Reaction.products frame) ∧ Aligned carrier.atoms carrier.chain ∧
      ∃ input previous, input ∈ event.consumed ∧ carrierAt? history input = some previous ∧
        carrier.atoms = previous.atoms ∧ carrier.bonds = previous.bonds := by
  unfold preservedChain? at actual
  by_cases usable : preserving event.reaction = true
  · simp only [if_pos usable] at actual
    cases input : event.consumed.head? with
    | none => simp [input] at actual
    | some material =>
      simp only [input] at actual
      cases previous : carrierAt? history material with
      | none => simp [previous] at actual
      | some old =>
        simp only [previous] at actual
        cases output : (event.created (Reaction.products frame)).head? with
        | none => simp [output] at actual
        | some new =>
          simp only [output] at actual
          cases kind : new.species <;> try (simp [kind] at actual)
          rename_i chain
          rcases actual with ⟨aligned,same⟩
          subst carrier
          exact ⟨List.mem_of_head? output,aligned,material,old,
            List.mem_of_head? input,previous,rfl,rfl⟩
  · simp only [if_neg usable] at actual
    cases actual

def priorAtoms? (history : List (Carrier frame)) (renewal : Renewal frame) : Option (List Atom) :=
  match carrierAt? history renewal.chainMaterial with
  | some carrier => some carrier.atoms
  | none => if renewal.chain.hydrolysed = [] then some (oldAtoms (Graph.fromChain frame renewal.chain)) else none

def step (history : List (Carrier frame)) (event : LocalEvent frame) : Step frame :=
  match classify event with
  | .residual event reason =>
    match preservedChain? history event with
    | some carrier => .transported carrier
    | none => .residual (.source (.residual event reason))
  | .renewed renewal =>
    match priorAtoms? history renewal with
    | none => .residual (.missingAtomicHistory renewal)
    | some atoms =>
      if Aligned atoms renewal.chain then
        if FreshWater atoms renewal.water then .updated renewal atoms (grown atoms renewal)
        else .residual (.reusedWater renewal atoms)
      else .residual (.carrierMismatch renewal atoms)

theorem step_updated (history : List (Carrier frame)) (event : LocalEvent frame)
    (renewal : Renewal frame) (before : List Atom) (carrier : Carrier frame)
    (actual : step history event = .updated renewal before carrier) :
    classify event = .renewed renewal ∧ priorAtoms? history renewal = some before ∧
      Aligned before renewal.chain ∧ FreshWater before renewal.water ∧ carrier = grown before renewal := by
  unfold step at actual
  cases classified : classify event with
  | residual old reason =>
    cases preserved : preservedChain? history old <;> simp only [classified,preserved] at actual <;> cases actual
  | renewed generated =>
    simp only [classified] at actual
    cases prior : priorAtoms? history generated with
    | none => simp [prior] at actual
    | some atoms =>
      simp only [prior] at actual
      split at actual
      · rename_i aligned
        split at actual
        · rename_i fresh
          simp only [Step.updated.injEq] at actual
          rcases actual with ⟨rfl,rfl,rfl⟩
          exact ⟨rfl,prior,aligned,fresh,rfl⟩
        · cases actual
      · cases actual

theorem updated_carrier (history : List (Carrier frame)) (event : LocalEvent frame)
    (renewal : Renewal frame) (before : List Atom) (carrier : Carrier frame)
    (actual : step history event = .updated renewal before carrier) :
    carrier.material ∈ event.created (Reaction.products frame) ∧
      Aligned carrier.atoms carrier.chain ∧ before.Sublist carrier.atoms ∧
      (∀ atom ∈ before, atom ∈ carrier.atoms) := by
  have generated := step_updated history event renewal before carrier actual
  have source := classified_inputs event renewal generated.1
  rcases generated with ⟨classified,prior,aligned,fresh,rfl⟩
  refine ⟨?_,grown_aligned before renewal source.2 aligned fresh,
    (grown_preserves before renewal).2.1,(grown_preserves before renewal).2.2⟩
  simpa only [grown,source.1] using (output_is_actual renewal source.2).1

theorem updated_bonds (history : List (Carrier frame)) (event : LocalEvent frame)
    (renewal : Renewal frame) (before : List Atom) (carrier : Carrier frame)
    (actual : step history event = .updated renewal before carrier) : CompleteBonds carrier := by
  have generated := step_updated history event renewal before carrier actual
  have source := classified_inputs event renewal generated.1
  rw [generated.2.2.2.2]
  exact grown_bonds before renewal source.2 generated.2.2.1 generated.2.2.2.1

theorem previous_water_preserved (history : List (Carrier frame)) (event : LocalEvent frame)
    (renewal : Renewal frame) (before : List Atom) (carrier : Carrier frame)
    (actual : step history event = .updated renewal before carrier)
    (oldWater : Water) (slot : WaterAtom)
    (old : ∃ atom ∈ before, atom.origin = .water oldWater slot) :
    ∃ atom ∈ carrier.atoms, atom.origin = .water oldWater slot := by
  rcases old with ⟨atom,member,origin⟩
  exact ⟨atom,(updated_carrier history event renewal before carrier actual).2.2.2 atom member,origin⟩

structure Trace (frame : CPS1Recycling.Frame) where
  history : List (Carrier frame)
  steps : List (Step frame)

def historyAfter (history : List (Carrier frame)) : Step frame → List (Carrier frame)
  | .updated _ _ carrier | .transported carrier => history ++ [carrier]
  | .residual _ => history

def run (history : List (Carrier frame)) (events : List (LocalEvent frame)) : Trace frame :=
  List.rec (motive := fun _ => List (Carrier frame) → Trace frame)
    (fun prior => ⟨prior,[]⟩)
    (fun event _ recur prior =>
      let next := step prior event
      let rest := recur (historyAfter prior next)
      ⟨rest.history,next :: rest.steps⟩) events history

theorem run_nil (history : List (Carrier frame)) : run history [] = ⟨history,[]⟩ := rfl

theorem run_cons (history : List (Carrier frame)) (event : LocalEvent frame) (rest : List (LocalEvent frame)) :
    run history (event :: rest) =
      let selected := step history event
      let after := run (historyAfter history selected) rest
      ⟨after.history,selected :: after.steps⟩ := rfl

inductive Path : List (Carrier frame) → List (LocalEvent frame) → List (Step frame) → List (Carrier frame) → Prop
  | nil (history) : Path history [] [] history
  | cons {history event events steps final}
      (tail : Path (historyAfter history (step history event)) events steps final) :
      Path history (event :: events) (step history event :: steps) final

theorem run_path (history : List (Carrier frame)) (events : List (LocalEvent frame)) :
    Path history events (run history events).steps (run history events).history := by
  induction events generalizing history with
  | nil => exact .nil _
  | cons event rest ih => simpa only [run_cons] using Path.cons (ih (historyAfter history (step history event)))

theorem path_history_preserved (history : List (Carrier frame)) (events : List (LocalEvent frame))
    (steps : List (Step frame)) (final : List (Carrier frame)) (path : Path history events steps final) :
    history.Sublist final := by
  induction path with
  | nil => exact List.Sublist.refl _
  | @cons history event events steps final tail ih =>
    have before : history.Sublist (historyAfter history (step history event)) := by
      cases step history event <;> first | exact List.sublist_append_left _ _ | exact List.Sublist.refl _
    exact before.trans ih

theorem path_updates (history : List (Carrier frame)) (events : List (LocalEvent frame))
    (steps : List (Step frame)) (final : List (Carrier frame)) (path : Path history events steps final) :
    ∀ renewal before carrier, Step.updated renewal before carrier ∈ steps →
      carrier ∈ final ∧ carrier = grown before renewal ∧
        Aligned carrier.atoms carrier.chain ∧ CompleteBonds carrier ∧ before.Sublist carrier.atoms ∧
        (∀ atom ∈ before, atom ∈ carrier.atoms) ∧
      (∃ event ∈ events, carrier.material ∈ event.created (Reaction.products frame)) := by
  induction path with
  | nil => simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | @cons history event events steps final tail ih =>
    intro renewal before carrier member
    rcases List.mem_cons.mp member with selected | later
    · have actual : step history event = .updated renewal before carrier := selected.symm
      have generated := updated_carrier history event renewal before carrier actual
      have installed : carrier ∈ historyAfter history (step history event) := by
        rw [actual]
        simp only [historyAfter,List.mem_append,List.mem_singleton,or_true]
      have held := (path_history_preserved _ _ _ _ tail).subset installed
      exact ⟨held,(step_updated history event renewal before carrier actual).2.2.2.2,
        generated.2.1,updated_bonds history event renewal before carrier actual,
        generated.2.2.1,generated.2.2.2,event,List.mem_cons_self,generated.1⟩
    · rcases ih renewal before carrier later with ⟨held,same,aligned,bonds,sublist,atoms,eventSource,memberSource,material⟩
      exact ⟨held,same,aligned,bonds,sublist,atoms,eventSource,List.mem_cons_of_mem _ memberSource,material⟩

structure Occurrence (frame : CPS1Recycling.Frame) where
  source : CPS1AddressedChemicalReaction.Source.Occurrence frame
  history : List (Carrier frame)
  stages : List (Trace frame)

def start (source : CPS1AddressedChemicalReaction.Source.Occurrence frame) : Occurrence frame :=
  ⟨source,[],[]⟩

def next (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) : Occurrence frame :=
  let result := CPS1AddressedChemicalReaction.Source.execution current.source actions feed
  let generated := run current.history result.fired
  ⟨CPS1AddressedChemicalReaction.Source.next current.source actions feed,
    generated.history,current.stages ++ [generated]⟩

theorem next_source (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) :
    (next current actions feed).source = CPS1AddressedChemicalReaction.Source.next current.source actions feed := rfl

theorem source_generated_atomic_next (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) :
    type_of% (CPS1AddressedChemicalReaction.Source.consumed_source current.source actions feed) ∧
      (next current actions feed).source = CPS1AddressedChemicalReaction.Source.next current.source actions feed ∧
      current.history.Sublist (next current actions feed).history ∧
      (∀ renewal before carrier,
        Step.updated renewal before carrier ∈
          (run current.history (CPS1AddressedChemicalReaction.Source.execution current.source actions feed).fired).steps →
        carrier ∈ (next current actions feed).history ∧ carrier = grown before renewal ∧
        Aligned carrier.atoms carrier.chain ∧ CompleteBonds carrier ∧
        before.Sublist carrier.atoms ∧ (∀ atom ∈ before, atom ∈ carrier.atoms) ∧
        (∃ event ∈ (CPS1AddressedChemicalReaction.Source.execution current.source actions feed).fired,
          carrier.material ∈ event.created (Reaction.products frame))) := by
  have path := run_path current.history (CPS1AddressedChemicalReaction.Source.execution current.source actions feed).fired
  exact ⟨CPS1AddressedChemicalReaction.Source.consumed_source current.source actions feed,rfl,
    path_history_preserved _ _ _ _ path,path_updates _ _ _ _ path⟩

theorem next_history_water (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (carrier : Carrier frame) (held : carrier ∈ current.history) (water : Water) (slot : WaterAtom)
    (present : ∃ atom ∈ carrier.atoms, atom.origin = .water water slot) :
    ∃ retained ∈ (next current actions feed).history,
      ∃ atom ∈ retained.atoms, atom.origin = .water water slot :=
  ⟨carrier,(source_generated_atomic_next current actions feed).2.2.1.subset held,present⟩

def advanceAll (current : Occurrence frame)
    (inputs : List CPS1AddressedChemicalReaction.Source.Input) : Occurrence frame :=
  List.rec (motive := fun _ => Occurrence frame → Occurrence frame)
    (fun prior => prior)
    (fun input _ recur prior => recur (next prior input.1 input.2)) inputs current

theorem advance_all_nil (current : Occurrence frame) : advanceAll current [] = current := rfl

theorem advance_all_cons (current : Occurrence frame)
    (input : CPS1AddressedChemicalReaction.Source.Input)
    (rest : List CPS1AddressedChemicalReaction.Source.Input) :
    advanceAll current (input :: rest) = advanceAll (next current input.1 input.2) rest := rfl

theorem advance_all_source (current : Occurrence frame)
    (inputs : List CPS1AddressedChemicalReaction.Source.Input) :
    (advanceAll current inputs).source =
      CPS1AddressedChemicalReaction.Source.advanceAll current.source inputs := by
  induction inputs generalizing current with
  | nil => rfl
  | cons input rest ih =>
    simpa only [advance_all_cons,CPS1AddressedChemicalReaction.Source.advance_all_cons,next_source] using
      ih (next current input.1 input.2)

theorem advance_all_retained (current : Occurrence frame)
    (inputs : List CPS1AddressedChemicalReaction.Source.Input) :
    current.history.Sublist (advanceAll current inputs).history ∧
      current.stages.Sublist (advanceAll current inputs).stages := by
  induction inputs generalizing current with
  | nil => exact ⟨List.Sublist.refl _,List.Sublist.refl _⟩
  | cons input rest ih =>
    have later := ih (next current input.1 input.2)
    exact ⟨(source_generated_atomic_next current input.1 input.2).2.2.1.trans later.1,
      (List.sublist_append_left current.stages _).trans later.2⟩

def requested (prior : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (inputs : List CPS1AddressedChemicalReaction.Source.Input) : Occurrence frame :=
  advanceAll (start (CPS1AddressedChemicalReaction.Source.start prior)) inputs

theorem requested_source (prior : CPS1LocalChemicalExecution.Source.Occurrence frame)
    (inputs : List CPS1AddressedChemicalReaction.Source.Input) :
    (requested prior inputs).source = CPS1AddressedChemicalReaction.Source.requested prior inputs :=
  advance_all_source _ inputs

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
  let current := start (CPS1AddressedChemicalReaction.Source.start previous.2)
  pure ⟨previous.1,next current (actions ++ CPS1LocalChemicalExecution.Source.chemicalActions) feed⟩

theorem from_source_project
    (edits : SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) :
    (fromSource edits water additional path recycleFeed scanFeed bodyFeed depth actions feed).map
      (fun current => ⟨current.1,current.2.source⟩) =
      CPS1AddressedChemicalReaction.Source.fromSource edits water additional path
        recycleFeed scanFeed bodyFeed depth actions feed := by
  unfold fromSource CPS1AddressedChemicalReaction.Source.fromSource
  cases CPS1LocalChemicalExecution.Source.actualCapture edits water additional path recycleFeed scanFeed bodyFeed depth with
  | none => rfl
  | some source => rfl

end CPS1AddressedHydrolysis.Atomic
