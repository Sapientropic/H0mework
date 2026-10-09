import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveSourceEntry.Entry
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Closure

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace CPS1ReactiveSourceEntry.NativeSource
noncomputable section
open CPS1Deformation CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
variable {frame : CPS1Recycling.Frame}

def NativeGather (state : Material frame) : Prop :=
  CPS1AtomicDynamics.Body.gather
    (CPS1EnzymeBath.Joint.particles frame state.currentJoint)
    state.currentJoint.rows = .ok state.currentNodes

def GatherStock (stock : Stock frame) : Prop :=
  ∀ state, Species.deformed state ∈ stock → NativeGather state

theorem current_row_map_lookup (state : Material frame)
    (rows : List (CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row))
    (address : CPS1AtomicDynamics.Charged.Address) :
    CPS1AtomicDynamics.Body.row? (rows.map state.currentRow) address =
      (CPS1AtomicDynamics.Body.row? rows address).map
        (fun row => (state.currentRow (address,row)).2) := by
  induction rows with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨native,row⟩
    by_cases same : native = address
    · subst native
      simp [CPS1AtomicDynamics.Body.row?, Material.currentRow]
    · simpa [CPS1AtomicDynamics.Body.row?, Material.currentRow, same] using ih

-- Both complete node and row lists use this same deterministic address-preserving map.
theorem material_gather_from_reference (state : Material frame)
    (actual : CPS1AtomicDynamics.Body.gather
      (CPS1EnzymeBath.Joint.particles frame state.reference.geometry.originJoint)
      state.reference.geometry.originJoint.rows = .ok state.reference.geometry.nodes) :
    NativeGather state := by
  have paid := CPS1AtomicDynamics.Body.gather_source _ _ _ actual
  apply CPS1AtomicDynamics.Body.gather_exact _ _ ?_ _ ?_ ?_
  · change state.currentNodes.map CPS1AtomicDynamics.Body.Node.particle =
      CPS1EnzymeBath.Joint.particles frame state.reference.geometry.originJoint
    rw [CPS1Deformation.current_nodes_particles]
    exact paid.1
  · intro node member
    rcases List.mem_map.mp member with ⟨original,present,rfl⟩
    have known := (paid.2 original present).2
    change CPS1AtomicDynamics.Body.row?
      (state.reference.geometry.originJoint.rows.map state.currentRow)
      original.particle.address =
        some ((state.currentRow (original.particle.address,original.row)).2)
    rw [current_row_map_lookup, known]
    rfl
  · intro node member
    rcases List.mem_map.mp member with ⟨original,present,rfl⟩
    change 0 < (state.currentRow (original.particle.address,original.row)).2.inertia
    dsimp only [Material.currentRow]
    cases selected : state.nuclearIndex? original.particle.address with
    | none =>
      change 0 < original.row.inertia
      exact (paid.2 original present).1
    | some index =>
      change 0 < (CPS1MolecularFrame.nucleus state.reference index).row.inertia
      exact (paid.2 _ (List.mem_of_mem_filter
        (CPS1MolecularFrame.nucleus_mem state.reference index))).1

theorem adopt_native_gather (reference : CPS1MolecularFrame.Material frame)
    (next : Material frame) (actual : adopt? reference = .ok next) : NativeGather next := by
  obtain ⟨occupied,_,same,_,_,gathered,_⟩ := adopt_outcome reference next actual
  rw [same]
  apply material_gather_from_reference
  exact gathered

theorem reprice_native_gather (state : Material frame) (reserve : ℝ)
    (actual : NativeGather state) : NativeGather (state.reprice reserve) := by
  unfold NativeGather
  rw [reprice_current_joint_particles, reprice_current_joint_rows, reprice_current_nodes]
  exact actual

theorem deposit_native_gather (state next : Material frame) (amount : ℝ)
    (prior : NativeGather state) (actual : state.deposit? amount = .ok next) :
    NativeGather next := by
  unfold Material.deposit? at actual
  split at actual
  · cases actual
  · cases Except.ok.inj actual
    exact reprice_native_gather state _ prior

theorem retained_stock_gather (stock : CPS1MolecularFrame.Stock frame) :
    GatherStock (stock.map Species.retained) := by
  intro state member
  rcases List.mem_map.mp member with ⟨species,_,same⟩
  cases same

theorem gather_stock_subset {left right : Stock frame}
    (subset : ∀ species ∈ right, species ∈ left) (generated : GatherStock left) :
    GatherStock right := fun state member => generated state (subset _ member)

theorem gather_stock_append {left right : Stock frame}
    (first : GatherStock left) (second : GatherStock right) : GatherStock (left ++ right) := by
  intro state member
  rcases List.mem_append.mp member with old | fresh
  · exact first state old
  · exact second state fresh

theorem reaction_gather (reaction : Reaction frame)
    (generated : GatherStock (reaction.reactants frame)) :
    GatherStock (reaction.products frame) := by
  intro state member
  cases reaction with
  | retained old =>
    exact retained_stock_gather _ state member
  | adopt reference =>
    cases actual : adopt? reference with
    | error failure => simp [CPS1Deformation.Reaction.products, actual] at member
    | ok next =>
      have same : state = next := by simpa [CPS1Deformation.Reaction.products, actual] using member
      subst state
      exact adopt_native_gather reference next actual
  | pulse before time =>
    cases actual : before.pulse? time with
    | error failure => simp [CPS1Deformation.Reaction.products, actual] at member
    | ok next =>
      have same : state = next.1 := by simpa [CPS1Deformation.Reaction.products, actual] using member
      subst state
      exact (pulse_grounded before next time actual).2.2.2.2.1
  | deposit before amount =>
    have prior := generated before (by simp [CPS1Deformation.Reaction.reactants])
    cases actual : before.deposit? amount with
    | error failure => simp [CPS1Deformation.Reaction.products, actual] at member
    | ok next =>
      have same : state = next := by simpa [CPS1Deformation.Reaction.products, actual] using member
      subst state
      exact deposit_native_gather before next amount prior actual
  | keepDeformed before =>
    have same : state = before := by simpa [CPS1Deformation.Reaction.products] using member
    subst state
    exact generated before (by simp [CPS1Deformation.Reaction.reactants])
  | requireCarrier => simp [CPS1Deformation.Reaction.products] at member

-- Same inventory decomposition as the paid fire_good; no program-history premise.
theorem fire_gather (reaction : Reaction frame) (stock next : Stock frame)
    (generated : GatherStock stock)
    (actual : Inventory.fire (CPS1Deformation.Reaction.reactants frame) (CPS1Deformation.Reaction.products frame)
      reaction stock = .ok next) : GatherStock next := by
  unfold Inventory.fire at actual
  cases consumed : Inventory.consume (reaction.reactants frame) stock with
  | error missing => simp [consumed] at actual
  | ok remainder =>
    simp only [consumed, Except.ok.injEq] at actual
    subst next
    have decomposition := Inventory.consume_perm _ _ _ consumed
    have input := gather_stock_subset
      (fun species member => decomposition.mem_iff.mpr (List.mem_append_left _ member)) generated
    have rest := gather_stock_subset
      (fun species member => decomposition.mem_iff.mpr (List.mem_append_right _ member)) generated
    exact gather_stock_append (reaction_gather reaction input) rest

theorem execute_gather (program : List (Reaction frame)) (stock : Stock frame)
    (generated : GatherStock stock) : GatherStock (execute frame program stock).stock := by
  induction program generalizing stock with
  | nil => exact generated
  | cons action rest ih =>
    change GatherStock (Inventory.execute (CPS1Deformation.Reaction.reactants frame)
      (CPS1Deformation.Reaction.products frame) (action :: rest) stock).stock
    cases fired : Inventory.fire (CPS1Deformation.Reaction.reactants frame) (CPS1Deformation.Reaction.products frame)
        action stock with
    | error missing => rw [Inventory.execute_cons, fired]; exact generated
    | ok next => rw [Inventory.execute_cons, fired]; exact ih next (fire_gather action stock next generated fired)

theorem raw_gather (action : Source.RawAction) : GatherStock (action.material frame) := by
  cases action with
  | old prior => exact retained_stock_gather _
  | adopt => simp [GatherStock, Source.RawAction.material]
  | pulse time => simp [GatherStock, Source.RawAction.material]
  | deposit amount => simp [GatherStock, Source.RawAction.material]

theorem actions_gather (actions : List Source.RawAction) :
    GatherStock (actions.flatMap (Source.RawAction.material frame)) := by
  induction actions with
  | nil => simp [GatherStock]
  | cons action rest ih => exact gather_stock_append (raw_gather action) ih

theorem feed_gather (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    GatherStock (feed.map (fun kind => Species.retained (.retained (.retained (.retained
      (.retained (CPS1EnzymeBath.componentSpecies frame kind))))))) := by
  intro state member
  rcases List.mem_map.mp member with ⟨kind,_,same⟩
  cases same

theorem advance_gather (cursor : Source.Cursor frame) (actions : List Source.RawAction)
    (feed : List CPS1EnzymeBath.Primary.TemplateKind) (generated : GatherStock cursor.stock) :
    GatherStock (Source.advance frame cursor actions feed).stock :=
  execute_gather _ _
    (gather_stock_append (gather_stock_append generated (feed_gather feed)) (actions_gather actions))

theorem from_actual_advance_gather (previous : CPS1MolecularFrame.Source.Occurrence frame)
    (actions : List Source.RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    GatherStock (Source.advance frame (Source.fromActual frame previous).current actions feed).stock :=
  advance_gather _ actions feed (retained_stock_gather _)

-- Source.execution only needs to destruct its own previous Option and rewrite its actual result.
theorem execution_gather
    (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (electronicActions : List CPS1ElectronicSource.Source.RawAction) (electronicFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (nuclearActions : List CPS1QuantumNuclear.Source.RawAction) (nuclearFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (followingActions : List CPS1Following.Source.RawAction) (followingFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (molecularActions : List CPS1MolecularFrame.Source.RawAction) (molecularFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List Source.RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind)
    (current : Σ frame : CPS1Recycling.Frame, Source.Occurrence frame)
    (actual : Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
      followingActions followingFeed molecularActions molecularFeed actions feed = some current) :
    GatherStock current.2.current.stock := by
  unfold Source.execution at actual
  cases prior : CPS1MolecularFrame.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
      followingActions followingFeed molecularActions molecularFeed with
  | none => simp [prior] at actual
  | some previous =>
    simp only [prior] at actual
    cases Option.some.inj actual
    exact from_actual_advance_gather previous.2 actions feed

theorem current_nuclear_row_of_gather (state : CPS1Deformation.Material frame)
    (gathered : CPS1AtomicDynamics.Body.gather
      (CPS1EnzymeBath.Joint.particles frame state.currentJoint)
      state.currentJoint.rows = .ok state.currentNodes)
    (index : CPS1MolecularFrame.NuclearIndex state.reference) :
    CPS1AtomicDynamics.Body.row? state.currentJoint.rows
      (CPS1MolecularFrame.address state.reference index) = some (state.nuclearRow index) := by
  have paid := CPS1AtomicDynamics.Body.gather_source _ _ _ gathered
  have particleUnique := CPS1AtomicDynamics.Charged.particles_unique
    (CPS1EnzymeBath.Joint.descriptorGraph frame state.currentJoint)
  change ((CPS1EnzymeBath.Joint.particles frame state.currentJoint).map
    CPS1AtomicDynamics.Charged.Particle.address).Nodup at particleUnique
  rw [← paid.1, List.map_map] at particleUnique
  have referenceUnique :
      (state.reference.geometry.nodes.map (fun node => node.particle.address)).Nodup := by
    simpa only [CPS1Deformation.Material.currentNodes, List.map_map, Function.comp_def,
      CPS1Deformation.Material.currentNode] using particleUnique
  have nuclearUnique :
      (state.reference.geometry.nuclei.map (fun node => node.particle.address)).Nodup :=
    referenceUnique.sublist (List.filter_sublist.map _)
  have injective : Function.Injective (CPS1MolecularFrame.address state.reference) := by
    intro first second same
    let first' : Fin (state.reference.geometry.nuclei.map
        (fun node => node.particle.address)).length := ⟨first.val, by rw [List.length_map]; exact first.isLt⟩
    let second' : Fin (state.reference.geometry.nuclei.map
        (fun node => node.particle.address)).length := ⟨second.val, by rw [List.length_map]; exact second.isLt⟩
    have mapped : (state.reference.geometry.nuclei.map
        (fun node => node.particle.address)).get first' =
      (state.reference.geometry.nuclei.map (fun node => node.particle.address)).get second' := by
      simpa only [CPS1MolecularFrame.address, CPS1MolecularFrame.nucleus,
        List.get_eq_getElem, List.getElem_map] using same
    have eqIndices := nuclearUnique.injective_get mapped
    have values := congrArg (fun index : Fin (state.reference.geometry.nuclei.map
      (fun node => node.particle.address)).length => index.val) eqIndices
    change first.val = second.val at values
    exact Fin.ext values
  have selected : state.nuclearIndex?
      (CPS1MolecularFrame.address state.reference index) = some index := by
    change (List.ofFn (fun next : CPS1MolecularFrame.NuclearIndex state.reference => next)).find?
      (fun next => CPS1MolecularFrame.address state.reference next =
        CPS1MolecularFrame.address state.reference index) = some index
    apply List.find?_ofFn_eq_some.mpr
    refine ⟨by simp, index, rfl, ?_⟩
    intro earlier before actual
    have eqIndex := injective (of_decide_eq_true actual)
    exact (ne_of_lt before) eqIndex
  have nativeMember : CPS1MolecularFrame.nucleus state.reference index ∈
      state.reference.geometry.nodes :=
    List.mem_of_mem_filter (CPS1MolecularFrame.nucleus_mem state.reference index)
  have currentMember := List.mem_map_of_mem (f := state.currentNode) nativeMember
  have currentRow := (paid.2 _ currentMember).2
  change CPS1AtomicDynamics.Body.row? state.currentJoint.rows
    (CPS1MolecularFrame.address state.reference index) =
      some ((state.currentRow (CPS1MolecularFrame.address state.reference index,
        (CPS1MolecularFrame.nucleus state.reference index).row)).2) at currentRow
  simpa only [CPS1Deformation.Material.currentRow, selected] using currentRow

theorem original_rows_from_stock {current : CPS1ReactiveField.Occurrence frame}
    (material : CPS1ReactiveField.Material current)
    (generated : GatherStock current.old.current.stock) : CPS1ReactiveSourceEntry.OriginalRows material := by
  intro index
  exact current_nuclear_row_of_gather material.source.old
    (generated material.source.old material.source.held) index

end
end CPS1ReactiveSourceEntry.NativeSource
