import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.Ingress

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1PhosphorylExchange
noncomputable section
open CPS1AtomicDynamics CPS1AtomicSource CPS1SameEventFunction
open Filter
open scoped Topology BigOperators
variable {frame : CPS1Recycling.Frame}

def firstFuel : List FuelKind := [.atp,.atp,.bicarbonate]

def freshAtoms {cursor : CPS1ReactiveNuclear.SourceCursor frame} : List (Atom cursor) :=
  firstFuel.zipIdx.flatMap (fun entry => (fuelGraph entry.1).atoms.map
    (fun atom => ⟨.fuel entry.2 entry.1 atom,atom⟩))

def freshParticles {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) : List Charged.Particle :=
  (freshAtoms (cursor := cursor)).zipIdx source.atoms.length |>.flatMap
    (fun entry => Charged.atomParticles (entry.1.descriptor,entry.2))

theorem common_particles_append {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) :
    commonParticles source firstFuel = source.particles.map Classical.Particle.readout ++ freshParticles source := by
  unfold commonParticles commonAtoms
  rw [List.zipIdx_append,List.flatMap_append]
  simp only [List.length_map,Nat.zero_add,List.zipIdx_map,List.flatMap_map]
  unfold Classical.Source.particles Classical.atomParticles
  simp only [List.map_flatMap,List.map_map,Function.comp_def,List.map_id_fun']
  rfl

def firstChannel {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) : Channel :=
  ⟨0,.nucleus (source.atoms.length+28),.nucleus (source.atoms.length+25),
    .nucleus (source.atoms.length+88)⟩

private def fuelRole {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (occurrence : Nat) (kind : FuelKind) (name : String) (entry : Atom cursor × Nat) : Bool :=
  match entry.1.origin with
  | .fuel slot source atom => slot == occurrence && source == kind && atom.address.atom == name
  | _ => false

private theorem prior_role_missing {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (occurrence : Nat) (kind : FuelKind) (name : String) :
    ((source.atoms.map (fun atom => (⟨.prior atom,atom.descriptor⟩ : Atom cursor))).zipIdx).find?
      (fuelRole occurrence kind name) = none := by
  apply List.find?_eq_none.mpr
  intro entry held
  rw [List.zipIdx_map] at held
  obtain ⟨prior,_,same⟩ := List.mem_map.mp held
  subst entry
  simp [fuelRole]

private theorem common_role_slot {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (occurrence : Nat) (kind : FuelKind) (name : String) :
    (((commonAtoms source firstFuel).zipIdx).find? (fuelRole occurrence kind name)).map Prod.snd =
      (((freshAtoms (cursor := cursor)).zipIdx source.atoms.length).find?
        (fuelRole occurrence kind name)).map Prod.snd := by
  unfold commonAtoms
  rw [List.zipIdx_append,List.find?_append,prior_role_missing]
  simp only [List.length_map,Nat.zero_add]
  rfl

theorem first_channel_selected {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) :
    channel? (commonAtoms source firstFuel) firstFuel = some (firstChannel source) := by
  unfold channel?
  change (do
    let p ← (((commonAtoms source firstFuel).zipIdx).find? (fuelRole 0 .atp "28")).map Prod.snd
    let leave ← (((commonAtoms source firstFuel).zipIdx).find? (fuelRole 0 .atp "25")).map Prod.snd
    let attack ← (((commonAtoms source firstFuel).zipIdx).find? (fuelRole 2 .bicarbonate "O2")).map Prod.snd
    pure (⟨0,.nucleus p,.nucleus leave,.nucleus attack⟩ : Channel)) = some (firstChannel source)
  rw [common_role_slot,common_role_slot,common_role_slot]
  simp +decide [freshAtoms,firstFuel,fuelGraph,atpGraph,CPS1EnzymeBath.Primary.atp,
    CPS1EnzymeBath.Joint.bathAtom,bicarbonateGraph,fuelRole,firstChannel,Nat.add_assoc]

def freshRow {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height : ℝ) (entry : Charged.Particle × Nat) : Body.Row :=
  let y := if entry.1.address = (firstChannel source).phosphorus then height
    else if entry.1.address = (firstChannel source).leavingOxygen then height+1
    else if entry.1.address = (firstChannel source).attackingOxygen then height+2
    else height+4+entry.2
  ⟨transversePoint x y 0,0,1⟩

def freshNodes {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height : ℝ) : List Body.Node :=
  (freshParticles source).zipIdx.map (fun entry => ⟨entry.1,freshRow source x height entry⟩)

theorem fresh_nodes_particles {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height : ℝ) :
    (freshNodes source x height).map Body.Node.particle = freshParticles source := by
  simp only [freshNodes,List.map_map,Function.comp_def]
  exact List.zipIdx_map_fst 0 _

theorem fresh_unit_inertia {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height : ℝ) :
    ∀ node ∈ freshNodes source x height, node.row.inertia = 1 := by
  intro node held
  obtain ⟨entry,_,same⟩ := List.mem_map.mp held
  subst node
  rfl

def baseNodes {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time) (x height : ℝ) : List Body.Node :=
  step.next.nodes ++ freshNodes before.packet.source x height

theorem base_particles {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step) (x height : ℝ) :
    (baseNodes before step x height).map Body.Node.particle = commonParticles before.packet.source firstFuel := by
  rw [baseNodes,List.map_append,(actual_responded_post_source before step actual).1,
    fresh_nodes_particles,common_particles_append]

theorem fresh_particles_unique {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) :
    ((freshParticles source).map Charged.Particle.address).Nodup := by
  have generated := common_addresses_unique source firstFuel
  rw [common_particles_append,List.map_append] at generated
  exact (List.nodup_append.mp generated).2.1

private theorem fresh_row_separated {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height : ℝ) (first second : Charged.Particle × Nat)
    (addresses : first.1.address ≠ second.1.address) (ordinals : first.2 ≠ second.2) :
    (freshRow source x height first).position ≠ (freshRow source x height second).position := by
  intro equal
  have read := congrArg (fun point : Body.Point => point (1 : Fin 3)) equal
  have firstNonnegative : 0 ≤ (first.2 : ℝ) := Nat.cast_nonneg _
  have secondNonnegative : 0 ≤ (second.2 : ℝ) := Nat.cast_nonneg _
  simp only [freshRow,transversePoint,Matrix.cons_val_one,Matrix.cons_val_zero] at read
  split_ifs at read
  all_goals first
    | apply addresses; calc
        first.1.address = (firstChannel source).phosphorus := by assumption
        _ = second.1.address := by symm; assumption
    | apply addresses; calc
        first.1.address = (firstChannel source).leavingOxygen := by assumption
        _ = second.1.address := by symm; assumption
    | apply addresses; calc
        first.1.address = (firstChannel source).attackingOxygen := by assumption
        _ = second.1.address := by symm; assumption
    | linarith
    | apply ordinals; exact_mod_cast (by linarith : (first.2 : ℝ) = (second.2 : ℝ))

theorem fresh_nodes_ready {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height : ℝ) : Body.ready (freshNodes source x height) := by
  have addresses : ((freshParticles source).zipIdx.map (fun entry => entry.1.address)).Nodup := by
    change ((freshParticles source).zipIdx.map (Charged.Particle.address ∘ Prod.fst)).Nodup
    rw [← List.map_map,List.zipIdx_map_fst]
    exact fresh_particles_unique source
  have ordinals : ((freshParticles source).zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' _
  apply List.pairwise_map.mpr
  exact ((List.pairwise_map.mp addresses).and (List.pairwise_map.mp ordinals)).imp
    (fun {first second} different => fresh_row_separated source x height first second different.1 different.2)

theorem fresh_nodes_above {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height : ℝ) (node : Body.Node)
    (held : node ∈ freshNodes source x height) : height ≤ node.row.position (1 : Fin 3) := by
  obtain ⟨entry,_,same⟩ := List.mem_map.mp held
  subst node
  have nonnegative : 0 ≤ (entry.2 : ℝ) := Nat.cast_nonneg _
  simp only [freshRow,transversePoint,Matrix.cons_val_one,Matrix.cons_val_zero]
  split_ifs <;> linarith

theorem base_ready {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time) (x height : ℝ)
    (above : ∀ node ∈ step.next.nodes, node.row.position (1 : Fin 3) < height) :
    Body.ready (baseNodes before step x height) := by
  apply List.pairwise_append.mpr
  refine ⟨step.nextReady,fresh_nodes_ready _ x height,?_⟩
  intro old oldHeld fresh freshHeld same
  have y := congrArg (fun point : Body.Point => point (1 : Fin 3)) same
  have high := fresh_nodes_above before.packet.source x height fresh freshHeld
  have low := above old oldHeld
  linarith

def baseRaw {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    (source : Classical.Source cursor) (x height : ℝ) : Raw :=
  ⟨firstFuel,(freshNodes source x height).map (fun node => (node.particle.address,node.row)),0,0⟩

theorem base_gathered {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step) (x height : ℝ) :
    Body.gather (commonParticles before.packet.source firstFuel)
      (step.next.nodes.map (fun node => (node.particle.address,node.row)) ++
        (baseRaw before.packet.source x height).rows) = .ok (baseNodes before step x height) := by
  have particles := base_particles before step actual x height
  have unique : ((baseNodes before step x height).map (fun node => node.particle.address)).Nodup := by
    change ((baseNodes before step x height).map (Charged.Particle.address ∘ Body.Node.particle)).Nodup
    rw [← List.map_map,particles]
    exact common_addresses_unique _ _
  apply Body.gather_exact _ _ particles
  · intro node held
    have reported := Body.row_at_source _ unique node held
    simpa only [baseNodes,baseRaw,List.map_append] using reported
  · intro node held
    rcases List.mem_append.mp held with old | fresh
    · exact (actual_responded_post_source before step actual).2.2 node old
    · rw [fresh_unit_inertia _ _ _ node fresh]
      norm_num

theorem base_rows_compatible {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step) (x height : ℝ) :
    Classical.rowCompatible (step.next.nodes.map (fun node => (node.particle.address,node.row)))
      (baseRaw before.packet.source x height).rows = .ok () := by
  classical
  have particles := base_particles before step actual x height
  have unique : ((baseNodes before step x height).map (fun node => node.particle.address)).Nodup := by
    change ((baseNodes before step x height).map (Charged.Particle.address ∘ Body.Node.particle)).Nodup
    rw [← List.map_map,particles]
    exact common_addresses_unique _ _
  have different := (List.nodup_append.mp (by
    simpa only [baseNodes,List.map_append] using unique)).2.2
  have rowMissing (old : Body.Node) (held : old ∈ step.next.nodes) :
      Body.row? (baseRaw before.packet.source x height).rows old.particle.address = none := by
    unfold Body.row? baseRaw
    have missing : ((freshNodes before.packet.source x height).map
        (fun node => (node.particle.address,node.row))).find?
        (fun entry => entry.1 = old.particle.address) = none := by
      apply List.find?_eq_none.mpr
      intro entry present
      obtain ⟨fresh,freshHeld,same⟩ := List.mem_map.mp present
      subst entry
      have distinct := different old.particle.address (List.mem_map_of_mem held)
        fresh.particle.address (List.mem_map_of_mem freshHeld)
      simpa only [decide_eq_true_eq] using Ne.symm distinct
    rw [missing]
    rfl
  unfold Classical.rowCompatible
  split
  · rfl
  · rename_i entry found
    have selected := List.find?_some found
    have held := List.mem_of_find?_eq_some found
    obtain ⟨old,oldHeld,same⟩ := List.mem_map.mp held
    subst entry
    rw [rowMissing old oldHeld] at selected
    cases selected

theorem base_unit_inertia {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time) (x height : ℝ)
    (oldUnit : ∀ node ∈ step.next.nodes, node.row.inertia = 1) :
    ∀ node ∈ baseNodes before step x height, node.row.inertia = 1 := by
  intro node held
  rcases List.mem_append.mp held with old | fresh
  · exact oldUnit node old
  · exact fresh_unit_inertia _ _ _ node fresh

private theorem measured_mass_unit (nodes : List Body.Node)
    (unit : ∀ node ∈ nodes, node.row.inertia = 1) :
    ((nodes.find? (fun node => match node.particle.address with
      | .electron .. => true | _ => false)).map (fun node => node.row.inertia)).getD 1 = 1 := by
  cases found : nodes.find? (fun node => match node.particle.address with
    | .electron .. => true | _ => false) with
  | none => rfl
  | some node =>
    simp only [Option.map_some,Option.getD_some]
    exact unit node (List.mem_of_find?_eq_some found)

theorem base_admitted {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step) (x height : ℝ)
    (oldUnit : ∀ node ∈ step.next.nodes, node.row.inertia = 1)
    (above : ∀ node ∈ step.next.nodes, node.row.position (1 : Fin 3) < height) :
    ∃ source : Common before step (baseRaw before.packet.source x height),
      admit before step (baseRaw before.packet.source x height) = .ok source ∧
      source.nodes = baseNodes before step x height ∧ source.electronInertia = 1 := by
  classical
  have atp : ¬((baseRaw before.packet.source x height).fuel.filter (· == .atp)).length < 2 := by
    norm_num [baseRaw,firstFuel]
  have bicarbonate : ¬FuelKind.bicarbonate ∉ (baseRaw before.packet.source x height).fuel := by
    simp [baseRaw,firstFuel]
  have compatible := base_rows_compatible before step actual x height
  have gathered := base_gathered before step actual x height
  have ready := base_ready before step x height above
  have allUnit := base_unit_inertia before step x height oldUnit
  have mass := measured_mass_unit (baseNodes before step x height) allUnit
  have uniform : ∀ node ∈ baseNodes before step x height,
      match node.particle.address with | .nucleus _ => True | .electron .. => node.row.inertia = 1 := by
    intro node held
    cases node.particle.address
    · trivial
    · exact allUnit node held
  unfold admit
  rw [dif_neg atp,dif_neg bicarbonate,compatible]
  dsimp only [baseRaw]
  dsimp only [baseRaw] at gathered
  split
  · rename_i failure found
    have impossible := gathered.symm.trans found
    cases impossible
  · rename_i nodes found
    have identity := Except.ok.inj (found.symm.trans gathered)
    subst nodes
    rw [dif_pos ready]
    change ∃ source : Common before step (baseRaw before.packet.source x height),
      (if equal : ∀ node ∈ baseNodes before step x height,
      match node.particle.address with | .nucleus _ => True | .electron .. => node.row.inertia =
        (((baseNodes before step x height).find? (fun node => match node.particle.address with
          | .electron .. => true | _ => false)).map (fun node => node.row.inertia)).getD 1 then
        Except.ok _ else Except.error Failure.unequalElectronInertia) = Except.ok source ∧
        source.nodes = baseNodes before step x height ∧ source.electronInertia = 1
    simp only [mass,dif_pos uniform]
    exact ⟨_,rfl,rfl,mass⟩

def oldHeight (nodes : List Body.Node) : ℝ :=
  (nodes.map (fun node => |node.row.position (1 : Fin 3)|)).sum+5

theorem old_height_positive (nodes : List Body.Node) : 4 < oldHeight nodes := by
  have nonnegative : 0 ≤ (nodes.map (fun node => |node.row.position (1 : Fin 3)|)).sum := by
    apply List.sum_nonneg
    intro value held
    obtain ⟨node,_,same⟩ := List.mem_map.mp held
    subst value
    exact abs_nonneg _
  unfold oldHeight
  linarith

theorem old_below_height (nodes : List Body.Node) (node : Body.Node) (held : node ∈ nodes) :
    node.row.position (1 : Fin 3)+4 < oldHeight nodes := by
  have allNonnegative : ∀ value ∈ nodes.map (fun node => |node.row.position (1 : Fin 3)|), 0 ≤ value := by
    intro value present
    obtain ⟨entry,_,same⟩ := List.mem_map.mp present
    subst value
    exact abs_nonneg _
  have bound := List.single_le_sum allNonnegative |node.row.position (1 : Fin 3)|
    (List.mem_map_of_mem held)
  have signed := le_abs_self (node.row.position (1 : Fin 3))
  unfold oldHeight
  linarith

def particleElectronCount (particles : List Charged.Particle) : Nat :=
  (particles.filter (fun particle => match particle.address with
    | .electron .. => true | .nucleus _ => false)).length

theorem electron_count_particle_projection (nodes : List Body.Node) :
    electronCount nodes = particleElectronCount (nodes.map Body.Node.particle) := by
  unfold electronCount particleElectronCount
  rw [List.filter_map,List.length_map]
  rfl

theorem base_electron_count {cursor : CPS1ReactiveNuclear.SourceCursor frame}
    {priorRaw : Classical.Raw} (before : Classical.Current cursor priorRaw)
    (step : Classical.NativeStep before priorRaw.time)
    (actual : Classical.fromCursor cursor priorRaw = .responded before step) (x height : ℝ) :
    electronCount (baseNodes before step x height) = particleElectronCount
      (commonParticles before.packet.source firstFuel) := by
  rw [electron_count_particle_projection,base_particles before step actual x height]

theorem initial_bond_count (before after : List Body.Node) (same : electronCount before = electronCount after)
    (first second : Body.Point) :
    bondWeight before (initialOccupation before) first second =
      bondWeight after (initialOccupation after) first second := by
  unfold bondWeight
  rw [initial_density_kernel,initial_density_kernel]
  let kernel (count : Nat) : ℂ := ∑ electron : Fin count,
    star (CPS1ElectronicSource.spatialValue 0 (count+1) ⟨electron.val/2,by omega⟩ 0
      (fun axis => first axis))*
    CPS1ElectronicSource.spatialValue 0 (count+1) ⟨electron.val/2,by omega⟩ 0
      (fun axis => second axis)
  change Complex.normSq (kernel (electronCount before)) = Complex.normSq (kernel (electronCount after))
  rw [same]

end
end CPS1PhosphorylExchange
