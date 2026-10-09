import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveNuclear.Differential
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Response
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PositivePulse.SuccessNeighborhood

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

/- Owned joint construction. The original Delivery root and the upstream
   Birth/Germ/Differential stay fixed. -/
namespace CPS1ReactiveJointNuclear
noncomputable section
open CPS1ElectronicSource CPS1ReactiveNuclear
open CPS1ReactiveField CPS1ReactiveField.Carried
open scoped BigOperators InnerProductSpace Matrix Topology
variable {frame : CPS1Recycling.Frame}
variable {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}

def normalizationAt (germ : Germ root state) (positions : germ.Configuration) :
    Matrix state.ElectronIndex state.ElectronIndex ℂ :=
  CPS1PositivePulse.totalNormalization (𝕜 := ℂ)
    (fun electron => occupiedJetAt germ positions electron 0)

/-- The derivative is of the actual finite normalization fixed by this source
germ. Differentiability is paid in Occupation; no guessed rate or external
normalizer is admitted to the physical action. -/
def normalizationRate (germ : Germ root state) (direction : germ.Configuration) :
    Matrix state.ElectronIndex state.ElectronIndex ℂ :=
  fderiv ℝ (normalizationAt germ) germ.positions direction

def occupiedMetricTangent (germ : Germ root state) (direction : germ.Configuration) :
    germ.Coefficients := state.occupied * normalizationRate germ direction

def nuclearWork (germ : Germ root state) (direction : germ.Configuration) : ℝ :=
  nuclearDifferential germ (direction,0) + occupiedDifferential germ (occupiedMetricTangent germ direction)

/-- This uses the paid full E nuclear and occupied derivatives together. The
occupied term pays the moving-metric correction rather than holding C off the
orthonormal carrier while differentiating the physical nuclear response. -/
def force (germ : Germ root state) : germ.Configuration :=
  fun id axis => -(nuclearWork germ (Pi.single id (Pi.single axis 1)))

def movedPositions (germ : Germ root state) (time : ℝ) : germ.Configuration :=
  fun id => germ.positions id + (time / (germ.node id).row.inertia) • germ.momenta id +
    (time^2 / (2 * (germ.node id).row.inertia)) • force germ id

def movedMomenta (germ : Germ root state) (time : ℝ) : germ.Configuration :=
  germ.momenta + time • force germ

def electronicKick (state : Snapshot) (time : ℝ) :
    Matrix state.PrimitiveIndex state.ElectronIndex ℂ :=
  CPS1ReactiveFieldDynamics.increment state
    (CPS1ReactiveFieldDynamics.responseCoordinates state time)

/-- The Cayley increment and nuclear motion consume the same current full E.
The nuclear motion acts on every common Id, including the old bath. -/
def preResponse (germ : Germ root state) (time : ℝ) : Snapshot :=
  germ.snapshotAt ((movedPositions germ time,movedMomenta germ time),electronicKick state time)

theorem force_full_energy (germ : Germ root state) (id : germ.Id) (axis : Fin 3) :
    force germ id axis =
      -(nuclearDifferential germ (Pi.single id (Pi.single axis 1),0) +
        occupiedDifferential germ (occupiedMetricTangent germ (Pi.single id (Pi.single axis 1)))) := rfl

theorem force_raw_nuclear_and_metric (germ : Germ root state) (id : germ.Id) (axis : Fin 3) :
    force germ id axis = nuclearForce germ id axis -
      occupiedDifferential germ (occupiedMetricTangent germ (Pi.single id (Pi.single axis 1))) := by
  simp only [force,nuclearWork,nuclearForce]
  ring

theorem moved_positions_zero (germ : Germ root state) : movedPositions germ 0 = germ.positions := by
  funext id
  simp only [movedPositions,zero_div,zero_pow (by decide : 2 ≠ 0),zero_smul,add_zero]

theorem moved_momenta_zero (germ : Germ root state) : movedMomenta germ 0 = germ.momenta := by
  simp only [movedMomenta,zero_smul,add_zero]

theorem moved_positions_continuousAt (germ : Germ root state) (point : ℝ) :
    ContinuousAt (movedPositions germ) point := by
  apply continuousAt_pi.mpr
  intro id
  exact (continuousAt_const.add
    ((continuousAt_id.div_const (germ.node id).row.inertia).smul continuousAt_const)).add
      (((continuousAt_id.pow 2).div_const (2 * (germ.node id).row.inertia)).smul continuousAt_const)

theorem moved_momenta_continuousAt (germ : Germ root state) (point : ℝ) :
    ContinuousAt (movedMomenta germ) point :=
  continuousAt_const.add (continuousAt_id.smul continuousAt_const)

theorem moving_nuclei_ready_eventually (germ : Germ root state) :
    ∀ᶠ time in 𝓝 (0 : ℝ), CPS1AtomicDynamics.Body.ready
      (List.ofFn (germ.nodeAt (movedPositions germ time) (movedMomenta germ time))) := by
  have currentReady : CPS1AtomicDynamics.Body.ready
      (List.ofFn (germ.nodeAt (movedPositions germ 0) (movedMomenta germ 0))) := by
    rw [moved_positions_zero,moved_momenta_zero,
      show germ.nodeAt germ.positions germ.momenta = state.nuclei.get from funext germ.node_current,
      List.ofFn_get]
    exact germ.ready
  have indexedReady : (List.finRange state.nuclei.length).Pairwise (fun first second =>
      euclideanPoint (movedPositions germ 0 (germ.nuclearId first)) ≠
        euclideanPoint (movedPositions germ 0 (germ.nuclearId second))) := by
    simpa only [CPS1AtomicDynamics.Body.ready,List.ofFn_eq_map,List.pairwise_map,Germ.nodeAt]
      using currentReady
  have generated := CPS1PositivePulse.pairwise_positions_eventually
    (List.finRange state.nuclei.length)
    (fun time index => euclideanPoint (movedPositions germ time (germ.nuclearId index)))
    (fun index _ => CPS1Deformation.pointDifferential.continuous.continuousAt.comp
      ((continuous_apply (germ.nuclearId index)).continuousAt.comp (moved_positions_continuousAt germ 0)))
    indexedReady
  simpa only [CPS1AtomicDynamics.Body.ready,List.ofFn_eq_map,List.pairwise_map,Germ.nodeAt] using generated

theorem electronic_kick_zero (state : Snapshot) : electronicKick state 0 = state.occupied := by
  rw [electronicKick,CPS1ReactiveFieldDynamics.response_coordinates_zero,
    CPS1ReactiveFieldDynamics.increment_current]

theorem pre_response_zero (germ : Germ root state) : preResponse germ 0 = state := by
  rw [preResponse,moved_positions_zero,moved_momenta_zero,electronic_kick_zero]
  exact germ.snapshot_current

theorem pre_response_storage (germ : Germ root state) (time : ℝ) :
    (preResponse germ time).PrimitiveIndex = state.PrimitiveIndex ∧
    (preResponse germ time).ElectronIndex = state.ElectronIndex ∧
    (preResponse germ time).occupied = electronicKick state time ∧
    (preResponse germ time).nuclei =
      List.ofFn (germ.nodeAt (movedPositions germ time) (movedMomenta germ time)) ∧
    (preResponse germ time).waterOrigins = state.waterOrigins ∧
    (preResponse germ time).electronInertia = state.electronInertia ∧
    (preResponse germ time).reserve = state.reserve ∧
    (preResponse germ time).Ne = state.Ne := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem primitive_motion_generated (germ : Germ root state) (time : ℝ)
    (primitive : state.PrimitiveIndex) :
    ((preResponse germ time).primitive primitive).origin = (state.primitive primitive).origin ∧
    ((preResponse germ time).primitive primitive).mode = (state.primitive primitive).mode ∧
    ((preResponse germ time).primitive primitive).spin = (state.primitive primitive).spin ∧
    ((preResponse germ time).primitive primitive).centre =
      movedPositions germ time (germ.primitiveId primitive) := ⟨rfl,rfl,rfl,rfl⟩

theorem nuclear_motion_generated (germ : Germ root state) (time : ℝ)
    (slot : Fin state.nuclei.length) :
    (germ.nodeAt (movedPositions germ time) (movedMomenta germ time) slot).particle =
      (state.nuclei.get slot).particle ∧
    (germ.nodeAt (movedPositions germ time) (movedMomenta germ time) slot).row.inertia =
      (state.nuclei.get slot).row.inertia ∧
    (germ.nodeAt (movedPositions germ time) (movedMomenta germ time) slot).row.position =
      euclideanPoint (movedPositions germ time (germ.nuclearId slot)) ∧
    (germ.nodeAt (movedPositions germ time) (movedMomenta germ time) slot).row.momentum =
      euclideanPoint (movedMomenta germ time (germ.nuclearId slot)) := ⟨rfl,rfl,rfl,rfl⟩

abbrev KeyRows (root : CPS1Deformation.Source.Occurrence frame) :=
  List (Key root × CPS1AtomicDynamics.Body.Row)

/-- This is the complete live nuclear stock. No current Graph slot resolves an
old identity; the source-born slot equivalence is only its dependent readout. -/
def nuclearRows (germ : Germ root state) (time : ℝ) : KeyRows root :=
  List.ofFn (fun slot : Fin state.nuclei.length =>
    ((germ.nuclearId slot).val,
      (germ.nodeAt (movedPositions germ time) (movedMomenta germ time) slot).row))

def liveRow (germ : Germ root state) (time : ℝ) (id : germ.Id) : CPS1AtomicDynamics.Body.Row :=
  (germ.nodeAt (movedPositions germ time) (movedMomenta germ time)
    ((germ.birth.slotEquiv germ.unique).symm id)).row

theorem live_row_zero (germ : Germ root state) (id : germ.Id) :
    liveRow germ 0 id = (germ.node id).row := by
  rw [liveRow,moved_positions_zero,moved_momenta_zero,germ.node_current]
  rfl

theorem live_row_inertia (germ : Germ root state) (time : ℝ) (id : germ.Id) :
    (liveRow germ time id).inertia = (germ.node id).row.inertia := rfl

theorem live_row_position_continuous (germ : Germ root state) (id : germ.Id) :
    ContinuousAt (fun time : ℝ => (liveRow germ time id).position) 0 := by
  change ContinuousAt (fun time : ℝ => euclideanPoint (movedPositions germ time
    (germ.nuclearId ((germ.birth.slotEquiv germ.unique).symm id)))) 0
  exact CPS1Deformation.pointDifferential.continuous.continuousAt.comp
    ((continuous_apply _).continuousAt.comp (moved_positions_continuousAt germ 0))

/-- `.old slot` is interpreted only in the original seeded enzyme graph owned
at birth. Bath keys never pass through this partial reactive restriction. -/
def originKey? (germ : Germ root state) : CPS1AddressedHydrolysis.Origin → Option (Key root)
  | .old slot =>
    ((CPS1AtomicSource.Graph.fromChain frame germ.birth.owner.currentJoint.originBody.source).atoms[slot]?).map
      Key.enzyme
  | .water water atom => some (.water water atom)

/-- This membership is in the birth-owned carrier. The resulting numeric
readout belongs to this exact germ Snapshot, not a later body's slot ordering. -/
def originId? (germ : Germ root state) (origin : CPS1AddressedHydrolysis.Origin) : Option germ.Id := by
  classical
  exact match originKey? germ origin with
    | none => none
    | some key => if held : key ∈ germ.birth.nuclearKeys then some ⟨key,held⟩ else none

def originRow? (germ : Germ root state) (time : ℝ)
    (origin : CPS1AddressedHydrolysis.Origin) : Option CPS1AtomicDynamics.Body.Row :=
  (originId? germ origin).map (liveRow germ time)

def movedRow (germ : Germ root state) (time : ℝ)
    (item : CPS1AddressedReactiveJoint.Address × CPS1AtomicDynamics.Body.Row) :
    CPS1AddressedReactiveJoint.Address × CPS1AtomicDynamics.Body.Row :=
  match item.1 with
  | .nucleus origin =>
    match originId? germ origin with
    | none => item
    | some id => (item.1,{item.2 with
        position := (liveRow germ time id).position,momentum := (liveRow germ time id).momentum})
  | .electron .. => item

theorem moved_row_inertia (germ : Germ root state) (time : ℝ)
    (item : CPS1AddressedReactiveJoint.Address × CPS1AtomicDynamics.Body.Row) :
    (movedRow germ time item).2.inertia = item.2.inertia := by
  cases item with
  | mk address row =>
    cases address with
    | electron => rfl
    | nucleus origin => dsimp only [movedRow]; cases originId? germ origin <;> rfl

theorem moved_row_position_continuous (germ : Germ root state)
    (item : CPS1AddressedReactiveJoint.Address × CPS1AtomicDynamics.Body.Row) :
    ContinuousAt (fun time : ℝ => (movedRow germ time item).2.position) 0 := by
  cases item with
  | mk address row =>
    cases address with
    | electron => exact continuousAt_const
    | nucleus origin =>
      cases selected : originId? germ origin with
      | none =>
        simpa only [movedRow,selected] using
          (continuousAt_const : ContinuousAt (fun _ : ℝ => row.position) 0)
      | some id =>
        simpa only [movedRow,selected] using live_row_position_continuous germ id

theorem moved_row_zero (germ : Germ root state) (origin : CPS1AddressedHydrolysis.Origin)
    (row : CPS1AtomicDynamics.Body.Row) (aligned : originRow? germ 0 origin = some row) :
    movedRow germ 0 (.nucleus origin,row) = (.nucleus origin,row) := by
  unfold originRow? at aligned
  cases selected : originId? germ origin with
  | none => simp only [selected,Option.map_none] at aligned; cases aligned
  | some id =>
    simp only [selected,Option.map_some,Option.some.injEq] at aligned
    dsimp only [movedRow]
    rw [selected]
    dsimp only
    rw [aligned]

theorem moved_row_full (germ : Germ root state) (time : ℝ)
    (origin : CPS1AddressedHydrolysis.Origin) (row : CPS1AtomicDynamics.Body.Row)
    (id : germ.Id) (selected : originId? germ origin = some id)
    (aligned : liveRow germ 0 id = row) :
    (movedRow germ time (.nucleus origin,row)).2 = liveRow germ time id := by
  have inertia : (liveRow germ time id).inertia = row.inertia := by
    rw [live_row_inertia,← live_row_zero germ id,aligned]
  dsimp only [movedRow]
  rw [selected]
  dsimp only
  cases current : liveRow germ time id
  cases row
  simp only [current] at inertia
  cases inertia
  rfl

def originRows (germ : Germ root state) (time : ℝ)
    (rows : CPS1AddressedReactiveJoint.Rows.Stock) : CPS1AddressedReactiveJoint.Rows.Stock :=
  rows.map (movedRow germ time)

theorem moved_row_address (germ : Germ root state) (time : ℝ)
    (item : CPS1AddressedReactiveJoint.Address × CPS1AtomicDynamics.Body.Row) :
    (movedRow germ time item).1 = item.1 := by
  cases item with
  | mk address row =>
    cases address with
    | electron => rfl
    | nucleus origin => dsimp only [movedRow]; cases originId? germ origin <;> rfl

theorem origin_rows_inventory (germ : Germ root state) (time : ℝ)
    (rows : CPS1AddressedReactiveJoint.Rows.Stock) :
    (originRows germ time rows).length = rows.length ∧
    (originRows germ time rows).map Prod.fst = rows.map Prod.fst := by
  constructor
  · exact List.length_map _
  · simp only [originRows,List.map_map,Function.comp_def,moved_row_address]

theorem origin_rows_electron (germ : Germ root state) (time : ℝ)
    (origin : CPS1AddressedHydrolysis.Origin) (orbital : Nat)
    (row : CPS1AtomicDynamics.Body.Row) :
    movedRow germ time (.electron origin orbital,row) = (.electron origin orbital,row) := rfl

theorem origin_row_read_map (germ : Germ root state) (time : ℝ)
    (rows : CPS1AddressedReactiveJoint.Rows.Stock) (address : CPS1AddressedReactiveJoint.Address) :
    CPS1AddressedReactiveJoint.Rows.row? (originRows germ time rows) address =
      (CPS1AddressedReactiveJoint.Rows.row? rows address).map
        (fun row => (movedRow germ time (address,row)).2) := by
  classical
  induction rows with
  | nil => rfl
  | cons entry rest ih =>
    by_cases same : entry.1 = address
    · obtain ⟨key,row⟩ := entry
      dsimp only at same
      subst address
      simp [originRows,CPS1AddressedReactiveJoint.Rows.row?,moved_row_address]
    · simpa [originRows,CPS1AddressedReactiveJoint.Rows.row?,moved_row_address,same] using ih

theorem find_readout_particle
    (particles : List CPS1AddressedReactiveJoint.Particle)
    (unique : (particles.map (fun particle => particle.readout.address)).Nodup)
    (particle : CPS1AddressedReactiveJoint.Particle) (member : particle ∈ particles) :
    particles.find? (fun candidate => candidate.readout.address = particle.readout.address) = some particle := by
  classical
  induction particles with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons first rest ih =>
    have distinct := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | later
    · subst particle
      simp only [List.find?_cons,decide_true]
    · have different : first.readout.address ≠ particle.readout.address := by
        intro same
        apply distinct.1
        change first.readout.address ∈ _
        rw [same]
        exact List.mem_map.mpr ⟨particle,later,rfl⟩
      simpa only [List.find?_cons,decide_eq_false_iff_not.mpr different] using ih distinct.2 later

/-- The native-address lookup is a restriction of this same admitted body
inventory. It never resolves an old birth slot in a different occurrence. -/
def nativeMovedRow (germ : Germ root state) (particles : List CPS1AddressedReactiveJoint.Particle)
    (time : ℝ) (entry : CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row) :
    CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row :=
  match particles.find? (fun particle => particle.readout.address = entry.1) with
  | none => entry
  | some particle => (entry.1,(movedRow germ time (particle.address,entry.2)).2)

def liveNode (germ : Germ root state) (particles : List CPS1AddressedReactiveJoint.Particle)
    (time : ℝ) (node : CPS1AtomicDynamics.Body.Node) : CPS1AtomicDynamics.Body.Node :=
  ⟨node.particle,(nativeMovedRow germ particles time (node.particle.address,node.row)).2⟩

theorem native_moved_row_address (germ : Germ root state)
    (particles : List CPS1AddressedReactiveJoint.Particle) (time : ℝ)
    (entry : CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row) :
    (nativeMovedRow germ particles time entry).1 = entry.1 := by
  unfold nativeMovedRow
  cases particles.find? (fun particle => particle.readout.address = entry.1) <;> rfl

theorem native_moved_row_inertia (germ : Germ root state)
    (particles : List CPS1AddressedReactiveJoint.Particle) (time : ℝ)
    (entry : CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row) :
    (nativeMovedRow germ particles time entry).2.inertia = entry.2.inertia := by
  unfold nativeMovedRow
  cases particles.find? (fun particle => particle.readout.address = entry.1) with
  | none => rfl
  | some particle => exact moved_row_inertia germ time _

theorem live_node_position_continuous (germ : Germ root state)
    (particles : List CPS1AddressedReactiveJoint.Particle) (node : CPS1AtomicDynamics.Body.Node) :
    ContinuousAt (fun time : ℝ => (liveNode germ particles time node).row.position) 0 := by
  unfold liveNode nativeMovedRow
  cases particles.find? (fun particle => particle.readout.address = node.particle.address) with
  | none => exact continuousAt_const
  | some particle => exact moved_row_position_continuous germ _

theorem readout_rows_motion (germ : Germ root state)
    (particles : List CPS1AddressedReactiveJoint.Particle)
    (unique : (particles.map (fun particle => particle.readout.address)).Nodup)
    (rows : CPS1AddressedReactiveJoint.Rows.Stock) (time : ℝ) :
    CPS1AddressedReactiveJoint.Rows.readoutRows particles (originRows germ time rows) =
      (CPS1AddressedReactiveJoint.Rows.readoutRows particles rows).map (nativeMovedRow germ particles time) := by
  have all : ∀ processed : List CPS1AddressedReactiveJoint.Particle,
      (∀ particle ∈ processed, particle ∈ particles) →
      CPS1AddressedReactiveJoint.Rows.readoutRows processed (originRows germ time rows) =
        (CPS1AddressedReactiveJoint.Rows.readoutRows processed rows).map (nativeMovedRow germ particles time) := by
    intro processed
    induction processed with
    | nil => intro _; rfl
    | cons particle rest ih =>
      intro inside
      have tail := ih (fun source member => inside source (List.mem_cons_of_mem _ member))
      have selected := find_readout_particle particles unique particle (inside particle List.mem_cons_self)
      cases known : CPS1AddressedReactiveJoint.Rows.row? rows particle.address with
      | none =>
        simpa only [CPS1AddressedReactiveJoint.Rows.readoutRows,List.filterMap_cons,
          origin_row_read_map,known,Option.map_none] using tail
      | some row =>
        simpa only [CPS1AddressedReactiveJoint.Rows.readoutRows,List.filterMap_cons,
          origin_row_read_map,known,Option.map_some,List.map_cons,nativeMovedRow,selected] using
          congrArg (List.cons (particle.readout.address,(movedRow germ time (particle.address,row)).2)) tail
  exact all particles (fun _ held => held)

private theorem native_row_read_map (germ : Germ root state)
    (particles : List CPS1AddressedReactiveJoint.Particle) (time : ℝ)
    (rows : List (CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row))
    (address : CPS1AtomicDynamics.Charged.Address) :
    CPS1AtomicDynamics.Body.row? (rows.map (nativeMovedRow germ particles time)) address =
      (CPS1AtomicDynamics.Body.row? rows address).map
        (fun row => (nativeMovedRow germ particles time (address,row)).2) := by
  classical
  induction rows with
  | nil => rfl
  | cons entry rest ih =>
    by_cases same : entry.1 = address
    · obtain ⟨key,row⟩ := entry
      dsimp only at same
      subst address
      simp [CPS1AtomicDynamics.Body.row?,native_moved_row_address]
    · simpa [CPS1AtomicDynamics.Body.row?,native_moved_row_address,same] using ih

theorem native_gather_motion (germ : Germ root state)
    (sourceParticles : List CPS1AddressedReactiveJoint.Particle) (time : ℝ)
    (rows : List (CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row))
    (particles : List CPS1AtomicDynamics.Charged.Particle) (nodes : List CPS1AtomicDynamics.Body.Node)
    (actual : CPS1AtomicDynamics.Body.gather particles rows = .ok nodes) :
    CPS1AtomicDynamics.Body.gather particles (rows.map (nativeMovedRow germ sourceParticles time)) =
      .ok (nodes.map (liveNode germ sourceParticles time)) := by
  classical
  induction particles generalizing nodes with
  | nil =>
    have empty : nodes = [] := (Except.ok.inj actual).symm
    subst nodes
    rfl
  | cons particle rest ih =>
    cases known : CPS1AtomicDynamics.Body.row? rows particle.address with
    | none => simp [CPS1AtomicDynamics.Body.gather_cons,known] at actual
    | some row =>
      by_cases invalid : row.inertia ≤ 0
      · simp [CPS1AtomicDynamics.Body.gather_cons,known,invalid] at actual
      · cases remainder : CPS1AtomicDynamics.Body.gather rest rows with
        | error failure => simp [CPS1AtomicDynamics.Body.gather_cons,known,invalid,remainder] at actual
        | ok tail =>
          have same : nodes = (⟨particle,row⟩ : CPS1AtomicDynamics.Body.Node) :: tail := by
            simpa only [CPS1AtomicDynamics.Body.gather_cons,known,if_neg invalid,remainder,Except.ok.injEq]
              using actual.symm
          rw [same]
          have transported := ih tail remainder
          have read := native_row_read_map germ sourceParticles time rows particle.address
          rw [known] at read
          simp only [Option.map_some] at read
          simp only [CPS1AtomicDynamics.Body.gather_cons,read,native_moved_row_inertia,
            if_neg invalid,transported,List.map_cons,liveNode]

/-- A pulse writes current physical values. It does not call `Rows.report?` and
does not edit the raw report history, chemical history, or original root. -/
def movedSource (source : Occurrence frame) (germ : Germ source.old state) (time : ℝ) :
    Occurrence frame :=
  {source with ingress :=
    {source.ingress with measurements :=
      {source.ingress.measurements with rows := originRows germ time source.ingress.measurements.rows}}}

def movedBody (source : Occurrence frame) (germ : Germ source.old state) (time : ℝ) :
    Except CPS1AddressedReactiveJoint.Rows.Failure (CPS1AddressedReactiveJoint.Body frame) :=
  CPS1AddressedReactiveJoint.admission (movedSource source germ time).ingress

theorem moved_source_whole (source : Occurrence frame) (germ : Germ source.old state) (time : ℝ) :
    (movedSource source germ time).old = source.old ∧
    (movedSource source germ time).ingress.atomic = source.ingress.atomic ∧
    (movedSource source germ time).ingress.measurements.reserve = source.ingress.measurements.reserve ∧
    (movedSource source germ time).ingress.pending = source.ingress.pending ∧
    (movedSource source germ time).ingress.stages = source.ingress.stages ∧
    (movedSource source germ time).ingress.measurements.rows =
      originRows germ time source.ingress.measurements.rows ∧
    (movedSource source germ time).ingress.atomic.source.stock = source.ingress.atomic.source.stock ∧
    (movedSource source germ time).ingress.atomic.history = source.ingress.atomic.history :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem moved_body_actual (source : Occurrence frame) (germ : Germ source.old state)
    (time : ℝ) (body : CPS1AddressedReactiveJoint.Body frame)
    (actual : movedBody source germ time = .ok body) :
    CPS1AddressedReactiveJoint.BodyProperties (movedSource source germ time).ingress.atomic
      (movedSource source germ time).ingress.measurements body :=
  CPS1AddressedReactiveJoint.admitted_body _ _ _ actual

end
end CPS1ReactiveJointNuclear
