import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveJointNuclear.Occupation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Find

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/- Cache construction draft. The public data producer below takes raw source
inputs and finite depth. The proof obligations at the end are results to prove,
never producer arguments. This draft starts no Lean command or assumed declaration. -/
namespace CPS1ReactiveJointNuclear
noncomputable section
open CPS1ElectronicSource CPS1ReactiveNuclear
open CPS1ReactiveField CPS1ReactiveField.Carried
open scoped BigOperators InnerProductSpace Matrix Topology
variable {frame : CPS1Recycling.Frame}
variable {root : CPS1Deformation.Source.Occurrence frame} {state : Snapshot}

@[reducible] def motionBirth (germ : Germ root state) (time : ℝ) : Birth root (paidResponse germ time) := by
  have count : (paidResponse germ time).nuclei.length = state.nuclei.length := by
    rw [(paid_response_account germ time).2.2.2.2.2]
    exact List.length_ofFn
  exact ⟨germ.birth.owner,germ.birth.ownerHeld,germ.birth.nuclearKeys,
    germ.birth.nuclearLength.trans count.symm,germ.birth.primitiveKey⟩

@[reducible] def motionGerm (germ : Germ root state) (time : ℝ) :
    Except GermFailure (Germ root (paidResponse germ time)) := admitBirth (motionBirth germ time)

theorem motion_birth_node (germ : Germ root state) (time : ℝ) (id : germ.Id) :
    (motionBirth germ time).node germ.unique id =
      germ.nodeAt (movedPositions germ time) (movedMomenta germ time)
        ((germ.birth.slotEquiv germ.unique).symm id) := by
  change (paidResponse germ time).nuclei.get
    (((motionBirth germ time).slotEquiv germ.unique).symm id) = _
  change (List.ofFn (germ.nodeAt (movedPositions germ time) (movedMomenta germ time))).get
    (((motionBirth germ time).slotEquiv germ.unique).symm id) = _
  erw [List.get_ofFn]
  congr 1

@[reducible] def materializedGerm (germ : Germ root state) (time : ℝ)
    (ready : CPS1AtomicDynamics.Body.ready (paidResponse germ time).nuclei) :
    Germ root (paidResponse germ time) := by
  refine ⟨motionBirth germ time,germ.unique,germ.covered,?_,?_,ready⟩
  · intro primitive
    rw [motion_birth_node]
    change movedPositions germ time (germ.primitiveId primitive) =
      Geometry.nucleusPosition (germ.nodeAt (movedPositions germ time) (movedMomenta germ time)
        ((germ.birth.slotEquiv germ.unique).symm (germ.primitiveId primitive)))
    simp only [Germ.nodeAt,Germ.nuclearId,Birth.nuclearId,Equiv.apply_symm_apply]
    funext axis
    rfl
  · intro id
    rw [motion_birth_node]
    exact germ.positive id

theorem motion_germ_generated (germ : Germ root state) (time : ℝ)
    (ready : CPS1AtomicDynamics.Body.ready (paidResponse germ time).nuclei) :
    motionGerm germ time = .ok (materializedGerm germ time ready) := by
  let generated := materializedGerm germ time ready
  change admitBirth generated.birth = .ok generated
  simp only [admitBirth,dif_pos generated.unique,dif_pos generated.covered,
    dif_pos generated.centre,dif_pos generated.positive,dif_pos generated.ready]

theorem origin_row_after_motion (germ : Germ root state) (time : ℝ)
    (after : Germ root (paidResponse germ time)) (actual : motionGerm germ time = .ok after)
    (origin : CPS1AddressedHydrolysis.Origin) :
    originRow? after 0 origin = originRow? germ time origin := by
  have generated := motion_germ_generated germ time after.ready
  have same : after = materializedGerm germ time after.ready := Except.ok.inj (actual.symm.trans generated)
  rw [same]
  have keys : originKey? (materializedGerm germ time after.ready) origin = originKey? germ origin := by
    cases origin <;> rfl
  unfold originRow? originId?
  rw [keys]
  cases selected : originKey? germ origin with
  | none => simp only [Option.map_none]
  | some key =>
    by_cases held : key ∈ germ.birth.nuclearKeys
    · simp only [dif_pos held,Option.map_some]
      rw [live_row_zero]
      exact congrArg (fun node : CPS1AtomicDynamics.Body.Node => some node.row)
        (motion_birth_node germ time ⟨key,held⟩)
    · simp only [dif_neg held,Option.map_none]

/-- The current dynamic nuclear rows must agree with the same key readout of
the current physical fields. Only particles in the actual admitted body enter
this check; unused reports remain present as typed residual input. -/
def BodyOriginAligned (body : CPS1AddressedReactiveJoint.Body frame) (germ : Germ root state) : Prop :=
  ∀ particle ∈ CPS1AddressedReactiveJoint.particles body.atoms,
    ∀ origin, particle.address = CPS1AddressedReactiveJoint.Address.nucleus origin →
      originRow? germ 0 origin = CPS1AddressedReactiveJoint.Rows.row?
        body.sourceRows particle.address

abbrev OriginAligned (active : Active frame) (germ : Germ active.source.old active.fields) : Prop :=
  BodyOriginAligned active.body germ

private theorem gather_known_rows
    (nodes : List CPS1AtomicDynamics.Body.Node)
    (rows : List (CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row))
    (known : ∀ node ∈ nodes, 0 < node.row.inertia ∧
      CPS1AtomicDynamics.Body.row? rows node.particle.address = some node.row) :
    CPS1AtomicDynamics.Body.gather (nodes.map CPS1AtomicDynamics.Body.Node.particle) rows = .ok nodes := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    have current := known node List.mem_cons_self
    have tail := ih (fun following member => known following (List.mem_cons_of_mem _ member))
    simp only [List.map_cons,CPS1AtomicDynamics.Body.gather_cons,current.2,
      if_neg (not_le.mpr current.1),tail]

theorem active_native_gather (active : Active frame) :
    CPS1AtomicDynamics.Body.gather
      ((CPS1AddressedReactiveJoint.particles active.body.atoms).map CPS1AddressedReactiveJoint.Particle.readout)
      (CPS1AddressedReactiveJoint.Rows.readoutRows (CPS1AddressedReactiveJoint.particles active.body.atoms)
        active.body.sourceRows) = .ok active.body.nodes := by
  have facts := CPS1AddressedReactiveJoint.admitted_body _ _ _ active.actual
  rcases facts with ⟨_,_,_,_,_,_,_,mapped,_,source⟩
  have rows : ∀ node ∈ active.body.nodes, 0 < node.row.inertia ∧
      CPS1AtomicDynamics.Body.row?
        (CPS1AddressedReactiveJoint.Rows.readoutRows (CPS1AddressedReactiveJoint.particles active.body.atoms)
          active.body.sourceRows) node.particle.address = some node.row := by
    intro node member
    rcases source node member with ⟨positive,particle,present,identity,row⟩
    refine ⟨positive,?_⟩
    rw [identity,CPS1AddressedReactiveJoint.Rows.readout_row _ _
      (CPS1AddressedReactiveJoint.particle_readout_unique _) particle present]
    exact row
  simpa only [mapped] using gather_known_rows active.body.nodes _ rows

theorem active_particle_row (active : Active frame) (particle : CPS1AddressedReactiveJoint.Particle)
    (member : particle ∈ CPS1AddressedReactiveJoint.particles active.body.atoms) :
    ∃ row, CPS1AddressedReactiveJoint.Rows.row? active.body.sourceRows particle.address = some row := by
  have generated := CPS1AtomicDynamics.Body.gather_source _ _ _ (active_native_gather active)
  have present : particle.readout ∈ active.body.nodes.map CPS1AtomicDynamics.Body.Node.particle :=
    generated.1 ▸ List.mem_map.mpr ⟨particle,member,rfl⟩
  obtain ⟨node,held,identity⟩ := List.mem_map.mp present
  have row := (generated.2 node held).2
  rw [identity,CPS1AddressedReactiveJoint.Rows.readout_row _ _
    (CPS1AddressedReactiveJoint.particle_readout_unique _) particle member] at row
  exact ⟨node.row,row⟩

@[reducible] def bodyCandidate (active : Active frame) (germ : Germ active.source.old active.fields) (time : ℝ) :
    CPS1AddressedReactiveJoint.Body frame :=
  {active.body with
    nodes := active.body.nodes.map (liveNode germ (CPS1AddressedReactiveJoint.particles active.body.atoms) time)
    sourceRows := originRows germ time active.body.sourceRows}

theorem body_candidate_gather (active : Active frame) (germ : Germ active.source.old active.fields)
    (time : ℝ) :
    CPS1AddressedReactiveJoint.Rows.gather active.body.atoms (bodyCandidate active germ time).sourceRows =
      .ok (bodyCandidate active germ time).nodes := by
  have facts := CPS1AddressedReactiveJoint.admitted_body _ _ _ active.actual
  rcases facts with ⟨_,_,_,_,_,_,unique,_,_,_⟩
  have transported := native_gather_motion germ (CPS1AddressedReactiveJoint.particles active.body.atoms) time
    (CPS1AddressedReactiveJoint.Rows.readoutRows (CPS1AddressedReactiveJoint.particles active.body.atoms)
      active.body.sourceRows)
    ((CPS1AddressedReactiveJoint.particles active.body.atoms).map CPS1AddressedReactiveJoint.Particle.readout)
    active.body.nodes (active_native_gather active)
  rw [← readout_rows_motion germ _ (CPS1AddressedReactiveJoint.particle_readout_unique _) active.body.sourceRows time]
    at transported
  unfold CPS1AddressedReactiveJoint.Rows.gather
  rw [if_pos unique]
  change (CPS1AtomicDynamics.Body.gather
      ((CPS1AddressedReactiveJoint.particles active.body.atoms).map CPS1AddressedReactiveJoint.Particle.readout)
      (CPS1AddressedReactiveJoint.Rows.readoutRows (CPS1AddressedReactiveJoint.particles active.body.atoms)
        (originRows germ time active.body.sourceRows))).mapError _ = _
  rw [transported]
  rfl

theorem moved_body_normal_form (active : Active frame) (germ : Germ active.source.old active.fields)
    (time : ℝ) :
    movedBody active.source germ time =
      @ite (Except CPS1AddressedReactiveJoint.Rows.Failure (CPS1AddressedReactiveJoint.Body frame))
        (CPS1AtomicDynamics.Body.ready (bodyCandidate active germ time).nodes) (Classical.propDecidable _)
        (.ok (bodyCandidate active germ time)) (.error (.body .collision)) := by
  classical
  have facts := CPS1AddressedReactiveJoint.admitted_body _ _ _ active.actual
  rcases facts with ⟨atomic,atoms,rows,reserve,nonnegative,missing,_,_,_,_⟩
  have gathered := body_candidate_gather active germ time
  simp only [movedBody,movedSource,CPS1AddressedReactiveJoint.admission,CPS1AddressedReactiveJoint.admit?]
  rw [← reserve,if_neg (not_lt.mpr nonnegative),← atoms,← rows,gathered]
  simp only [bodyCandidate,atomic,atoms,reserve,missing,ite_not]

theorem body_candidate_admission (active : Active frame) (germ : Germ active.source.old active.fields)
    (time : ℝ) (ready : CPS1AtomicDynamics.Body.ready (bodyCandidate active germ time).nodes) :
    movedBody active.source germ time = .ok (bodyCandidate active germ time) := by
  rw [moved_body_normal_form,if_pos ready]

theorem actual_moved_body (active : Active frame) (germ : Germ active.source.old active.fields)
    (time : ℝ) (body : CPS1AddressedReactiveJoint.Body frame)
    (actual : movedBody active.source germ time = .ok body) : body = bodyCandidate active germ time := by
  rw [moved_body_normal_form] at actual
  split at actual
  · exact (Except.ok.inj actual).symm
  · cases actual

theorem live_node_zero_of_origin_aligned (active : Active frame)
    (germ : Germ active.source.old active.fields) (aligned : OriginAligned active germ)
    (node : CPS1AtomicDynamics.Body.Node) (member : node ∈ active.body.nodes) :
    liveNode germ (CPS1AddressedReactiveJoint.particles active.body.atoms) 0 node = node := by
  have facts := CPS1AddressedReactiveJoint.admitted_body _ _ _ active.actual
  rcases facts with ⟨_,_,_,_,_,_,_,_,_,source⟩
  rcases source node member with ⟨_,particle,present,identity,row⟩
  have selected := find_readout_particle (CPS1AddressedReactiveJoint.particles active.body.atoms)
    (CPS1AddressedReactiveJoint.particle_readout_unique _) particle present
  have field : (movedRow germ 0 (particle.address,node.row)).2 = node.row := by
    cases address : particle.address with
    | electron => rfl
    | nucleus origin =>
      have same := (aligned particle present origin address).trans row
      exact congrArg Prod.snd (moved_row_zero germ origin node.row same)
  unfold liveNode nativeMovedRow
  rw [identity,selected,field]
  change (⟨particle.readout,node.row⟩ : CPS1AtomicDynamics.Body.Node) = node
  rw [← identity]

theorem full_body_ready_eventually (active : Active frame)
    (germ : Germ active.source.old active.fields) (aligned : OriginAligned active germ) :
    ∀ᶠ time in 𝓝 (0 : ℝ), CPS1AtomicDynamics.Body.ready (bodyCandidate active germ time).nodes := by
  have facts := CPS1AddressedReactiveJoint.admitted_body _ _ _ active.actual
  rcases facts with ⟨_,_,_,_,_,_,_,_,ready,_⟩
  have zero : (bodyCandidate active germ 0).nodes = active.body.nodes := by
    change active.body.nodes.map (liveNode germ (CPS1AddressedReactiveJoint.particles active.body.atoms) 0) = _
    have identity : active.body.nodes.map (liveNode germ (CPS1AddressedReactiveJoint.particles active.body.atoms) 0) =
        active.body.nodes.map (fun node => node) :=
      List.map_congr_left (fun node member => live_node_zero_of_origin_aligned active germ aligned node member)
    simpa only [List.map_id_fun',id_eq] using identity
  have initial : active.body.nodes.Pairwise (fun first second =>
      (liveNode germ (CPS1AddressedReactiveJoint.particles active.body.atoms) 0 first).row.position ≠
        (liveNode germ (CPS1AddressedReactiveJoint.particles active.body.atoms) 0 second).row.position) := by
    have begin : CPS1AtomicDynamics.Body.ready (bodyCandidate active germ 0).nodes := zero.symm ▸ ready
    simpa only [CPS1AtomicDynamics.Body.ready,bodyCandidate,List.pairwise_map] using begin
  have generated := CPS1PositivePulse.pairwise_positions_eventually active.body.nodes
    (fun time node => (liveNode germ (CPS1AddressedReactiveJoint.particles active.body.atoms) time node).row.position)
    (fun node _ => live_node_position_continuous germ _ node) initial
  simpa only [CPS1AtomicDynamics.Body.ready,bodyCandidate,List.pairwise_map] using generated

theorem origin_aligned_after_body (active : Active frame)
    (germ : Germ active.source.old active.fields) (aligned : OriginAligned active germ)
    (time : ℝ) (after : Germ active.source.old (paidResponse germ time))
    (actual : motionGerm germ time = .ok after) :
    BodyOriginAligned (bodyCandidate active germ time) after := by
  intro particle member origin address
  obtain ⟨row,known⟩ := active_particle_row active particle member
  have zero := (aligned particle member origin address).trans known
  have read := origin_row_read_map germ time active.body.sourceRows particle.address
  rw [known] at read
  unfold originRow? at zero
  cases selected : originId? germ origin with
  | none => simp only [selected,Option.map_none] at zero; cases zero
  | some id =>
    simp only [selected,Option.map_some,Option.some.injEq] at zero
    have updated := moved_row_full germ time origin row id selected zero
    rw [address] at read
    simp only [Option.map_some,updated] at read
    rw [origin_row_after_motion germ time after actual origin]
    change originRow? germ time origin =
      CPS1AddressedReactiveJoint.Rows.row? (originRows germ time active.body.sourceRows) particle.address
    rw [address]
    simpa only [originRow?,selected,Option.map_some] using read.symm


def AdmissibleDyadic (source : Occurrence frame) (germ : Germ source.old state) (index : Nat) : Prop :=
  let time := CPS1ReactiveFieldDynamics.dyadicTime index
  NonzeroPivots (preResponse germ time) ∧
  CPS1AtomicDynamics.Body.ready (paidResponse germ time).nuclei ∧
  (movedBody source germ time).toOption.isSome = true ∧
  (motionGerm germ time).toOption.isSome = true ∧
  energyDelta germ time < state.reserve

private theorem exists_joint_admissible (active : Active frame)
    (germ : Germ active.source.old active.fields) (aligned : OriginAligned active germ)
    (margin : 0 < active.fields.reserve) : ∃ index, AdmissibleDyadic active.source germ index := by
  have price : ∀ᶠ time in 𝓝 (0 : ℝ), energyDelta germ time < active.fields.reserve :=
    (energy_delta_continuous_zero germ active.good).eventually_lt continuousAt_const (by
      rw [energy_delta_zero germ active.good]
      exact margin)
  have neighbourhood : ∀ᶠ time in 𝓝 (0 : ℝ),
      NonzeroPivots (preResponse germ time) ∧
      CPS1AtomicDynamics.Body.ready (paidResponse germ time).nuclei ∧
      (movedBody active.source germ time).toOption.isSome = true ∧
      (motionGerm germ time).toOption.isSome = true ∧
      energyDelta germ time < active.fields.reserve := by
    filter_upwards [pivots_eventually_nonzero germ active.good,moving_nuclei_ready_eventually germ,
      full_body_ready_eventually active germ aligned,price] with time pivots nuclei bodyReady paid
    exact ⟨pivots,nuclei,by rw [body_candidate_admission active germ time bodyReady]; rfl,
      by rw [motion_germ_generated germ time nuclei]; rfl,paid⟩
  have powers : Filter.Tendsto CPS1ReactiveFieldDynamics.dyadicTime Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)
  exact (powers.eventually neighbourhood).exists


/-- The existence check searches this current's recomputed candidate only. The
closure obligation proves its positive branch from current source facts. It
contains no table of future Ready states, supplied time, or endpoint witness. -/
def affordableIndex? (source : Occurrence frame) (germ : Germ source.old state) : Option Nat := by
  classical
  exact if generated : ∃ index, AdmissibleDyadic source germ index then
    some (Nat.find generated) else none

theorem affordable_index_generated (source : Occurrence frame) (germ : Germ source.old state)
    (index : Nat) (actual : affordableIndex? source germ = some index) :
    AdmissibleDyadic source germ index ∧
      ∀ earlier, earlier < index → ¬ AdmissibleDyadic source germ earlier := by
  classical
  unfold affordableIndex? at actual
  split at actual
  · rename_i generated
    cases Option.some.inj actual
    exact ⟨Nat.find_spec generated,fun earlier smaller => Nat.find_min generated smaller⟩
  · cases actual

theorem paid_response_good (germ : Germ root state) (time : ℝ)
    (pivots : NonzeroPivots (preResponse germ time)) : (paidResponse germ time).Good := by
  change (response germ time).Good
  exact response_good germ time pivots

inductive Failure
  | missingActive
  | staleActive
  | exhaustedReserve
  | germ (failure : GermFailure)
  | unalignedOriginRows
  | noAdmissibleDyadic
  | liveBody (failure : CPS1AddressedReactiveJoint.Rows.Failure)
  deriving DecidableEq

@[reducible] def boundGerm (current : SourceCursor frame) (active : Active frame)
    (held : current.native.active = some active) :
    Except GermFailure (Germ active.source.old active.fields) := by
  simpa only [GermAt,held] using current.germ

def Ready (current : SourceCursor frame) : Prop :=
  ∃ active : Active frame, ∃ held : current.native.active = some active,
    active.source = current.native.current ∧ 0 < active.fields.reserve ∧
      ∃ germ : Germ active.source.old active.fields,
        boundGerm current active held = .ok germ ∧ OriginAligned active germ

structure Pulse (frame : CPS1Recycling.Frame) where
  before : SourceCursor frame
  after : SourceCursor frame
  index : Nat
  time : ℝ

/-- The actual joint write constructs both native state and its germ. The live
source is updated here; it is not identified with the old occurrence by a false
SourceImmutable equality. Raw/chemical stages are unchanged and remain valid. -/
def step (current : SourceCursor frame) : Except Failure (SourceCursor frame × Pulse frame) := by
  classical
  exact match held : current.native.active with
    | none => .error .missingActive
    | some active =>
      if active.source ≠ current.native.current then .error .staleActive
      else if ¬ 0 < active.fields.reserve then .error .exhaustedReserve
      else match binding : boundGerm current active held with
        | .error failure => .error (.germ failure)
        | .ok germ =>
          if ¬ OriginAligned active germ then .error .unalignedOriginRows
          else match selected : affordableIndex? active.source germ with
            | none => .error .noAdmissibleDyadic
            | some index =>
              let time := CPS1ReactiveFieldDynamics.dyadicTime index
              let paid := affordable_index_generated active.source germ index selected
              match bodyActual : movedBody active.source germ time with
              | .error failure => .error (.liveBody failure)
              | .ok body =>
                match afterBinding : motionGerm germ time with
                | .error failure => .error (.germ failure)
                | .ok afterGerm =>
                  let fields := paidResponse germ time
                  let nextActive : Active frame :=
                    ⟨movedSource active.source germ time,fields,
                      paid_response_good germ time paid.1.1,body,bodyActual,active.paidRawReserve⟩
                  let native : Cursor frame :=
                    {current.native with current := nextActive.source,active := some nextActive}
                  let next : SourceCursor frame := ⟨native,.ok afterGerm⟩
                  .ok (next,⟨current,next,index,time⟩)

def Pulse.Valid (pulse : Pulse frame) : Prop :=
  ∃ active : Active frame, ∃ held : pulse.before.native.active = some active,
    ∃ germ : Germ active.source.old active.fields,
      boundGerm pulse.before active held = .ok germ ∧
      active.source = pulse.before.native.current ∧ OriginAligned active germ ∧
      pulse.time = CPS1ReactiveFieldDynamics.dyadicTime pulse.index ∧
      AdmissibleDyadic active.source germ pulse.index ∧
      (∀ earlier, earlier < pulse.index → ¬ AdmissibleDyadic active.source germ earlier) ∧
      ∃ body : CPS1AddressedReactiveJoint.Body frame,
        movedBody active.source germ pulse.time = .ok body ∧
      ∃ afterGerm : Germ active.source.old (paidResponse germ pulse.time),
        motionGerm germ pulse.time = .ok afterGerm ∧
      ∃ afterActive : Active frame, ∃ _afterHeld : pulse.after.native.active = some afterActive,
        afterActive.source = movedSource active.source germ pulse.time ∧
        afterActive.fields = paidResponse germ pulse.time ∧
        afterActive.body = body ∧ afterActive.paidRawReserve = active.paidRawReserve ∧
        pulse.after.native.current = afterActive.source ∧
        pulse.after.native.stages = pulse.before.native.stages ∧
        afterGerm.birth.nuclearKeys = germ.birth.nuclearKeys ∧
        afterGerm.birth.owner = germ.birth.owner ∧
        afterActive.fields.Ne = active.fields.Ne ∧
        afterActive.fields.account = active.fields.account ∧
        afterActive.fields.Good ∧ 0 < afterActive.fields.reserve ∧ Ready pulse.after

theorem step_generated (current next : SourceCursor frame) (pulse : Pulse frame)
    (actual : step current = .ok (next,pulse)) :
    pulse.Valid ∧ Ready next ∧ pulse.before = current ∧ pulse.after = next := by
  classical
  unfold step at actual
  split at actual
  · cases actual
  · rename_i active held
    split at actual
    · cases actual
    · rename_i sourceSame
      split at actual
      · cases actual
      · rename_i marginTag
        split at actual
        · cases actual
        · rename_i germ binding
          split at actual
          · cases actual
          · rename_i alignmentTag
            split at actual
            · cases actual
            · rename_i index selected
              let time := CPS1ReactiveFieldDynamics.dyadicTime index
              let paid := affordable_index_generated active.source germ index selected
              dsimp only at actual
              split at actual
              · cases actual
              · rename_i body bodyActual
                split at actual
                · cases actual
                · rename_i afterGerm afterBinding
                  let nextActive : Active frame :=
                    ⟨movedSource active.source germ time,paidResponse germ time,
                      paid_response_good germ time paid.1.1,body,bodyActual,active.paidRawReserve⟩
                  let native : Cursor frame :=
                    {current.native with current := nextActive.source,active := some nextActive}
                  let generated : SourceCursor frame := ⟨native,.ok afterGerm⟩
                  have sameSource : active.source = current.native.current := not_ne_iff.mp sourceSame
                  have aligned : OriginAligned active germ := not_not.mp alignmentTag
                  have bodySame : body = bodyCandidate active germ time :=
                    actual_moved_body active germ time body bodyActual
                  have afterAligned : OriginAligned nextActive afterGerm := by
                    change BodyOriginAligned body afterGerm
                    rw [bodySame]
                    exact origin_aligned_after_body active germ aligned time afterGerm afterBinding
                  have positive : 0 < nextActive.fields.reserve := sub_pos.mpr paid.1.2.2.2.2
                  have afterReady : Ready generated :=
                    ⟨nextActive,rfl,rfl,positive,afterGerm,rfl,afterAligned⟩
                  have birth := admit_birth_generated (motionBirth germ time) afterGerm afterBinding
                  cases Except.ok.inj actual
                  refine ⟨?_,afterReady,rfl,rfl⟩
                  refine ⟨active,held,germ,binding,sameSource,aligned,rfl,paid.1,paid.2,
                    body,bodyActual,afterGerm,afterBinding,nextActive,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
                    ?_,?_,rfl,(paid_response_account germ time).2.2.1,
                    paid_response_good germ time paid.1.1,positive,afterReady⟩
                  · exact congrArg Birth.nuclearKeys birth
                  · exact congrArg Birth.owner birth

/-- Source birth and the actual admitted body are read inside `step`. A
successful raw invocation produces current alignment and margin here; callers
never supply an OriginAligned or future-Ready certificate. -/
theorem step_current_ready (current next : SourceCursor frame) (pulse : Pulse frame)
    (actual : step current = .ok (next,pulse)) : Ready current := by
  classical
  unfold step at actual
  split at actual
  · cases actual
  · rename_i active held
    split at actual
    · cases actual
    · rename_i sourceSame
      split at actual
      · cases actual
      · rename_i marginTag
        split at actual
        · cases actual
        · rename_i germ binding
          split at actual
          · cases actual
          · rename_i alignmentTag
            exact ⟨active,held,not_ne_iff.mp sourceSame,not_not.mp marginTag,germ,binding,not_not.mp alignmentTag⟩

theorem step_ready (current : SourceCursor frame) (ready : Ready current) :
    ∃ next pulse, step current = .ok (next,pulse) ∧ pulse.Valid ∧ Ready next := by
  classical
  rcases ready with ⟨active,held,same,margin,germ,binding,aligned⟩
  have existsIndex := exists_joint_admissible active germ aligned margin
  let index := Nat.find existsIndex
  have indexSpec : AdmissibleDyadic active.source germ index := Nat.find_spec existsIndex
  have selected : affordableIndex? active.source germ = some index := by
    simp only [affordableIndex?,dif_pos existsIndex,index]
  let time := CPS1ReactiveFieldDynamics.dyadicTime index
  let body := bodyCandidate active germ time
  have bodyActual : movedBody active.source germ time = .ok body := by
    have checked := indexSpec.2.2.1
    rw [moved_body_normal_form] at checked
    split at checked
    · exact body_candidate_admission active germ time (by assumption)
    · simp only [Except.toOption,Option.isSome] at checked
      cases checked
  have bodyAdmission : CPS1AddressedReactiveJoint.admission
      (movedSource active.source germ time).ingress = .ok body := by
    simpa only [movedBody] using bodyActual
  let afterGerm := materializedGerm germ time indexSpec.2.1
  have afterBinding : motionGerm germ time = .ok afterGerm := motion_germ_generated _ _ _
  let nextActive : Active frame :=
    ⟨movedSource active.source germ time,paidResponse germ time,
      paid_response_good germ time indexSpec.1,body,bodyAdmission,active.paidRawReserve⟩
  let native : Cursor frame :=
    {current.native with current := nextActive.source,active := some nextActive}
  let next : SourceCursor frame := ⟨native,.ok afterGerm⟩
  let pulse : Pulse frame := ⟨current,next,index,time⟩
  have actual : step current = .ok (next,pulse) := by
    dsimp only [step]
    split
    · rename_i absent
      rw [held] at absent
      cases absent
    · rename_i actualActive actualHeld
      have activeSame : actualActive = active := Option.some.inj (actualHeld.symm.trans held)
      subst actualActive
      have bindingHere : boundGerm current active actualHeld = .ok germ := binding
      simp only [if_neg (not_ne_iff.mpr same),if_neg (not_not.mpr margin)]
      split
      · rename_i failed failedBinding
        have rejected := failedBinding.symm.trans bindingHere
        cases rejected
      · rename_i candidate candidateBinding
        have germSame : candidate = germ := Except.ok.inj (candidateBinding.symm.trans bindingHere)
        subst candidate
        simp only [if_neg (not_not.mpr aligned)]
        split
        · rename_i missing
          have rejected := missing.symm.trans selected
          cases rejected
        · rename_i actualIndex actualSelected
          have indexSame : actualIndex = index := Option.some.inj (actualSelected.symm.trans selected)
          subst actualIndex
          split
          · rename_i failure failedBody
            have rejected := failedBody.symm.trans bodyActual
            cases rejected
          · rename_i actualBody actualBodyHeld
            have bodySame : actualBody = body := Except.ok.inj (actualBodyHeld.symm.trans bodyActual)
            subst actualBody
            split
            · rename_i failure failedGerm
              have rejected := failedGerm.symm.trans afterBinding
              cases rejected
            · rename_i actualGerm actualGermHeld
              have germSame : actualGerm = afterGerm := Except.ok.inj (actualGermHeld.symm.trans afterBinding)
              subst actualGerm
              rfl
  have generated := step_generated current next pulse actual
  exact ⟨next,pulse,actual,generated.1,generated.2.1⟩

theorem step_source_whole (current next : SourceCursor frame) (pulse : Pulse frame)
    (actual : step current = .ok (next,pulse)) :
    next.native.current.old = current.native.current.old ∧
    next.native.current.ingress.atomic = current.native.current.ingress.atomic ∧
    next.native.current.ingress.pending = current.native.current.ingress.pending ∧
    next.native.current.ingress.stages = current.native.current.ingress.stages ∧
    next.native.stages = current.native.stages := by
  have valid := (step_generated current next pulse actual).1
  have before := (step_generated current next pulse actual).2.2.1
  have after := (step_generated current next pulse actual).2.2.2
  rcases valid with ⟨active,held,germ,_,same,_,_,_,_,body,_,afterGerm,_,afterActive,afterHeld,
    source,fields,bodyIdentity,rawReserve,currentSource,stages,rest⟩
  rw [before] at same stages
  rw [after] at currentSource stages
  rw [currentSource,source,← same]
  exact ⟨rfl,rfl,rfl,rfl,stages⟩

structure Run (frame : CPS1Recycling.Frame) where
  cursor : SourceCursor frame
  pulses : List (Pulse frame)
  remaining : Nat
  failure : Option Failure

@[reducible] def renew (current : SourceCursor frame) (depth : Nat) : Run frame :=
  Nat.rec (motive := fun _ => SourceCursor frame → Run frame)
    (fun current => ⟨current,[],0,none⟩)
    (fun depth recur current => match step current with
      | .error failure => ⟨current,[],depth+1,some failure⟩
      | .ok (next,pulse) => let rest := recur next; {rest with pulses := pulse :: rest.pulses}) depth current

theorem renew_succ (current : SourceCursor frame) (depth : Nat) :
    renew current (depth+1) = match step current with
      | .error failure => ⟨current,[],depth+1,some failure⟩
      | .ok (next,pulse) => let rest := renew next depth; {rest with pulses := pulse :: rest.pulses} := rfl

inductive Trace : SourceCursor frame → List (Pulse frame) → SourceCursor frame → Prop
  | nil (current) : Trace current [] current
  | cons (current next final : SourceCursor frame) (pulse : Pulse frame) (rest : List (Pulse frame))
      (actual : step current = .ok (next,pulse)) (tail : Trace next rest final) :
      Trace current (pulse :: rest) final

theorem renew_trace (current : SourceCursor frame) (depth : Nat) :
    Trace current (renew current depth).pulses (renew current depth).cursor := by
  induction depth generalizing current with
  | zero => exact .nil current
  | succ depth ih =>
    rw [renew_succ]
    cases actual : step current with
    | error => exact .nil current
    | ok result => exact .cons current result.1 _ result.2 _ actual (ih result.1)

theorem trace_whole (current final : SourceCursor frame) (pulses : List (Pulse frame))
    (trace : Trace current pulses final) :
    final.native.current.old = current.native.current.old ∧
    final.native.current.ingress.atomic = current.native.current.ingress.atomic ∧
    final.native.current.ingress.pending = current.native.current.ingress.pending ∧
    final.native.current.ingress.stages = current.native.current.ingress.stages ∧
    final.native.stages = current.native.stages ∧
    ∀ pulse ∈ pulses, pulse.Valid := by
  induction trace with
  | nil current => exact ⟨rfl,rfl,rfl,rfl,rfl,by intro pulse member; cases member⟩
  | cons current next final pulse rest actual _ ih =>
    have generated := step_source_whole current next pulse actual
    refine ⟨ih.1.trans generated.1,ih.2.1.trans generated.2.1,
      ih.2.2.1.trans generated.2.2.1,ih.2.2.2.1.trans generated.2.2.2.1,
      ih.2.2.2.2.1.trans generated.2.2.2.2,?_⟩
    intro entry member
    rcases List.mem_cons.mp member with same | later
    · exact same ▸ (step_generated current next pulse actual).1
    · exact ih.2.2.2.2.2 entry later

theorem renew_whole (current : SourceCursor frame) (depth : Nat) :
    (renew current depth).cursor.native.current.old = current.native.current.old ∧
    (renew current depth).cursor.native.current.ingress.atomic = current.native.current.ingress.atomic ∧
    (renew current depth).cursor.native.current.ingress.pending = current.native.current.ingress.pending ∧
    (renew current depth).cursor.native.current.ingress.stages = current.native.current.ingress.stages ∧
    (renew current depth).cursor.native.stages = current.native.stages ∧
    ∀ pulse ∈ (renew current depth).pulses, pulse.Valid :=
  trace_whole _ _ _ (renew_trace current depth)

theorem renew_ready (current : SourceCursor frame) (depth : Nat) (ready : Ready current) :
    (renew current depth).remaining = 0 ∧ (renew current depth).failure = none ∧
    (renew current depth).pulses.length = depth ∧ Ready (renew current depth).cursor := by
  induction depth generalizing current with
  | zero => exact ⟨rfl,rfl,rfl,ready⟩
  | succ depth ih =>
    obtain ⟨next,pulse,actual,valid,afterReady⟩ := step_ready current ready
    have tail := ih next afterReady
    rw [renew_succ,actual]
    exact ⟨tail.1,tail.2.1,by simp only [List.length_cons,tail.2.2.1],tail.2.2.2⟩

def continueChemical (current : SourceCursor frame) (depth : Nat) (inputs : List Input) : Run frame :=
  let physical := renew current depth
  {physical with cursor := SourceCursor.advanceAll physical.cursor inputs}

theorem continue_chemical_actual (current : SourceCursor frame) (depth : Nat) (inputs : List Input) :
    (continueChemical current depth inputs).cursor.native.current.ingress.atomic =
      CPS1AddressedHydrolysis.Atomic.advanceAll current.native.current.ingress.atomic (inputs.map Prod.fst) := by
  change (SourceCursor.advanceAll (renew current depth).cursor inputs).native.current.ingress.atomic = _
  rw [SourceCursor.actual_atomic_next,(renew_whole current depth).2.1]

/-- The stored Type0 source producer feeds this method directly. It allocates
the actual native occurrence and its birth germ before any joint pulse. -/
def fromOld (old : CPS1Deformation.Source.Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (pulseDepth : Nat) : Run frame :=
  renew (SourceCursor.start (CPS1ReactiveField.next (CPS1ReactiveField.start old) actions feed raw)) pulseDepth

open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
def fromSource (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (electronicActions : List CPS1ElectronicSource.Source.RawAction) (electronicFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (nuclearActions : List CPS1QuantumNuclear.Source.RawAction) (nuclearFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (followingActions : List CPS1Following.Source.RawAction) (followingFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (molecularActions : List CPS1MolecularFrame.Source.RawAction) (molecularFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (deformationActions : List CPS1Deformation.Source.RawAction) (deformationFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (pulseDepth : Nat) :
    Option (Σ frame : CPS1Recycling.Frame, Run frame) :=
  match CPS1Deformation.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
      followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed with
  | none => none
  | some source => some ⟨source.1,fromOld source.2 actions feed raw pulseDepth⟩

def advanceFromSource (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (electronicActions : List CPS1ElectronicSource.Source.RawAction) (electronicFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (nuclearActions : List CPS1QuantumNuclear.Source.RawAction) (nuclearFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (followingActions : List CPS1Following.Source.RawAction) (followingFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (molecularActions : List CPS1MolecularFrame.Source.RawAction) (molecularFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (deformationActions : List CPS1Deformation.Source.RawAction) (deformationFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) (pulseDepth : Nat) (inputs : List Input) :
    Option (Σ frame : CPS1Recycling.Frame, Run frame) :=
  (fromSource edits water additional path recycleFeed scanFeed bodyFeed depth
    oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
    followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed actions feed raw pulseDepth).map
    (fun source => ⟨source.1,{source.2 with cursor := SourceCursor.advanceAll source.2.cursor inputs}⟩)


end
end CPS1ReactiveJointNuclear
