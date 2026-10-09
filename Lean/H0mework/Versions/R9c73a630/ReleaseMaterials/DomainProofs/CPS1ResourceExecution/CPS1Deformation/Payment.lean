import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Pulse

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open CPS1ElectronicSource
open scoped BigOperators Matrix InnerProductSpace Matrix.Norms.Elementwise
variable {frame : CPS1Recycling.Frame}

theorem reprice_current_row (state : Material frame) (reserve : ℝ)
    (entry : CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row) :
    (state.reprice reserve).currentRow entry = state.currentRow entry := by
  cases state with
  | mk reference positions momenta occupied originalReserve =>
    dsimp only [Material.reprice]
    simp only [Material.currentRow,Material.nuclearIndex?,Material.nuclearRow]
    cases chosen : (List.finRange reference.geometry.nuclei.length).find?
      (fun index => CPS1MolecularFrame.address reference index = entry.1) <;> rfl

theorem reprice_current_nodes (state : Material frame) (reserve : ℝ) :
    (state.reprice reserve).currentNodes = state.currentNodes := by
  unfold Material.currentNodes
  change state.reference.geometry.nodes.map (fun node =>
    (⟨node.particle,((state.reprice reserve).currentRow (node.particle.address,node.row)).2⟩ : CPS1AtomicDynamics.Body.Node)) = _
  simp only [reprice_current_row]
  rfl

theorem reprice_current_joint_rows (state : Material frame) (reserve : ℝ) :
    (state.reprice reserve).currentJoint.rows = state.currentJoint.rows := by
  unfold Material.currentJoint
  change state.reference.geometry.originJoint.rows.map (state.reprice reserve).currentRow = _
  simp only [show (state.reprice reserve).currentRow = state.currentRow from funext (reprice_current_row state reserve)]

theorem reprice_current_joint_particles (state : Material frame) (reserve : ℝ) :
    CPS1EnzymeBath.Joint.particles frame (state.reprice reserve).currentJoint =
      CPS1EnzymeBath.Joint.particles frame state.currentJoint := rfl

theorem adopt_outcome (reference : CPS1MolecularFrame.Material frame) (next : Material frame)
    (actual : adopt? reference = .ok next) :
    ∃ occupied : Occupation reference.reference,
      normalize? reference.reference (sourcePositions reference.reference) reference.occupied = .ok occupied ∧
      next = (fromMolecular reference occupied).reprice
        (reference.reserve-((fromMolecular reference occupied).energy-reference.energy)) ∧
      0 ≤ reference.reserve ∧ (fromMolecular reference occupied).energy-reference.energy ≤ reference.reserve ∧
      CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame reference.currentJoint)
        reference.currentJoint.rows = .ok reference.reference.geometry.nodes ∧
      CPS1AtomicDynamics.Body.ready reference.reference.geometry.nodes := by
  classical
  unfold adopt? at actual
  split at actual <;> try contradiction
  rename_i nonnegative
  split at actual <;> try contradiction
  try dsimp only at actual
  rename_i nodes gathered
  split at actual <;> try contradiction
  rename_i matched
  split at actual <;> try contradiction
  rename_i ready
  split at actual <;> try contradiction
  try dsimp only at actual
  rename_i occupied normalized
  split at actual <;> try contradiction
  rename_i affordable
  refine ⟨occupied,normalized,(Except.ok.inj actual).symm,not_lt.mp nonnegative,
    not_lt.mp affordable,?_,?_⟩
  · exact gathered.trans (congrArg Except.ok (not_ne_iff.mp matched))
  · simpa only [not_ne_iff.mp matched] using not_not.mp ready

theorem adopt_good (reference : CPS1MolecularFrame.Material frame) (next : Material frame)
    (actual : adopt? reference = .ok next) : Good next := by
  obtain ⟨occupied,normalized,same,_,_,_,_⟩ := adopt_outcome reference next actual
  rw [same]
  exact (normalize_generated reference.reference (sourcePositions reference.reference)
    reference.occupied occupied normalized).1

theorem adopt_paid (reference : CPS1MolecularFrame.Material frame) (next : Material frame)
    (actual : adopt? reference = .ok next) :
    0 ≤ reference.reserve ∧ 0 ≤ next.reserve ∧ next.energy+next.reserve = reference.energy+reference.reserve := by
  obtain ⟨occupied,_,same,nonnegative,affordable,_,_⟩ := adopt_outcome reference next actual
  rw [same,material_reprice_energy]
  exact ⟨nonnegative,sub_nonneg.mpr affordable,by change _+(_-(_-_))=_+_; ring⟩

theorem adopt_source (reference : CPS1MolecularFrame.Material frame) (next : Material frame)
    (actual : adopt? reference = .ok next) :
    next.reference = reference.reference ∧ HEq next.positions (sourcePositions reference.reference) ∧
      HEq next.momenta (sourceMomenta reference.reference) ∧
      next.currentJoint.originBody = reference.currentJoint.originBody ∧
      next.currentJoint.components = reference.currentJoint.components ∧
      next.currentJoint.nextOccurrence = reference.currentJoint.nextOccurrence ∧
      next.currentJoint.reserve = next.reserve := by
  obtain ⟨occupied,_,same,_,_,_,_⟩ := adopt_outcome reference next actual
  rw [same]
  exact ⟨rfl,HEq.rfl,HEq.rfl,rfl,rfl,rfl,rfl⟩

theorem adopt_grounded (reference : CPS1MolecularFrame.Material frame) (next : Material frame)
    (actual : adopt? reference = .ok next) :
    CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame reference.currentJoint)
      reference.currentJoint.rows = .ok reference.reference.geometry.nodes ∧
      CPS1AtomicDynamics.Body.ready reference.reference.geometry.nodes ∧
      IsUnit (gramAt next.reference next.positions) := by
  obtain ⟨occupied,_,same,_,_,gathered,ready⟩ := adopt_outcome reference next actual
  rw [same]
  exact ⟨gathered,ready,source_gram_unit reference.reference⟩

theorem pulse_outcome (state : Material frame) (next : Material frame × ElectronicPulse) (time : ℝ)
    (actual : state.pulse? time = .ok next) :
    ∃ normalized : Occupation state.reference,
      normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) = .ok normalized ∧
      next.1 = (pulseCandidate state time normalized).reprice
        (state.reserve-((pulseCandidate state time normalized).energy-state.energy)) ∧
      0 ≤ time ∧ 0 ≤ state.reserve ∧ (pulseCandidate state time normalized).energy-state.energy ≤ state.reserve ∧
      CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame state.currentJoint)
        state.currentJoint.rows = .ok state.currentNodes ∧
      CPS1AtomicDynamics.Body.ready state.currentNodes ∧
      CPS1AtomicDynamics.Body.ready (nuclearNodesAt state.reference state.positions) ∧
      (IsUnit (gramAt state.reference state.positions) ∧
        ∀ nuclear, 0 < CPS1MolecularFrame.inertia state.reference nuclear) ∧
      IsUnit (gramAt state.reference (state.movedPositions time)) ∧
      CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame (pulseCandidate state time normalized).currentJoint)
        (pulseCandidate state time normalized).currentJoint.rows = .ok (pulseCandidate state time normalized).currentNodes ∧
      CPS1AtomicDynamics.Body.ready (pulseCandidate state time normalized).currentNodes ∧
      CPS1AtomicDynamics.Body.ready (nuclearNodesAt (pulseCandidate state time normalized).reference
        (pulseCandidate state time normalized).positions) := by
  classical
  unfold Material.pulse? at actual
  by_cases negativeTime : time < 0
  · rw [if_pos negativeTime] at actual
    cases actual
  rw [if_neg negativeTime] at actual
  by_cases negativeReserve : state.reserve < 0
  · rw [if_pos negativeReserve] at actual
    cases actual
  rw [if_neg negativeReserve] at actual
  cases gathered : CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame state.currentJoint)
      state.currentJoint.rows with
  | error failure => rw [gathered] at actual; cases actual
  | ok nodes =>
    rw [gathered] at actual
    dsimp only at actual
    by_cases mismatch : nodes ≠ state.currentNodes
    · rw [if_pos mismatch] at actual
      cases actual
    rw [if_neg mismatch] at actual
    by_cases collision : ¬ CPS1AtomicDynamics.Body.ready nodes
    · rw [if_pos collision] at actual
      cases actual
    rw [if_neg collision] at actual
    by_cases nuclearCollision : ¬ CPS1AtomicDynamics.Body.ready (nuclearNodesAt state.reference state.positions)
    · rw [if_pos nuclearCollision] at actual
      cases actual
    rw [if_neg nuclearCollision] at actual
    by_cases nonpositiveMass : ¬ ∀ nuclear, 0 < CPS1MolecularFrame.inertia state.reference nuclear
    · rw [if_pos nonpositiveMass] at actual
      cases actual
    rw [if_neg nonpositiveMass] at actual
    by_cases singular : ¬ IsUnit (gramAt state.reference state.positions)
    · rw [if_pos singular] at actual
      cases actual
    rw [if_neg singular] at actual
    by_cases nextSingular : ¬ IsUnit (gramAt state.reference (state.movedPositions time))
    · rw [if_pos nextSingular] at actual
      cases actual
    rw [if_neg nextSingular] at actual
    cases normalization : normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) with
    | error failure => rw [normalization] at actual; cases actual
    | ok normalized =>
      rw [normalization] at actual
      dsimp only at actual
      cases gatheredAfter : CPS1AtomicDynamics.Body.gather
          (CPS1EnzymeBath.Joint.particles frame (pulseCandidate state time normalized).currentJoint)
          (pulseCandidate state time normalized).currentJoint.rows with
      | error failure => rw [gatheredAfter] at actual; cases actual
      | ok after =>
        rw [gatheredAfter] at actual
        dsimp only at actual
        by_cases afterMismatch : after ≠ (pulseCandidate state time normalized).currentNodes
        · rw [if_pos afterMismatch] at actual
          cases actual
        rw [if_neg afterMismatch] at actual
        by_cases afterCollision : ¬ CPS1AtomicDynamics.Body.ready after
        · rw [if_pos afterCollision] at actual
          cases actual
        rw [if_neg afterCollision] at actual
        by_cases afterNuclearCollision : ¬ CPS1AtomicDynamics.Body.ready
            (nuclearNodesAt (pulseCandidate state time normalized).reference (pulseCandidate state time normalized).positions)
        · rw [if_pos afterNuclearCollision] at actual
          cases actual
        rw [if_neg afterNuclearCollision] at actual
        by_cases shortage : state.reserve < (pulseCandidate state time normalized).energy-state.energy
        · rw [if_pos shortage] at actual
          cases actual
        rw [if_neg shortage] at actual
        refine ⟨normalized,rfl,congrArg Prod.fst (Except.ok.inj actual).symm,not_lt.mp negativeTime,
          not_lt.mp negativeReserve,not_lt.mp shortage,?_,?_,not_not.mp nuclearCollision,
          ⟨not_not.mp singular,not_not.mp nonpositiveMass⟩,not_not.mp nextSingular,?_,?_,not_not.mp afterNuclearCollision⟩
        · exact congrArg Except.ok (not_ne_iff.mp mismatch)
        · simpa only [not_ne_iff.mp mismatch] using not_not.mp collision
        · exact gatheredAfter.trans (congrArg Except.ok (not_ne_iff.mp afterMismatch))
        · simpa only [not_ne_iff.mp afterMismatch] using not_not.mp afterCollision

theorem pulse_good (state : Material frame) (next : Material frame × ElectronicPulse) (time : ℝ)
    (actual : state.pulse? time = .ok next) : Good next.1 := by
  obtain ⟨normalized,normalization,same,_,_,_,_,_,_,_,_,_,_,_⟩ := pulse_outcome state next time actual
  rw [same]
  exact physical_fock_response_good state.reference (state.movedPositions time) normalized time
    (normalize_generated state.reference (state.movedPositions time) (state.transportedOccupation time)
      normalized normalization).1

theorem pulse_paid (state : Material frame) (next : Material frame × ElectronicPulse) (time : ℝ)
    (actual : state.pulse? time = .ok next) :
    0 ≤ time ∧ 0 ≤ state.reserve ∧ 0 ≤ next.1.reserve ∧ next.1.energy+next.1.reserve = state.energy+state.reserve := by
  obtain ⟨normalized,_,same,nonnegativeTime,nonnegativeReserve,affordable,_,_,_,_,_,_,_,_⟩ :=
    pulse_outcome state next time actual
  rw [same,material_reprice_energy]
  exact ⟨nonnegativeTime,nonnegativeReserve,sub_nonneg.mpr affordable,by change _+(_-(_-_))=_+_; ring⟩

theorem pulse_same_source (state : Material frame) (next : Material frame × ElectronicPulse) (time : ℝ)
    (actual : state.pulse? time = .ok next) :
    next.1.reference = state.reference ∧ HEq next.1.positions (state.movedPositions time) ∧
      HEq next.1.momenta (state.movedMomenta time) ∧
      next.1.currentJoint.originBody = state.currentJoint.originBody ∧
      next.1.currentJoint.components = state.currentJoint.components ∧
      next.1.currentJoint.nextOccurrence = state.currentJoint.nextOccurrence ∧
      next.1.currentJoint.rows.map Prod.fst = state.currentJoint.rows.map Prod.fst ∧
      next.1.currentJoint.reserve = next.1.reserve := by
  obtain ⟨normalized,_,same,_,_,_,_,_,_,_,_,_,_,_⟩ := pulse_outcome state next time actual
  rw [same]
  refine ⟨rfl,HEq.rfl,HEq.rfl,rfl,rfl,rfl,?_,rfl⟩
  rw [current_joint_addresses,current_joint_addresses]
  rfl

theorem pulse_grounded (state : Material frame) (next : Material frame × ElectronicPulse) (time : ℝ)
    (actual : state.pulse? time = .ok next) :
    CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame state.currentJoint)
      state.currentJoint.rows = .ok state.currentNodes ∧
      CPS1AtomicDynamics.Body.ready state.currentNodes ∧
      CPS1AtomicDynamics.Body.ready (nuclearNodesAt state.reference state.positions) ∧
      IsUnit (gramAt state.reference state.positions) ∧
      CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame next.1.currentJoint)
        next.1.currentJoint.rows = .ok next.1.currentNodes ∧
      CPS1AtomicDynamics.Body.ready next.1.currentNodes ∧
      CPS1AtomicDynamics.Body.ready (nuclearNodesAt next.1.reference next.1.positions) ∧
      IsUnit (gramAt next.1.reference next.1.positions) := by
  obtain ⟨normalized,_,same,_,_,_,gathered,ready,nuclearReady,currentUnit,nextUnit,
    gatheredAfter,readyAfter,nuclearReadyAfter⟩ := pulse_outcome state next time actual
  rw [same]
  rw [reprice_current_nodes,reprice_current_joint_rows,reprice_current_joint_particles]
  refine ⟨gathered,ready,nuclearReady,currentUnit.1,?_,?_,nuclearReadyAfter,nextUnit⟩
  · exact gatheredAfter
  · exact readyAfter

theorem pulse_force_generated (state : Material frame) (next : Material frame × ElectronicPulse) (time : ℝ)
    (actual : state.pulse? time = .ok next) (direction : NuclearConfiguration state.reference) :
    IsUnit (gramAt state.reference state.positions) ∧
      HasDerivAt (fun elapsed : ℝ => energyWithMomenta state.reference (state.positions+elapsed • direction) state.momenta
        (state.occupied+elapsed • occupiedConnectionRate state.reference state.positions direction state.occupied))
        (-(∑ nuclear, inner ℝ (euclideanPoint (state.jointForce nuclear)) (euclideanPoint (direction nuclear)))) 0 := by
  obtain ⟨_,_,_,_,_,_,_,_,ready,unit,_,_,_,_⟩ := pulse_outcome state next time actual
  exact ⟨unit.1,covariant_full_energy_line state.reference state.positions state.momenta direction state.occupied ready⟩

theorem pulse_nuclear_work (state : Material frame) (next : Material frame × ElectronicPulse) (time : ℝ)
    (actual : state.pulse? time = .ok next) (nuclear : CPS1MolecularFrame.NuclearIndex state.reference) :
    CPS1AtomicDynamics.Coulomb.kinetic (CPS1MolecularFrame.inertia state.reference nuclear)
        (euclideanPoint (state.movedMomenta time nuclear)) -
      CPS1AtomicDynamics.Coulomb.kinetic (CPS1MolecularFrame.inertia state.reference nuclear)
        (euclideanPoint (state.momenta nuclear)) =
      inner ℝ (euclideanPoint (state.jointForce nuclear))
        (euclideanPoint (state.movedPositions time nuclear)-euclideanPoint (state.positions nuclear)) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,unit,_,_,_,_⟩ := pulse_outcome state next time actual
  exact nuclear_midpoint_work state.reference state.positions state.momenta state.jointForce time nuclear (unit.2 nuclear)

theorem pulse_generated_fields (state : Material frame) (next : Material frame × ElectronicPulse) (time : ℝ)
    (actual : state.pulse? time = .ok next) :
    Orthonormal ℂ next.1.currentFields ∧
      CPS1ElectronicEvolution.slaterDual next.1.currentFields (CPS1ElectronicEvolution.slater next.1.currentFields) = 1 :=
  ⟨pulse_good state next time actual,CPS1ElectronicEvolution.slater_normalized _ (pulse_good state next time actual)⟩

theorem actual_midpoint (state : Material frame) (next : Material frame × ElectronicPulse) (time : ℝ)
    (actual : state.pulse? time = .ok next) :
    ∃ normalized : Occupation state.reference,
      normalize? state.reference (state.movedPositions time) (state.transportedOccupation time) = .ok normalized ∧
      HEq next.1.currentFields (occupiedFieldsAt state.reference (state.movedPositions time)
        (physicalFockResponse state.reference (state.movedPositions time) normalized time)) ∧
      ∀ slot : ElectronIndex state.reference.geometry,
        let before := occupiedFieldsAt state.reference (state.movedPositions time) normalized slot
        let after := occupiedFieldsAt state.reference (state.movedPositions time)
          (physicalFockResponse state.reference (state.movedPositions time) normalized time) slot
        after+(Complex.I*((time/2 : ℝ) : ℂ)) • physicalAction state.reference (state.movedPositions time) normalized after =
          before-(Complex.I*((time/2 : ℝ) : ℂ)) • physicalAction state.reference (state.movedPositions time) normalized before := by
  obtain ⟨normalized,normalization,same,_,_,_,_,_,_,_,_,_,_,_⟩ := pulse_outcome state next time actual
  refine ⟨normalized,normalization,?_,fun slot => physical_fock_midpoint _ _ _ _ slot⟩
  rw [same]
  exact HEq.rfl

theorem normalize_keeps_good_at_unit (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied next : Occupation source)
    (unit : IsUnit (gramAt source positions)) (good : Orthonormal ℂ (occupiedFieldsAt source positions occupied))
    (actual : normalize? source positions occupied = .ok next) : next = occupied := by
  unfold normalize? at actual
  split at actual <;> try contradiction
  cases Except.ok.inj actual
  exact fields_injective_at_unit source positions unit _ _ (normalization_current_fields source positions occupied _ good)

theorem normalize_good_at_unit (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source)
    (unit : IsUnit (gramAt source positions)) (good : Orthonormal ℂ (occupiedFieldsAt source positions occupied)) :
    normalize? source positions occupied = .ok occupied := by
  have enough : electronCount frame source.geometry.originJoint ≤
      CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (occupiedFieldsAt source positions occupied) := by
    simpa only [ElectronIndex,Fintype.card_fin] using
      CPS1MolecularFrame.FiniteNormed.independent_subfamily_rank_le (𝕜 := ℂ)
        (occupiedFieldsAt source positions occupied) id good.linearIndependent
  unfold normalize?
  rw [dif_pos enough]
  exact congrArg Except.ok (fields_injective_at_unit source positions unit _ _
    (normalization_current_fields source positions occupied enough good))

theorem from_molecular_energy (reference : CPS1MolecularFrame.Material frame) :
    (fromMolecular reference reference.occupied).energy = reference.energy :=
  energy_with_momenta_source reference.reference reference.occupied

theorem adopt_at_generated_current (reference : CPS1MolecularFrame.Material frame)
    (generated : CPS1MolecularFrame.Good reference) (nonnegative : 0 ≤ reference.reserve)
    (gathered : CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame reference.currentJoint)
      reference.currentJoint.rows = .ok reference.reference.geometry.nodes)
    (ready : CPS1AtomicDynamics.Body.ready reference.reference.geometry.nodes) :
    adopt? reference = .ok (fromMolecular reference reference.occupied) := by
  have fields : Orthonormal ℂ (occupiedFieldsAt reference.reference (sourcePositions reference.reference) reference.occupied) := by
    rw [occupiedFieldsAt,basis_source]
    exact CPS1MolecularFrame.material_fields reference generated
  have normalized := normalize_good_at_unit reference.reference (sourcePositions reference.reference)
    reference.occupied (source_gram_unit reference.reference) fields
  unfold adopt?
  rw [if_neg (not_lt.mpr nonnegative),gathered]
  dsimp only
  rw [if_neg (not_ne_iff.mpr rfl),if_neg (not_not.mpr ready),normalized]
  dsimp only
  rw [from_molecular_energy,sub_self,if_neg (not_lt.mpr nonnegative),sub_zero]
  rfl

theorem transported_occupation_zero (state : Material frame) : state.transportedOccupation 0 = state.occupied := by
  have connectionZero := (occupiedConnectionDifferential state.reference state.positions state.occupied).map_zero
  change occupiedConnectionRate state.reference state.positions 0 state.occupied = 0 at connectionZero
  simp only [Material.transportedOccupation,Material.movedPositions,kick_positions_zero,sub_self,connectionZero,add_zero]

theorem pulse_zero_time (state : Material frame) (next : Material frame × ElectronicPulse)
    (actual : state.pulse? 0 = .ok next) (good : Good state) : next.1 = state := by
  obtain ⟨normalized,normalization,same,_,_,_,_,_,_,unit,_,_,_,_⟩ := pulse_outcome state next 0 actual
  have positions : state.movedPositions 0 = state.positions := kick_positions_zero _ _ _ _
  rw [positions,transported_occupation_zero] at normalization
  have coefficients := normalize_keeps_good_at_unit state.reference state.positions state.occupied normalized
    unit.1 good normalization
  have candidate : pulseCandidate state 0 normalized = state := by
    rw [coefficients]
    unfold pulseCandidate
    rw [positions]
    change (⟨state.reference,state.positions,kickMomenta state.reference state.momenta state.jointForce 0,
      physicalFockResponse state.reference state.positions state.occupied 0,state.reserve⟩ : Material frame) = state
    rw [kick_momenta_zero,physical_fock_response_coefficients_zero _ _ _ unit.1]
  rw [candidate,sub_self,sub_zero] at same
  exact same

theorem deposit_good (state next : Material frame) (amount : ℝ)
    (actual : state.deposit? amount = .ok next) (good : Good state) : Good next := by
  unfold Material.deposit? at actual
  split at actual <;> try contradiction
  cases Except.ok.inj actual
  exact good

theorem deposit_paid (state next : Material frame) (amount : ℝ)
    (actual : state.deposit? amount = .ok next) :
    0 ≤ amount ∧ next.energy+next.reserve = state.energy+state.reserve+amount ∧ next.currentJoint.reserve = next.reserve := by
  unfold Material.deposit? at actual
  split at actual <;> try contradiction
  rename_i nonnegative
  cases Except.ok.inj actual
  rw [material_reprice_energy]
  exact ⟨not_lt.mp nonnegative,by change _+(_+_)=_+_+_; ring,rfl⟩

end
end CPS1Deformation
