import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Payment

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1PositivePulse
noncomputable section
open CPS1Deformation CPS1ElectronicSource
variable {frame : CPS1Recycling.Frame}

private theorem gather_cons (particle : CPS1AtomicDynamics.Charged.Particle)
    (rest : List CPS1AtomicDynamics.Charged.Particle)
    (rows : List (CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row)) :
    CPS1AtomicDynamics.Body.gather (particle :: rest) rows =
      match CPS1AtomicDynamics.Body.row? rows particle.address with
      | none => .error (.missingRow particle.address)
      | some row => if row.inertia ≤ 0 then .error (.nonpositiveInertia particle.address)
        else match CPS1AtomicDynamics.Body.gather rest rows with
          | .error failure => .error failure
          | .ok tail => .ok (⟨particle,row⟩ :: tail) := rfl

private theorem row_read_map
    (transform : CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row →
      CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row)
    (addresses : ∀ entry, (transform entry).1 = entry.1)
    (rows : List (CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row))
    (address : CPS1AtomicDynamics.Charged.Address) :
    CPS1AtomicDynamics.Body.row? (rows.map transform) address =
      (CPS1AtomicDynamics.Body.row? rows address).map (fun row => (transform (address,row)).2) := by
  classical
  induction rows with
  | nil => rfl
  | cons entry rest ih =>
    by_cases same : entry.1 = address
    · obtain ⟨key,row⟩ := entry
      dsimp only at same
      subst address
      simp [CPS1AtomicDynamics.Body.row?,addresses]
    · simpa [CPS1AtomicDynamics.Body.row?,addresses,same] using ih

private theorem gather_map_success
    (transform : CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row →
      CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row)
    (addresses : ∀ entry, (transform entry).1 = entry.1)
    (rows : List (CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row))
    (inertias : ∀ address row, CPS1AtomicDynamics.Body.row? rows address = some row →
      (transform (address,row)).2.inertia = row.inertia)
    (particles : List CPS1AtomicDynamics.Charged.Particle)
    (nodes : List CPS1AtomicDynamics.Body.Node)
    (actual : CPS1AtomicDynamics.Body.gather particles rows = .ok nodes) :
    CPS1AtomicDynamics.Body.gather particles (rows.map transform) =
      .ok (nodes.map (fun node =>
        (⟨node.particle,(transform (node.particle.address,node.row)).2⟩ : CPS1AtomicDynamics.Body.Node))) := by
  classical
  induction particles generalizing nodes with
  | nil =>
    have empty : nodes = [] := (Except.ok.inj actual).symm
    subst nodes
    rfl
  | cons particle rest ih =>
    cases found : CPS1AtomicDynamics.Body.row? rows particle.address with
    | none => simp [gather_cons,found] at actual
    | some row =>
      by_cases invalid : row.inertia ≤ 0
      · simp [gather_cons,found,invalid] at actual
      · cases remainder : CPS1AtomicDynamics.Body.gather rest rows with
        | error missing => simp [gather_cons,found,invalid,remainder] at actual
        | ok tail =>
          have identified : nodes = (⟨particle,row⟩ : CPS1AtomicDynamics.Body.Node) :: tail := by
            simpa [gather_cons,found,invalid,remainder] using actual.symm
          rw [identified]
          have transported := ih tail remainder
          have read := row_read_map transform addresses rows particle.address
          rw [found] at read
          simp only [Option.map_some] at read
          simp [gather_cons,read,inertias particle.address row found,
            invalid,transported]

theorem current_row_absorbs (source : CPS1ElectronicSource.State frame)
    (firstPositions firstMomenta secondPositions secondMomenta : NuclearConfiguration source)
    (firstOccupied secondOccupied : Occupation source) (firstReserve secondReserve : ℝ)
    (entry : CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row) :
    let first : Material frame := ⟨source,firstPositions,firstMomenta,firstOccupied,firstReserve⟩
    let second : Material frame := ⟨source,secondPositions,secondMomenta,secondOccupied,secondReserve⟩
    second.currentRow (first.currentRow entry) = second.currentRow entry := by
  dsimp only
  simp only [Material.currentRow,Material.nuclearIndex?]
  cases selected : (List.finRange source.geometry.nuclei.length).find?
      (fun index => CPS1MolecularFrame.address source index = entry.1) <;> rfl

theorem current_row_inertia (source : CPS1ElectronicSource.State frame)
    (firstPositions firstMomenta secondPositions secondMomenta : NuclearConfiguration source)
    (firstOccupied secondOccupied : Occupation source) (firstReserve secondReserve : ℝ)
    (entry : CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row) :
    let first : Material frame := ⟨source,firstPositions,firstMomenta,firstOccupied,firstReserve⟩
    let second : Material frame := ⟨source,secondPositions,secondMomenta,secondOccupied,secondReserve⟩
    (second.currentRow (first.currentRow entry)).2.inertia = (first.currentRow entry).2.inertia := by
  dsimp only
  simp only [Material.currentRow,Material.nuclearIndex?]
  cases selected : (List.finRange source.geometry.nuclei.length).find?
      (fun index => CPS1MolecularFrame.address source index = entry.1) <;> rfl

theorem current_rows_transport (source : CPS1ElectronicSource.State frame)
    (firstPositions firstMomenta secondPositions secondMomenta : NuclearConfiguration source)
    (firstOccupied secondOccupied : Occupation source) (firstReserve secondReserve : ℝ) :
    let first : Material frame := ⟨source,firstPositions,firstMomenta,firstOccupied,firstReserve⟩
    let second : Material frame := ⟨source,secondPositions,secondMomenta,secondOccupied,secondReserve⟩
    first.currentJoint.rows.map second.currentRow = second.currentJoint.rows := by
  dsimp only
  simp only [Material.currentJoint,List.map_map]
  apply List.map_congr_left
  intro entry _
  exact current_row_absorbs source firstPositions firstMomenta secondPositions secondMomenta
    firstOccupied secondOccupied firstReserve secondReserve entry

theorem current_gather_transport (source : CPS1ElectronicSource.State frame)
    (firstPositions firstMomenta secondPositions secondMomenta : NuclearConfiguration source)
    (firstOccupied secondOccupied : Occupation source) (firstReserve secondReserve : ℝ) :
    let first : Material frame := ⟨source,firstPositions,firstMomenta,firstOccupied,firstReserve⟩
    let second : Material frame := ⟨source,secondPositions,secondMomenta,secondOccupied,secondReserve⟩
    CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame first.currentJoint)
      first.currentJoint.rows = .ok first.currentNodes →
    CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame second.currentJoint)
      second.currentJoint.rows = .ok second.currentNodes := by
  dsimp only
  let first : Material frame := ⟨source,firstPositions,firstMomenta,firstOccupied,firstReserve⟩
  let second : Material frame := ⟨source,secondPositions,secondMomenta,secondOccupied,secondReserve⟩
  change CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame first.currentJoint)
    first.currentJoint.rows = .ok first.currentNodes →
    CPS1AtomicDynamics.Body.gather (CPS1EnzymeBath.Joint.particles frame second.currentJoint)
    second.currentJoint.rows = .ok second.currentNodes
  intro actual
  have addresses : ∀ entry, (second.currentRow entry).1 = entry.1 := fun _ => rfl
  have inertias : ∀ address row, CPS1AtomicDynamics.Body.row? first.currentJoint.rows address = some row →
      (second.currentRow (address,row)).2.inertia = row.inertia := by
    intro address row found
    have read := row_read_map first.currentRow (fun _ => rfl)
      source.geometry.originJoint.rows address
    change CPS1AtomicDynamics.Body.row? first.currentJoint.rows address = _ at read
    rw [read] at found
    cases original : CPS1AtomicDynamics.Body.row? source.geometry.originJoint.rows address with
    | none => simp [original] at found
    | some initial =>
      simp only [original,Option.map_some,Option.some.injEq] at found
      rw [← found]
      exact current_row_inertia source firstPositions firstMomenta secondPositions secondMomenta
        firstOccupied secondOccupied firstReserve secondReserve (address,initial)
  have transported := gather_map_success second.currentRow addresses first.currentJoint.rows inertias
    (CPS1EnzymeBath.Joint.particles frame first.currentJoint) first.currentNodes actual
  rw [current_rows_transport source firstPositions firstMomenta secondPositions secondMomenta
    firstOccupied secondOccupied firstReserve secondReserve] at transported
  have nodes : first.currentNodes.map
      (fun node => (⟨node.particle,(second.currentRow (node.particle.address,node.row)).2⟩ :
        CPS1AtomicDynamics.Body.Node)) = second.currentNodes := by
    simp only [Material.currentNodes,List.map_map]
    apply List.map_congr_left
    intro node _
    exact congrArg (fun entry => (⟨node.particle,entry.2⟩ : CPS1AtomicDynamics.Body.Node))
      (current_row_absorbs source firstPositions firstMomenta secondPositions secondMomenta
        firstOccupied secondOccupied firstReserve secondReserve (node.particle.address,node.row))
  rw [nodes] at transported
  exact transported

end
end CPS1PositivePulse
