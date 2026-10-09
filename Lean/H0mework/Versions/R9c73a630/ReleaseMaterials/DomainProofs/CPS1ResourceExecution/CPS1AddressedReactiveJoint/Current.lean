import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedReactiveJoint.Rows

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CPS1AddressedReactiveJoint
noncomputable section
open CPS1AddressedHydrolysis CPS1LocalChemicalExecution
variable {frame : CPS1Recycling.Frame}

structure Body (frame : CPS1Recycling.Frame) where
  atomic : Atomic.Occurrence frame
  atoms : List Atom
  nodes : List CPS1AtomicDynamics.Body.Node
  sourceRows : Rows.Stock
  reserve : ℝ
  missing : List (LocalMaterial frame × Missing)

def Body.energy (body : Body frame) : ℝ := CPS1AtomicDynamics.Body.energy body.nodes

def Body.account (body : Body frame) : ℝ := body.energy+body.reserve

def admit? (current : Atomic.Occurrence frame) (state : Rows.State) : Except Rows.Failure (Body frame) := by
  classical
  exact if state.reserve < 0 then .error .negativeEnergy
    else match Rows.gather (atoms current.history current.source.stock) state.rows with
    | .error failure => .error failure
    | .ok nodes =>
      if ¬ CPS1AtomicDynamics.Body.ready nodes then .error (.body .collision)
      else .ok ⟨current,atoms current.history current.source.stock,nodes,state.rows,state.reserve,
        residuals current.history current.source.stock⟩

def BodyProperties (current : Atomic.Occurrence frame) (state : Rows.State) (body : Body frame) : Prop :=
  body.atomic = current ∧ body.atoms = atoms current.history current.source.stock ∧
    body.sourceRows = state.rows ∧ body.reserve = state.reserve ∧ 0 ≤ body.reserve ∧
    body.missing = residuals current.history current.source.stock ∧
    (body.atoms.map Atom.origin).Nodup ∧
    body.nodes.map CPS1AtomicDynamics.Body.Node.particle = (particles body.atoms).map Particle.readout ∧
    CPS1AtomicDynamics.Body.ready body.nodes ∧
    (∀ node ∈ body.nodes, 0 < node.row.inertia ∧
      ∃ particle ∈ particles body.atoms, node.particle = particle.readout ∧
        Rows.row? body.sourceRows particle.address = some node.row)

theorem admitted_body (current : Atomic.Occurrence frame) (state : Rows.State) (body : Body frame)
    (actual : admit? current state = .ok body) : BodyProperties current state body := by
  unfold admit? at actual
  split at actual
  · cases actual
  · rename_i nonnegative
    cases gathered : Rows.gather (atoms current.history current.source.stock) state.rows with
    | error => simp only [gathered] at actual; cases actual
    | ok nodes =>
      simp only [gathered] at actual
      split at actual
      · cases actual
      · rename_i ready
        cases Except.ok.inj actual
        have source := Rows.gather_generated _ _ _ gathered
        exact ⟨rfl,rfl,rfl,rfl,le_of_not_gt nonnegative,rfl,source.1,source.2.1,not_not.mp ready,source.2.2⟩

structure Stage (frame : CPS1Recycling.Frame) where
  before : List (Block frame)
  after : List (Block frame)
  measurements : Rows.Execution
  body : Except Rows.Failure (Body frame)

structure Occurrence (frame : CPS1Recycling.Frame) where
  atomic : Atomic.Occurrence frame
  measurements : Rows.State
  pending : List Rows.RawAction
  stages : List (Stage frame)

def start (source : CPS1AddressedChemicalReaction.Source.Occurrence frame) : Occurrence frame :=
  ⟨Atomic.start source,⟨[],0⟩,[],[]⟩

/-- The raw rows meet this source's available particle carrier before its actual
fire. Slot readouts are regenerated from the output carrier; the rows stay keyed
by origin, including water already incorporated by an earlier event. -/
def next (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List Rows.RawAction) : Occurrence frame :=
  let available := CPS1AddressedChemicalReaction.Source.available current.atomic.source actions feed
  let before := blocks current.atomic.history available
  let sourceParticles := particles (atoms current.atomic.history available)
  let measured := Rows.run sourceParticles current.measurements (raw ++ current.pending)
  let generated := Atomic.next current.atomic actions feed
  let after := blocks generated.history generated.source.stock
  let body := admit? generated measured.state
  ⟨generated,measured.state,measured.pending,current.stages ++ [⟨before,after,measured,body⟩]⟩

def admission (current : Occurrence frame) : Except Rows.Failure (Body frame) :=
  admit? current.atomic current.measurements

theorem source_generated_reactive_next (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List Rows.RawAction) :
    type_of% (Atomic.source_generated_atomic_next current.atomic actions feed) ∧
    (next current actions feed raw).atomic = Atomic.next current.atomic actions feed ∧
    (blocks current.atomic.history
      (CPS1AddressedChemicalReaction.Source.available current.atomic.source actions feed)).map Block.material =
      CPS1AddressedChemicalReaction.Source.available current.atomic.source actions feed ∧
    (blocks (next current actions feed raw).atomic.history (next current actions feed raw).atomic.source.stock).map
      Block.material = (next current actions feed raw).atomic.source.stock ∧
    (Rows.run (particles (atoms current.atomic.history
      (CPS1AddressedChemicalReaction.Source.available current.atomic.source actions feed)))
      current.measurements (raw ++ current.pending)).paid ++ (next current actions feed raw).pending =
      raw ++ current.pending ∧
    (∀ address row, Rows.row? current.measurements.rows address = some row →
      Rows.row? (next current actions feed raw).measurements.rows address = some row) ∧
    current.stages.Sublist (next current actions feed raw).stages ∧
    (∀ body, admission (next current actions feed raw) = .ok body →
      BodyProperties (next current actions feed raw).atomic (next current actions feed raw).measurements body) :=
  ⟨Atomic.source_generated_atomic_next current.atomic actions feed,rfl,blocks_whole _ _,blocks_whole _ _,
    Rows.run_whole _ _ _,Rows.run_rows_preserved _ _ _,List.sublist_append_left _ _,admitted_body _ _⟩

def advanceAll (current : Occurrence frame)
    (inputs : List (CPS1AddressedChemicalReaction.Source.Input × List Rows.RawAction)) : Occurrence frame :=
  List.rec (motive := fun _ => Occurrence frame → Occurrence frame)
    (fun prior => prior)
    (fun input _ recur prior => recur (next prior input.1.1 input.1.2 input.2)) inputs current

theorem advance_all_nil (current : Occurrence frame) : advanceAll current [] = current := rfl

theorem advance_all_cons (current : Occurrence frame)
    (input : CPS1AddressedChemicalReaction.Source.Input × List Rows.RawAction)
    (rest : List (CPS1AddressedChemicalReaction.Source.Input × List Rows.RawAction)) :
    advanceAll current (input :: rest) = advanceAll (next current input.1.1 input.1.2 input.2) rest := rfl

theorem advance_all_atomic (current : Occurrence frame)
    (inputs : List (CPS1AddressedChemicalReaction.Source.Input × List Rows.RawAction)) :
    (advanceAll current inputs).atomic = Atomic.advanceAll current.atomic (inputs.map Prod.fst) := by
  induction inputs generalizing current with
  | nil => rfl
  | cons input rest ih =>
    simpa only [advance_all_cons,List.map_cons,Atomic.advance_all_cons,next] using
      ih (next current input.1.1 input.1.2 input.2)

def fromSource
    (edits : SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) (raw : List Rows.RawAction) :
    Option (Σ frame : CPS1Recycling.Frame, Occurrence frame) := do
  let previous ← CPS1LocalChemicalExecution.Source.actualCapture edits water additional path
    recycleFeed scanFeed bodyFeed depth
  let current := start (CPS1AddressedChemicalReaction.Source.start previous.2)
  pure ⟨previous.1,next current (actions ++ CPS1LocalChemicalExecution.Source.chemicalActions) feed raw⟩

theorem from_source_project
    (edits : SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target.Edits)
    (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) (raw : List Rows.RawAction) :
    (fromSource edits water additional path recycleFeed scanFeed bodyFeed depth actions feed raw).map
      (fun current => ⟨current.1,current.2.atomic⟩) =
      Atomic.fromSource edits water additional path recycleFeed scanFeed bodyFeed depth actions feed := by
  unfold fromSource Atomic.fromSource
  cases CPS1LocalChemicalExecution.Source.actualCapture edits water additional path recycleFeed scanFeed bodyFeed depth with
  | none => rfl
  | some => rfl

end
end CPS1AddressedReactiveJoint
