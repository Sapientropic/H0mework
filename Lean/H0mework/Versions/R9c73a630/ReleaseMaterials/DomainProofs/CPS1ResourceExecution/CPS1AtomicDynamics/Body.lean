import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Charged
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicSource.Current
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Coulomb

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1AtomicDynamics.Body
noncomputable section
open CPS1AtomicSource CPS1LocalChemicalExecution
open scoped RealInnerProductSpace
abbrev Point := Coulomb.Point

structure Row where
  position : Point
  momentum : Point
  inertia : ℝ
  deriving DecidableEq

structure State (frame : CPS1Recycling.Frame) where
  source : Chain frame
  rows : List (Charged.Address × Row)
  reserve : ℝ
  deriving DecidableEq

def graph (frame : CPS1Recycling.Frame) (state : State frame) : Graph.Molecule :=
  Current.graph frame state.source

def particles (frame : CPS1Recycling.Frame) (state : State frame) : List Charged.Particle :=
  Charged.particles (graph frame state)

def row? (rows : List (Charged.Address × Row)) (address : Charged.Address) : Option Row :=
  (rows.find? (fun item => item.1 = address)).map Prod.snd

def addressPresent (frame : CPS1Recycling.Frame) (state : State frame) (address : Charged.Address) : Bool :=
  (particles frame state).any (fun particle => particle.address = address)

inductive Failure
  | missingRow (address : Charged.Address)
  | unknownAddress (address : Charged.Address)
  | conflictingRow (address : Charged.Address)
  | nonpositiveInertia (address : Charged.Address)
  | collision
  | negativeTime
  | negativeReserve
  | energyShortage
  deriving DecidableEq

/-- Raw measurements can bind an unreported source address once. Motion itself
updates that same row; a later raw report cannot replace its inertia or state. -/
def report? (frame : CPS1Recycling.Frame) (state : State frame)
    (address : Charged.Address) (row : Row) : Except Failure (State frame) :=
  if !(addressPresent frame state address) then .error (.unknownAddress address)
  else if row.inertia ≤ 0 then .error (.nonpositiveInertia address)
  else match row? state.rows address with
  | some old => if old = row then .ok state else .error (.conflictingRow address)
  | none => .ok {state with rows := (address,row) :: state.rows}

def deposit? (frame : CPS1Recycling.Frame) (state : State frame) (amount : ℝ) :
    Except Failure (State frame) :=
  if amount < 0 then .error .negativeReserve
  else .ok {state with reserve := state.reserve+amount}

structure Node where
  particle : Charged.Particle
  row : Row
  deriving DecidableEq

/-- Completeness is computed from every generated particle; it is never a source
premise or a caller-supplied coverage certificate. -/
def gather (particles : List Charged.Particle) (rows : List (Charged.Address × Row)) :
    Except Failure (List Node) :=
  List.rec (.ok []) (fun particle _ tail =>
    match row? rows particle.address with
    | none => .error (.missingRow particle.address)
    | some row =>
      if row.inertia ≤ 0 then .error (.nonpositiveInertia particle.address)
      else match tail with
      | .error failure => .error failure
      | .ok remainder => .ok (⟨particle,row⟩ :: remainder)) particles

def ready (nodes : List Node) : Prop :=
  nodes.Pairwise (fun first second => first.row.position ≠ second.row.position)

def potential (nodes : List Node) : ℝ :=
  List.rec 0 (fun first rest total =>
    (rest.map (fun second => Coulomb.pairEnergy (first.particle.charge : ℝ)
      (second.particle.charge : ℝ) first.row.position second.row.position)).sum + total) nodes

def kinetic (nodes : List Node) : ℝ :=
  (nodes.map (fun node => Coulomb.kinetic node.row.inertia node.row.momentum)).sum

def energy (nodes : List Node) : ℝ := kinetic nodes + potential nodes

/-- The force is the full addressed Coulomb field, in atomic units. No force,
finished potential or native pose is accepted from an action. -/
def force (node : Node) (nodes : List Node) : Point :=
  (nodes.map (fun other => if other.particle.address = node.particle.address then 0 else
    Coulomb.pairForce (node.particle.charge : ℝ) (other.particle.charge : ℝ)
      node.row.position other.row.position)).sum

def kick (node : Node) (nodes : List Node) (dt : ℝ) : Node :=
  let field := force node nodes
  {node with row :=
    {node.row with
      position := node.row.position + (dt / node.row.inertia) • node.row.momentum +
        (dt^2/(2*node.row.inertia)) • field
      momentum := node.row.momentum + dt • field}}

structure Pulse where
  before : List Node
  after : List Node
  elapsed : ℝ
  reserve : ℝ
  difference : ℝ
  returned : ℝ
  deriving DecidableEq

/-- A source pulse samples the current Coulomb field and pays its actual total
energy difference. It does not assert an exact continuum Hamiltonian orbit. -/
def pulse? (frame : CPS1Recycling.Frame) (state : State frame) (dt : ℝ) :
    Except Failure (State frame × Pulse) := by
  classical
  exact
    if dt < 0 then .error .negativeTime
    else if state.reserve < 0 then .error .negativeReserve
    else match gather (particles frame state) state.rows with
    | .error failure => .error failure
    | .ok nodes =>
      if ¬ ready nodes then .error .collision else
      let next := nodes.map (fun node => kick node nodes dt)
      if ¬ ready next then .error .collision else
      let difference := energy next - energy nodes
      if state.reserve < difference then .error .energyShortage else
      let nextState : State frame :=
        {state with
          rows := next.map (fun node => (node.particle.address,node.row))
          reserve := state.reserve-difference}
      .ok (nextState,⟨nodes,next,dt,state.reserve,difference,state.reserve-difference⟩)

theorem pulse_energy (before : List Node) (dt reserve : ℝ) :
    let after := before.map (fun node => kick node before dt)
    energy after + (reserve - (energy after-energy before)) = energy before + reserve := by
  dsimp only
  ring

theorem kick_source (node : Node) (nodes : List Node) (dt : ℝ) :
    (kick node nodes dt).particle = node.particle ∧
    (kick node nodes dt).row.inertia = node.row.inertia := ⟨rfl,rfl⟩

theorem kick_work (node : Node) (nodes : List Node) (dt : ℝ) (positive : 0 < node.row.inertia) :
    Coulomb.kinetic node.row.inertia (kick node nodes dt).row.momentum -
      Coulomb.kinetic node.row.inertia node.row.momentum =
    inner ℝ (force node nodes) ((kick node nodes dt).row.position-node.row.position) := by
  exact Coulomb.midpoint_work _ positive _ _ _ dt

theorem report_source (frame : CPS1Recycling.Frame) (state next : State frame)
    (address : Charged.Address) (row : Row) (paid : report? frame state address row = .ok next) :
    next.source = state.source := by
  by_cases present : addressPresent frame state address = true
  · by_cases positive : row.inertia ≤ 0
    · simp [report?,present,positive] at paid
    · cases old : row? state.rows address with
      | none => simp [report?,present,positive,old] at paid
                cases paid
                rfl
      | some prior =>
        by_cases same : prior = row
        · simp [report?,present,positive,old,same] at paid
          cases paid
          rfl
        · simp [report?,present,positive,old,same] at paid
  · simp [report?,present] at paid

end
end CPS1AtomicDynamics.Body
