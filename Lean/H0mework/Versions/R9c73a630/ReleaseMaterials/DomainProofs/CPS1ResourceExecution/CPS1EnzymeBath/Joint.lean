import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Primary
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Contract

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CPS1EnzymeBath.Joint
noncomputable section
open CPS1AtomicDynamics

structure Component where
  occurrence : Nat
  kind : Primary.TemplateKind
  deriving DecidableEq

inductive AtomOrigin
  | enzyme (source : CPS1AtomicSource.Graph.Atom)
  | bath (component : Component) (source : Primary.Atom)
  deriving DecidableEq

/-- The full source tag remains on the common carrier. Graph.Atom below is only a
chemical descriptor readout used by the already paid generic Coulomb calculus. -/
structure Atom where
  origin : AtomOrigin
  descriptor : CPS1AtomicSource.Graph.Atom
  deriving DecidableEq

inductive Address
  | enzyme (address : CPS1AtomicSource.Graph.Address)
  | bath (occurrence ordinal : Nat)
  deriving DecidableEq

def Atom.address (atom : Atom) : Address :=
  match atom.origin with
  | .enzyme source => .enzyme source.address
  | .bath component source => .bath component.occurrence source.ordinal

inductive BondOrigin
  | enzyme (source : CPS1AtomicSource.Graph.Bond)
  | bath (component : Component) (source : Primary.Bond)
  deriving DecidableEq

structure Bond where
  origin : BondOrigin
  left : Address
  right : Address
  deriving DecidableEq

def bathAtom (component : Component) (atom : Primary.Atom) : Atom :=
  ⟨.bath component atom,
    ⟨⟨component.occurrence,toString atom.ordinal⟩,
      ⟨toString atom.ordinal,atom.element,atom.charge,atom.aromatic,atom.stereo,false,false,false,false⟩⟩⟩

structure State (frame : CPS1Recycling.Frame) where
  originBody : Body.State frame
  components : List Component
  nextOccurrence : Nat
  rows : List (Charged.Address × Body.Row)
  reserve : ℝ
  deriving DecidableEq

def fromBody (frame : CPS1Recycling.Frame) (body : Body.State frame) : State frame :=
  ⟨body,[],0,body.rows,body.reserve⟩

def atoms (frame : CPS1Recycling.Frame) (state : State frame) : List Atom :=
  ((Body.graph frame state.originBody).atoms.map (fun atom => ⟨.enzyme atom,atom⟩)) ++
    state.components.flatMap (fun component => (Primary.template component.kind).atoms.map (bathAtom component))

def bonds (frame : CPS1Recycling.Frame) (state : State frame) : List Bond :=
  ((Body.graph frame state.originBody).bonds.map (fun bond =>
    ⟨.enzyme bond,.enzyme bond.left,.enzyme bond.right⟩)) ++
    state.components.flatMap (fun component => (Primary.template component.kind).bonds.map (fun bond =>
      ⟨.bath component bond,.bath component.occurrence bond.left,.bath component.occurrence bond.right⟩))

/-- This descriptor list is only the charged-particle calculus readout. The
source-tagged complete chemical bonds are retained by `bonds`. -/
def descriptorGraph (frame : CPS1Recycling.Frame) (state : State frame) : CPS1AtomicSource.Graph.Molecule :=
  ⟨(atoms frame state).map Atom.descriptor,[],[]⟩

def particles (frame : CPS1Recycling.Frame) (state : State frame) : List Charged.Particle :=
  Charged.particles (descriptorGraph frame state)

/-- Append-only components preserve every previously allocated global particle
slot, the original enzyme source occurrence, all measured rows and the existing reserve. -/
def attach (frame : CPS1Recycling.Frame) (state : State frame) (kind : Primary.TemplateKind) : State frame :=
  {state with
    components := state.components ++ [⟨state.nextOccurrence,kind⟩]
    nextOccurrence := state.nextOccurrence+1}

def addressPresent (frame : CPS1Recycling.Frame) (state : State frame) (address : Charged.Address) : Bool :=
  (particles frame state).any (fun particle => particle.address = address)

def report? (frame : CPS1Recycling.Frame) (state : State frame) (address : Charged.Address) (row : Body.Row) :
    Except Body.Failure (State frame) :=
  if !(addressPresent frame state address) then .error (.unknownAddress address)
  else if row.inertia ≤ 0 then .error (.nonpositiveInertia address)
  else match Body.row? state.rows address with
  | some old => if old = row then .ok state else .error (.conflictingRow address)
  | none => .ok {state with rows := (address,row) :: state.rows}

def deposit? (frame : CPS1Recycling.Frame) (state : State frame) (amount : ℝ) :
    Except Body.Failure (State frame) :=
  if amount < 0 then .error .negativeReserve else .ok {state with reserve := state.reserve+amount}

/-- Both enzyme and ligand coordinates enter the same fixed pair field. The old
body potential/force/kick are generic on source-tagged charged nodes. -/
def pulse? (frame : CPS1Recycling.Frame) (state : State frame) (dt : ℝ) :
    Except Body.Failure (State frame × Body.Pulse) := by
  classical
  exact
    if dt < 0 then .error .negativeTime
    else if state.reserve < 0 then .error .negativeReserve
    else match Body.gather (particles frame state) state.rows with
    | .error failure => .error failure
    | .ok nodes =>
      if ¬ Body.ready nodes then .error .collision else
      let next := nodes.map (fun node => Body.kick node nodes dt)
      if ¬ Body.ready next then .error .collision else
      let difference := Body.energy next-Body.energy nodes
      if state.reserve < difference then .error .energyShortage else
      .ok (
        {state with
          rows := next.map (fun node => (node.particle.address,node.row))
          reserve := state.reserve-difference},
        ⟨nodes,next,dt,state.reserve,difference,state.reserve-difference⟩)

theorem append_retains (frame : CPS1Recycling.Frame) (state : State frame) (kind : Primary.TemplateKind) :
    (attach frame state kind).originBody = state.originBody ∧ (attach frame state kind).rows = state.rows ∧
    (attach frame state kind).reserve = state.reserve ∧
    (attach frame state kind).components = state.components ++ [⟨state.nextOccurrence,kind⟩] :=
  ⟨rfl,rfl,rfl,rfl⟩

end
end CPS1EnzymeBath.Joint
