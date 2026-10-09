import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveField.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Source

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CPS1ReactiveField
noncomputable section
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
variable {frame : CPS1Recycling.Frame}

structure Occurrence (frame : CPS1Recycling.Frame) where
  old : CPS1Deformation.Source.Occurrence frame
  ingress : CPS1AddressedReactiveJoint.Occurrence frame

def editingSource (old : CPS1Deformation.Source.Occurrence frame) :
    CPS1EditingChemicalJoin.Source.Occurrence frame :=
  old.previous.previous.previous.previous.previous.previous.previous.previous

def atomicSource (old : CPS1Deformation.Source.Occurrence frame) :
    CPS1AtomicSource.Current.Occurrence frame :=
  old.previous.previous.previous.previous.previous.previous.previous

def heldDeformed (stock : CPS1Deformation.Stock frame) : Option (CPS1Deformation.Material frame) :=
  List.rec none (fun species _ tail => match species with
    | .deformed state => some state | _ => tail) stock

def enzymeView (old : CPS1Deformation.Source.Occurrence frame) : CPS1LocalChemicalExecution.Stock frame :=
  match heldDeformed old.current.stock with
  | none => []
  | some state => [.chain state.currentJoint.originBody.source]

/-- The chain is a restriction of the live physical carrier selected here. Its
old deformed token is removed from the new live inventory, not counted twice. -/
def freshIngress (old : CPS1Deformation.Source.Occurrence frame) :
    CPS1LocalChemicalExecution.Source.Occurrence frame :=
  {(editingSource old).previous with current := ⟨enzymeView old,[],[],[],none⟩}

def legacyAddress (count : Nat) : CPS1AtomicDynamics.Charged.Address →
    Option CPS1AddressedReactiveJoint.Address
  | .nucleus slot => if slot < count then some (.nucleus (.old slot)) else none
  | .electron slot orbital => if slot < count then some (.electron (.old slot) orbital) else none

def legacyRows (old : CPS1Deformation.Source.Occurrence frame) : CPS1AddressedReactiveJoint.Rows.Stock :=
  match heldDeformed old.current.stock with
  | none => []
  | some state => state.currentJoint.rows.filterMap (fun item =>
      (legacyAddress (CPS1AtomicSource.Graph.fromChain frame state.currentJoint.originBody.source).atoms.length
        item.1).map (fun address => (address,item.2)))

def start (old : CPS1Deformation.Source.Occurrence frame) : Occurrence frame :=
  ⟨old,{CPS1AddressedReactiveJoint.start
    (CPS1AddressedChemicalReaction.Source.start (freshIngress old)) with measurements := ⟨legacyRows old,0⟩}⟩

inductive LiveMaterial (frame : CPS1Recycling.Frame)
  | old (species : CPS1Deformation.Species frame)
  | reactive (material : CPS1AddressedChemicalReaction.Source.LocalMaterial frame)

def oldResidual (current : Occurrence frame) : CPS1Deformation.Stock frame :=
  match heldDeformed current.old.current.stock with
  | none => current.old.current.stock
  | some state => current.old.current.stock.erase (.deformed state)

def liveStock (current : Occurrence frame) : List (LiveMaterial frame) :=
  (oldResidual current).map LiveMaterial.old ++ current.ingress.atomic.source.stock.map LiveMaterial.reactive

theorem start_enzyme_identity (old : CPS1Deformation.Source.Occurrence frame)
    (state : CPS1Deformation.Material frame) (selected : heldDeformed old.current.stock = some state) :
    (start old).ingress.atomic.source.stock =
      [.inherited (.chain state.currentJoint.originBody.source)] := by
  simp only [start,CPS1AddressedReactiveJoint.start,CPS1AddressedHydrolysis.Atomic.start,
    CPS1AddressedChemicalReaction.Source.start,freshIngress,enzymeView,selected,List.map_cons,List.map_nil]

theorem legacy_row_source (old : CPS1Deformation.Source.Occurrence frame)
    (state : CPS1Deformation.Material frame) (selected : heldDeformed old.current.stock = some state)
    (address : CPS1AddressedReactiveJoint.Address) (row : CPS1AtomicDynamics.Body.Row)
    (member : (address,row) ∈ legacyRows old) :
    ∃ native, (native,row) ∈ state.currentJoint.rows ∧
      legacyAddress (CPS1AtomicSource.Graph.fromChain frame state.currentJoint.originBody.source).atoms.length
        native = some address := by
  simp only [legacyRows,selected] at member
  rcases List.mem_filterMap.mp member with ⟨item,held,mapped⟩
  cases actual : legacyAddress _ item.1 with
  | none => rw [actual] at mapped; cases mapped
  | some generated =>
    simp only [actual,Option.map_some,Option.some.injEq,Prod.mk.injEq] at mapped
    exact ⟨item.1,mapped.2 ▸ held,mapped.1 ▸ actual⟩

def next (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) : Occurrence frame :=
  {current with ingress := CPS1AddressedReactiveJoint.next current.ingress actions feed raw}

theorem source_whole (current : Occurrence frame)
    (actions : List CPS1LocalChemicalExecution.Source.LocalAction)
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial)
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) :
    (next current actions feed raw).old = current.old ∧
    (next current actions feed raw).old.current.stock = current.old.current.stock ∧
    (next current actions feed raw).old.current.pending = current.old.current.pending ∧
    (next current actions feed raw).old.current.stages = current.old.current.stages ∧
    type_of% (CPS1AddressedReactiveJoint.source_generated_reactive_next current.ingress actions feed raw) :=
  ⟨rfl,rfl,rfl,rfl,CPS1AddressedReactiveJoint.source_generated_reactive_next current.ingress actions feed raw⟩

theorem held_deformed_member (stock : CPS1Deformation.Stock frame)
    (state : CPS1Deformation.Material frame) (actual : heldDeformed stock = some state) :
    CPS1Deformation.Species.deformed state ∈ stock := by
  induction stock with
  | nil => cases actual
  | cons species rest ih =>
    cases species <;> first
    | exact List.mem_cons_of_mem _ (ih actual)
    | simp only [heldDeformed,Option.some.injEq] at actual
      cases actual
      exact List.mem_cons_self

inductive InletFailure
  | missingOldCarrier
  | oldOccupiedNotOrthonormal
  | raw (failure : CPS1AddressedReactiveJoint.Rows.Failure)

structure Inlet (current : Occurrence frame) where
  old : CPS1Deformation.Material frame
  held : CPS1Deformation.Species.deformed old ∈ current.old.current.stock
  good : CPS1Deformation.Good old
  body : CPS1AddressedReactiveJoint.Body frame
  actual : CPS1AddressedReactiveJoint.admission current.ingress = .ok body

def inlet (current : Occurrence frame) : Except InletFailure (Inlet current) := by
  classical
  exact match selected : heldDeformed current.old.current.stock with
    | none => .error .missingOldCarrier
    | some old => if good : CPS1Deformation.Good old then
        match actual : CPS1AddressedReactiveJoint.admission current.ingress with
        | .error failure => .error (.raw failure)
        | .ok body => .ok ⟨old,held_deformed_member _ _ selected,good,body,actual⟩
      else .error .oldOccupiedNotOrthonormal

abbrev OldElectronIndex {current : Occurrence frame} (source : Inlet current) :=
  CPS1ElectronicSource.ElectronIndex source.old.reference.geometry

def Inlet.oldFields {current : Occurrence frame} (source : Inlet current) :
    OldElectronIndex source → CPS1ElectronicSource.SpinSpace := source.old.currentFields

theorem inlet_old_fields {current : Occurrence frame} (source : Inlet current) :
    source.oldFields = source.old.currentFields ∧ Orthonormal ℂ source.oldFields := ⟨rfl,source.good⟩

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
    (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) :
    Option (Σ frame : CPS1Recycling.Frame, Occurrence frame) := do
  let old ← CPS1Deformation.Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
    oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
    followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed
  pure ⟨old.1,next (start old.2) actions feed raw⟩

end
end CPS1ReactiveField
