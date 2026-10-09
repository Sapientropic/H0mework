import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldPresentation.Snapshot

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace CPS1ReactiveField.FinitePresentation
noncomputable section
variable {frame : CPS1Recycling.Frame}

structure Active (frame : CPS1Recycling.Frame) where
  source : CPS1ReactiveField.Occurrence frame
  fields : Snapshot
  good : Orthonormal ℂ fields.fields
  body : CPS1AddressedReactiveJoint.Body frame
  actual : CPS1AddressedReactiveJoint.admission source.ingress = .ok body
  paidRawReserve : ℝ

@[reducible] def active (source : Carried.Active frame) : Active frame :=
  ⟨source.source,snapshot source.fields,good_exact source.fields source.good,
    source.body,source.actual,source.paidRawReserve⟩

structure Stage (frame : CPS1Recycling.Frame) where
  source : CPS1ReactiveField.Occurrence frame
  before : Option (Active frame)
  result : Except (Carried.Failure frame) (Active frame)

def stage (source : Carried.Stage frame) : Stage frame :=
  ⟨source.source,source.before.map active,match source.result with
    | .error failure => .error failure | .ok next => .ok (active next)⟩

def Stage.NativeValid (view : Stage frame) : Prop :=
  ∃ source : Carried.Stage frame, view = stage source ∧ source.Valid

structure Cursor (frame : CPS1Recycling.Frame) where
  current : CPS1ReactiveField.Occurrence frame
  active : Option (Active frame)
  stages : List (Stage frame)

def cursor (source : Carried.Cursor frame) : Cursor frame :=
  ⟨source.current,source.active.map active,source.stages.map stage⟩

theorem active_exact (source : Carried.Active frame) :
    (active source).source = source.source ∧ (active source).body = source.body ∧
    (active source).paidRawReserve = source.paidRawReserve ∧
    (active source).fields = snapshot source.fields ∧
    type_of% (accounts_exact source.fields) ∧ type_of% (Carried.active_whole source) :=
  ⟨rfl,rfl,rfl,rfl,accounts_exact source.fields,Carried.active_whole source⟩

theorem cursor_exact (source : Carried.Cursor frame) :
    (cursor source).current = source.current ∧ (cursor source).active = source.active.map active ∧
    (cursor source).stages = source.stages.map stage ∧ (cursor source).stages.length = source.stages.length := by
  exact ⟨rfl,rfl,rfl,by simp only [cursor,List.length_map]⟩

theorem stage_error (source : Carried.Stage frame) (failure : Carried.Failure frame)
    (actual : source.result = .error failure) : (stage source).result = .error failure := by
  simp only [stage,actual]

theorem stage_ok (source : Carried.Stage frame) (next : Carried.Active frame)
    (actual : source.result = .ok next) : (stage source).result = .ok (active next) := by
  simp only [stage,actual]

theorem finite_source (source : Carried.Cursor frame) (inputs : List Carried.Input) :
    (cursor (Carried.advanceAll source inputs)).current.ingress.atomic =
      CPS1AddressedHydrolysis.Atomic.advanceAll source.current.ingress.atomic (inputs.map Prod.fst) :=
  Carried.advance_all_source source inputs

theorem finite_stages (source : Carried.Cursor frame) (inputs : List Carried.Input) :
    ∃ generated : List (Carried.Stage frame),
      (cursor (Carried.advanceAll source inputs)).stages = (cursor source).stages ++ generated.map stage ∧
      ∀ entry ∈ generated, entry.Valid := by
  obtain ⟨generated,whole,valid⟩ := Carried.advance_all_generated_stages source inputs
  exact ⟨generated,by simp only [cursor,whole,List.map_append],valid⟩

theorem initial_stages_valid (source : CPS1ReactiveField.Occurrence frame) :
    ∀ entry ∈ (Carried.startCursor source).stages, entry.Valid := by
  intro entry member
  have same : entry = ⟨source,none,Carried.activate source⟩ := by
    simpa only [Carried.startCursor,List.mem_singleton] using member
  subst entry
  rfl

theorem complete_generated_stages (source : CPS1ReactiveField.Occurrence frame) (inputs : List Carried.Input) :
    ∀ entry ∈ (cursor (Carried.advanceAll (Carried.startCursor source) inputs)).stages, entry.NativeValid := by
  obtain ⟨generated,whole,valid⟩ := Carried.advance_all_generated_stages (Carried.startCursor source) inputs
  intro entry member
  rcases List.mem_map.mp member with ⟨native,held,rfl⟩
  refine ⟨native,rfl,?_⟩
  rw [whole] at held
  rcases List.mem_append.mp held with old | new
  · exact initial_stages_valid source native old
  · exact valid native new

theorem valid_activation (source : Carried.Stage frame) (next : Carried.Active frame)
    (valid : source.Valid) (initial : source.before = none) (actual : source.result = .ok next) :
    type_of% (Carried.activate_generated source.source next (by
      have paid : Carried.activate source.source = .ok next := by simpa only [Carried.Stage.Valid,initial] using valid.symm.trans actual
      exact paid)) := by
  have paid : Carried.activate source.source = .ok next := by simpa only [Carried.Stage.Valid,initial] using valid.symm.trans actual
  exact Carried.activate_generated source.source next paid

theorem valid_advance (source : Carried.Stage frame) (old next : Carried.Active frame)
    (valid : source.Valid) (before : source.before = some old) (actual : source.result = .ok next) :
    type_of% (Carried.advance_generated old source.source next (by
      have paid : Carried.advance old source.source = .ok next := by simpa only [Carried.Stage.Valid,before] using valid.symm.trans actual
      exact paid)) := by
  have paid : Carried.advance old source.source = .ok next := by simpa only [Carried.Stage.Valid,before] using valid.symm.trans actual
  exact Carried.advance_generated old source.source next paid

open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

def fromSourceWhole (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
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
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) (raw : List CPS1AddressedReactiveJoint.Rows.RawAction) :
    Option (Σ frame : CPS1Recycling.Frame, Cursor frame) :=
  (Carried.fromSource edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
    electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions
    molecularFeed deformationActions deformationFeed actions feed raw).map (fun source => ⟨source.1,cursor source.2⟩)

def advanceFromSourceWhole (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
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
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) (raw : List CPS1AddressedReactiveJoint.Rows.RawAction)
    (inputs : List Carried.Input) : Option (Σ frame : CPS1Recycling.Frame, Cursor frame) :=
  (Carried.fromSource edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
    electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions
    molecularFeed deformationActions deformationFeed actions feed raw).map
      (fun source => ⟨source.1,cursor (Carried.advanceAll source.2 inputs)⟩)

end
end CPS1ReactiveField.FinitePresentation
