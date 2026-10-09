import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Current
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldPresentation.Mouths

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace CPS1ReactiveFieldDynamics
noncomputable section
variable {frame : CPS1Recycling.Frame}
namespace Presentation
abbrev FP := CPS1ReactiveField.FinitePresentation.Snapshot

structure Pulse (frame : CPS1Recycling.Frame) where
  before : CPS1ReactiveField.FinitePresentation.Active frame
  index : Nat
  after : CPS1ReactiveField.FinitePresentation.Active frame

def pulse (source : CPS1ReactiveFieldDynamics.Pulse frame) : Pulse frame :=
  ⟨CPS1ReactiveField.FinitePresentation.active source.before,source.index,
    CPS1ReactiveField.FinitePresentation.active source.after⟩

def Pulse.NativeValid (view : Pulse frame) : Prop :=
  ∃ source : CPS1ReactiveFieldDynamics.Pulse frame, view = pulse source ∧ source.Valid

structure Whole (frame : CPS1Recycling.Frame) where
  cursor : CPS1ReactiveField.FinitePresentation.Cursor frame
  pulses : List (Pulse frame)
  remaining : Nat
  failure : Option Failure

/-- Read the already-generated native object once. This presentation has no
unpacking operation and cannot regenerate a different source or occupation. -/
def whole (source : Run frame) : Whole frame :=
  ⟨CPS1ReactiveField.FinitePresentation.cursor source.cursor,source.pulses.map pulse,
    source.remaining,source.failure⟩

theorem pulse_exact (source : CPS1ReactiveFieldDynamics.Pulse frame) :
    (pulse source).before = CPS1ReactiveField.FinitePresentation.active source.before ∧
    (pulse source).index = source.index ∧
    (pulse source).after = CPS1ReactiveField.FinitePresentation.active source.after ∧
    type_of% (CPS1ReactiveField.FinitePresentation.active_exact source.before) ∧
    type_of% (CPS1ReactiveField.FinitePresentation.active_exact source.after) :=
  ⟨rfl,rfl,rfl,CPS1ReactiveField.FinitePresentation.active_exact _,
    CPS1ReactiveField.FinitePresentation.active_exact _⟩

theorem whole_exact (source : Run frame) :
    (whole source).cursor = CPS1ReactiveField.FinitePresentation.cursor source.cursor ∧
    (whole source).pulses = source.pulses.map pulse ∧
    (whole source).remaining = source.remaining ∧ (whole source).failure = source.failure ∧
    type_of% (CPS1ReactiveField.FinitePresentation.cursor_exact source.cursor) :=
  ⟨rfl,rfl,rfl,rfl,CPS1ReactiveField.FinitePresentation.cursor_exact _⟩

def renewWhole (current : NativeCursor frame) (depth : Nat) : Whole frame := whole (renew current depth)
def continueWhole (current : NativeCursor frame) (depth : Nat)
    (inputs : List CPS1ReactiveField.Carried.Input) : Whole frame :=
  whole (continueChemical current depth inputs)

theorem renew_whole_native (current : NativeCursor frame) (depth : Nat) :
    (renewWhole current depth).cursor.current = current.current ∧
    (renewWhole current depth).cursor.stages =
      current.stages.map CPS1ReactiveField.FinitePresentation.stage ∧
    ∀ entry ∈ (renewWhole current depth).pulses, entry.NativeValid := by
  obtain ⟨same,stages,valid⟩ := CPS1ReactiveFieldDynamics.renew_whole current depth
  refine ⟨same,congrArg (List.map CPS1ReactiveField.FinitePresentation.stage) stages,?_⟩
  intro entry held
  rcases List.mem_map.mp held with ⟨native,member,rfl⟩
  exact ⟨native,rfl,valid native member⟩

theorem renew_whole_ready (current : NativeCursor frame) (depth : Nat) (ready : Ready current) :
    (renewWhole current depth).remaining = 0 ∧ (renewWhole current depth).failure = none ∧
    (renewWhole current depth).pulses.length = depth := by
  have paid := renew_ready current depth ready
  exact ⟨paid.1,paid.2.1,by simpa only [renewWhole,whole,List.length_map] using paid.2.2.1⟩

theorem native_pulse_paid (view : Pulse frame) (valid : view.NativeValid) :
    0 < dyadicTime view.index ∧ 0 < view.after.fields.reserve ∧
    view.after.fields.account = view.before.fields.account ∧
    view.after.fields.electronCount = view.before.fields.electronCount ∧
    view.after.body = view.before.body ∧ view.after.source = view.before.source ∧
    view.after.fields.nuclei = view.before.fields.nuclei ∧
    view.after.fields.waterOrigins = view.before.fields.waterOrigins := by
  obtain ⟨native,rfl,valid⟩ := valid
  have paid := CPS1ReactiveFieldDynamics.pulse_paid native valid
  exact ⟨paid.1,paid.2.1,paid.2.2.1,paid.2.2.2.1,valid.2.2.2.1,valid.2.2.1,
    paid.2.2.2.2.1,paid.2.2.2.2.2⟩

end Presentation

open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

def fromSourceNative (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
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
    (pulseDepth : Nat) : Option (Σ frame : CPS1Recycling.Frame, Run frame) :=
  (CPS1ReactiveField.Carried.fromSource edits water additional path recycleFeed scanFeed bodyFeed depth
    oldActions bathActions bathFeed electronicActions electronicFeed nuclearActions nuclearFeed
    followingActions followingFeed molecularActions molecularFeed deformationActions deformationFeed actions feed raw).map
      (fun source => ⟨source.1,renew source.2 pulseDepth⟩)

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
    (feed : List CPS1LocalChemicalExecution.Source.RawMaterial) (raw : List CPS1AddressedReactiveJoint.Rows.RawAction)
    (pulseDepth : Nat) : Option (Σ frame : CPS1Recycling.Frame, Presentation.Whole frame) :=
  (fromSourceNative edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
    electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions
    molecularFeed deformationActions deformationFeed actions feed raw pulseDepth).map
      (fun source => ⟨source.1,Presentation.whole source.2⟩)

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
    (pulseDepth : Nat) (inputs : List CPS1ReactiveField.Carried.Input) :
    Option (Σ frame : CPS1Recycling.Frame, Presentation.Whole frame) :=
  (fromSourceNative edits water additional path recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed
    electronicActions electronicFeed nuclearActions nuclearFeed followingActions followingFeed molecularActions
    molecularFeed deformationActions deformationFeed actions feed raw pulseDepth).map (fun source =>
      ⟨source.1,Presentation.whole {source.2 with
        cursor := CPS1ReactiveField.Carried.advanceAll source.2.cursor inputs}⟩)

end
end CPS1ReactiveFieldDynamics
