import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery.Installation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

open CPS1MaterialIncidence.NativeRootDataProbe
attribute [local irreducible] InputBodyAt generated_input source_input_body input_body_next

def process : SourceNativeLivingRootProcess ParentN where
  State := Supply.process.State
  stateAt := fun visit => ⟨ParentV,livingRoot,.finite visit⟩
  stateAt_injective := by
    intro left right equality
    change (⟨ParentV,livingRoot,.finite left⟩ : SourceNativeLivingRootCurrentAt ParentN) =
      ⟨ParentV,livingRoot,.finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := Supply.process.initial
  successorAt := by
    intro visit
    refine ⟨Supply.process.successor visit,?_,?_⟩
    · rcases visit with ⟨current,history⟩; rfl
    · rcases visit with ⟨current,history⟩; exact HEq.rfl

/-- Thirteen faces: the five root faces, the two Ngs faces, the two
Longitudinal faces and the two Supply faces are inherited, and this module
installs its own material/certificate coface. -/
abbrev Face := SourceNativeProjectionCoface Supply.Face Projection

def facade : SourceNativeLivingRuntimeFacade ParentN where
  process := process
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .component _ => projectionLaw | .inherited _ => ParentBase.projectionLaw
  installationAt := fun _ face => match face with
    | .component _ => componentInstallation | .inherited _ => inheritedInstallation
  projectionAt := fun _ face => match face with
    | .component face => face | .inherited face => face

def seed : LivingRuntimeState process := facade.seed

/-- Five ticks: the parent Ngs analysis occupied ticks one and two (its own
`atParent`) plus its literal next, the Longitudinal analysis the third tick
plus its literal next, and the Supply analysis the fourth tick plus its
literal next; this module's `atParent` is the fifth analysis current, i.e.
exactly the parent runtime state. -/
def atParent : LivingRuntimeState process := seed.tick.next.tick.next.tick.next.tick.next.tick.next
def afterParent : LivingRuntimeState process := atParent.tick.next

theorem exact_parent_and_literal_next :
    atParent.state = parentRuntime.state ∧
    atParent.emittedOccurrence = parentRuntime.emittedOccurrence ∧
    afterParent = atParent.tick.next ∧ afterParent.state = parentRuntime.tick.next.state := ⟨rfl,rfl,rfl,rfl⟩

theorem face_factorizes (runtime : LivingRuntimeState process) (face : Face) :
    type_of% (facade.readoutAt_factorizes runtime face) := facade.readoutAt_factorizes runtime face

theorem original_eleven_faces_retained (runtime : LivingRuntimeState process) (face : Supply.Face) :
    facade.readoutAt runtime (.inherited face) = ParentBase.projectionLaw.outcomeAt face runtime.emittedOccurrence := rfl

/-- This is the original Root.inputs address in the same thirteen-face
inventory, inherited through all four material cofaces. -/
def nativeInputsFace : Face := .inherited (.inherited (.inherited (.inherited .inputs)))

def readNativeMaterial (runtime : LivingRuntimeState process) : Root.NativeInputMaterial runtime.emittedOccurrence :=
  match facade.readoutAt runtime nativeInputsFace with
  | .inl ⟨_,payload⟩ => payload.2.1
  | .inr impossible => nomatch impossible

def readNativeBody (runtime : LivingRuntimeState process) : InputBodyAt runtime.current.visit.current.input :=
  (readNativeMaterial runtime).sourceBody

def readNativeWrite (runtime : LivingRuntimeState process) : Root.Native.Write runtime.current.visit.current :=
  (readNativeMaterial runtime).write

def readWrittenNativeBody (runtime : LivingRuntimeState process) : InputBodyAt runtime.current.visit.current.input :=
  (readNativeWrite runtime).body

theorem native_material_source_actual (runtime : LivingRuntimeState process) :
    readNativeBody runtime = runtime.current.visit.current.body := (readNativeMaterial runtime).sourceActual

theorem native_material_write_actual (runtime : LivingRuntimeState process) :
    readNativeWrite runtime = runtime.emittedOccurrence.2 := (readNativeMaterial runtime).writeActual

theorem native_written_body_actual (runtime : LivingRuntimeState process) :
    readWrittenNativeBody runtime = input_body_next runtime.current.visit.current.input (readNativeBody runtime) := by
  exact (readNativeWrite runtime).actual.trans
    (congrArg (input_body_next runtime.current.visit.current.input) (native_material_source_actual runtime).symm)

theorem full_native_current_next (runtime : LivingRuntimeState process) :
    runtime.tick.next.current.visit.current = Root.Native.next runtime.current.visit.current := rfl

theorem literal_native_body_next (runtime : LivingRuntimeState process) :
    readNativeBody runtime.tick.next = input_body_next runtime.current.visit.current.input (readNativeBody runtime) :=
  (show readNativeBody runtime.tick.next = readWrittenNativeBody runtime from rfl).trans
    (native_written_body_actual runtime)

theorem second_literal_native_body_next (runtime : LivingRuntimeState process) :
    readNativeBody runtime.tick.next.tick.next = input_body_next runtime.current.visit.current.input
      (input_body_next runtime.current.visit.current.input (readNativeBody runtime)) :=
  (literal_native_body_next runtime.tick.next).trans
    (congrArg (input_body_next runtime.current.visit.current.input) (literal_native_body_next runtime))

theorem native_material_factorizes (runtime : LivingRuntimeState process) :
    type_of% (facade.readoutAt_factorizes runtime nativeInputsFace) :=
  face_factorizes runtime nativeInputsFace

def readMaterial (runtime : LivingRuntimeState process) : Material :=
  match facade.readoutAt runtime (.component .material) with
  | .inl ⟨_,payload⟩ => payload.2 | .inr impossible => PEmpty.elim impossible

theorem readCertificate (runtime : LivingRuntimeState process) : DeliveryClosure :=
  match facade.readoutAt runtime (.component .certificate) with
  | .inl ⟨_,payload⟩ => payload.down | .inr impossible => PEmpty.elim impossible

theorem inherited_complete_physical_supply (runtime : LivingRuntimeState process) : Supply.PhysicalSupplyClosure :=
  match facade.readoutAt runtime (.inherited (.component .certificate)) with
  | .inl ⟨_,payload⟩ => payload.down | .inr impossible => PEmpty.elim impossible

theorem inherited_complete_longitudinal (runtime : LivingRuntimeState process) : Longitudinal.LongitudinalClosure :=
  match facade.readoutAt runtime (.inherited (.inherited (.component .certificate))) with
  | .inl ⟨_,payload⟩ => payload.down | .inr impossible => PEmpty.elim impossible

theorem inherited_complete_joint_alleles (runtime : LivingRuntimeState process) : Ngs.JointAlleleClosure :=
  match facade.readoutAt runtime (.inherited (.inherited (.inherited (.component .certificate)))) with
  | .inl ⟨_,payload⟩ => payload.down | .inr impossible => PEmpty.elim impossible

theorem inherited_complete_program (runtime : LivingRuntimeState process) : OriginalProgramClosure :=
  match facade.readoutAt runtime (.inherited (.inherited (.inherited (.inherited .certificate)))) with
  | .inl ⟨_,payload⟩ => payload.down | .inr impossible => PEmpty.elim impossible

theorem readMaterial_eq (runtime : LivingRuntimeState process) : readMaterial runtime = material := rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Delivery
