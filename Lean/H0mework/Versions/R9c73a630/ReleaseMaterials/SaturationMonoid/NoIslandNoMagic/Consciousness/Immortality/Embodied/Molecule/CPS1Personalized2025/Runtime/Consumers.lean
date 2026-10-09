import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Runtime.Facade
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeRootNextLaw

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Root
open CPS1MaterialIncidence.NativeRootDataProbe
noncomputable section

attribute [local irreducible] InputBodyAt generated_input source_input_body input_body_next


def readInputs (runtime : LivingRuntimeState process) : InputMaterial :=
  match facade.readoutAt runtime .inputs with
  | .inl ⟨_,payload⟩ => payload.2.2 | .inr impossible => PEmpty.elim impossible
def readSequence (runtime : LivingRuntimeState process) : SequenceMaterial :=
  match facade.readoutAt runtime .sequence with
  | .inl ⟨_,payload⟩ => payload.2 | .inr impossible => PEmpty.elim impossible
def readExperiment (runtime : LivingRuntimeState process) : ExperimentMaterial :=
  match facade.readoutAt runtime .experiment with
  | .inl ⟨_,payload⟩ => payload.2 | .inr impossible => PEmpty.elim impossible
def readResponse (runtime : LivingRuntimeState process) : ResponseMaterial :=
  match facade.readoutAt runtime .response with
  | .inl ⟨_,payload⟩ => payload.2 | .inr impossible => PEmpty.elim impossible
theorem readCertificate (runtime : LivingRuntimeState process) : OriginalProgramClosure :=
  match facade.readoutAt runtime .certificate with
  | .inl ⟨_,payload⟩ => payload.down | .inr impossible => PEmpty.elim impossible

theorem actualOperation (runtime : LivingRuntimeState process) : OperationAt (Native.erase runtime.current.visit.current) :=
  runtime.emittedOccurrence.2.operation

/-- Both time positions are restrictions of the original installed inputs
payload, tied to its same source occurrence. -/
def readNativeMaterial (runtime : LivingRuntimeState process) : NativeInputMaterial runtime.emittedOccurrence :=
  match facade.readoutAt runtime .inputs with
  | .inl ⟨_,payload⟩ => payload.2.1
  | .inr impossible => nomatch impossible

def readNativeWrite (runtime : LivingRuntimeState process) : Native.Write runtime.current.visit.current :=
  (readNativeMaterial runtime).write

def readNativeBody (runtime : LivingRuntimeState process) : InputBodyAt runtime.current.visit.current.input :=
  (readNativeMaterial runtime).sourceBody

def readWrittenNativeBody (runtime : LivingRuntimeState process) : InputBodyAt runtime.current.visit.current.input :=
  (readNativeWrite runtime).body

theorem installed_native_write_actual (runtime : LivingRuntimeState process) :
    readNativeWrite runtime = runtime.emittedOccurrence.2 := (readNativeMaterial runtime).writeActual

theorem installed_native_body_actual (runtime : LivingRuntimeState process) :
    readNativeBody runtime = runtime.current.visit.current.body := (readNativeMaterial runtime).sourceActual

theorem installed_written_body_actual (runtime : LivingRuntimeState process) :
    readWrittenNativeBody runtime = input_body_next runtime.current.visit.current.input (readNativeBody runtime) := by
  exact (readNativeWrite runtime).actual.trans
    (congrArg (input_body_next runtime.current.visit.current.input) (installed_native_body_actual runtime).symm)

theorem literal_next_consumes_installed_body (runtime : LivingRuntimeState process) :
    runtime.tick.next.current.visit.current = Native.next runtime.current.visit.current ∧
      readNativeBody runtime.tick.next = readWrittenNativeBody runtime ∧
      runtime.tick.next.current.visit.current.input = runtime.current.visit.current.input := ⟨rfl,rfl,rfl⟩

theorem literal_native_body_next (runtime : LivingRuntimeState process) :
    readNativeBody runtime.tick.next =
      input_body_next runtime.current.visit.current.input (readNativeBody runtime) :=
  (literal_next_consumes_installed_body runtime).2.1.trans (installed_written_body_actual runtime)

theorem second_literal_next_consumes_previous_body (runtime : LivingRuntimeState process) :
    readNativeBody runtime.tick.next.tick.next =
      input_body_next runtime.current.visit.current.input
        (input_body_next runtime.current.visit.current.input (readNativeBody runtime)) := by
  exact (literal_native_body_next runtime.tick.next).trans
    (congrArg (input_body_next runtime.current.visit.current.input) (literal_native_body_next runtime))

theorem installed_native_body_and_two_writes (runtime : LivingRuntimeState process) :
    (type_of% (face_factorizes runtime .inputs)) ∧
      InputWriteLaw runtime.current.visit.current.input (readNativeBody runtime) ∧
      InputWriteLaw runtime.current.visit.current.input (readWrittenNativeBody runtime) :=
  ⟨face_factorizes runtime .inputs,input_write_law _ _,input_write_law _ _⟩

theorem erased_phase_next_commutes (runtime : LivingRuntimeState process) :
    Native.erase runtime.tick.next.current.visit.current = Root.nextCurrent (Native.erase runtime.current.visit.current) := rfl

theorem wrong_source_body_rejected (runtime : LivingRuntimeState process)
    (replacement : InputBodyAt runtime.current.visit.current.input)
    (wrong : replacement ≠ readNativeBody runtime) :
    ¬ ∃ material : NativeInputMaterial runtime.emittedOccurrence, material.sourceBody = replacement := by
  rintro ⟨material,selected⟩
  exact wrong (selected.symm.trans (material.sourceActual.trans (installed_native_body_actual runtime).symm))

theorem wrong_source_written_body_rejected (runtime : LivingRuntimeState process)
    (replacement : InputBodyAt runtime.current.visit.current.input)
    (wrong : replacement ≠ readWrittenNativeBody runtime) :
    ¬ ∃ event : eventLaw.EventAt runtime.current.visit.current (), event.body = replacement := by
  rintro ⟨event,selected⟩
  exact wrong (selected.symm.trans (event.actual.trans (readNativeWrite runtime).actual.symm))

theorem all_materials_from_same_installed_occurrence (runtime : LivingRuntimeState process) :
    (∀ face, type_of% (face_factorizes runtime face)) ∧
    readInputs runtime = generatedInputMaterial ∧ readSequence runtime = generatedSequenceMaterial ∧
    readExperiment runtime = generatedExperimentMaterial ∧ readResponse runtime = generatedResponseMaterial :=
  ⟨face_factorizes runtime,rfl,rfl,rfl,rfl⟩

theorem first_next_consumes_whole_program :
    (readSequence afterFirst).intendedRepair = Source.genomic ∧
    Coding.translate Coding.code (readSequence afterFirst).editorCoding =
      some ((readSequence afterFirst).editorProtein.map String.singleton) ∧
    (readSequence afterFirst).guide.sulfurAfter = [1,2,3,97,98,99] ∧
    (readSequence afterFirst).firstStop ⟨false,true,false⟩ = some (Source.referenceProtein ++ ["*"]) :=
  ⟨(readCertificate afterFirst).sourceCorrection.2.1,
    (readCertificate afterFirst).editorTranslation.1,
    (readCertificate afterFirst).chemicalInventory.2.2.2.1,
    (readCertificate afterFirst).allFirstStops false true false⟩

theorem second_next_consumes_independent_response :
    (readExperiment afterSecond).rows = Source.assays ∧
    (readResponse afterSecond).assayNet 0 = none ∧
    (readResponse afterSecond).assayNet 10 = some (113/300) ∧
    (readResponse afterSecond).secondInfusion.patient = Source.clinical.patient ∧
    (readResponse afterSecond).secondInfusion.day = 230 ∧
    (readResponse afterSecond).originalFirstTaper = [101/10,81/10,101/10] ∧
    (readResponse afterSecond).finalMedication = 5 := by
  exact ⟨rfl,(readCertificate afterSecond).missingAssay.2.2.2.1,
    (readCertificate afterSecond).offTargetResponse.2.2.2.1,
    rfl,(readCertificate afterSecond).actualRedose.2.2.2.1,
    (readCertificate afterSecond).taperHistory.1,by decide +kernel⟩

structure InstalledOriginalProgramClosure : Prop where
  source : OriginalProgramClosure
  firstOperation : OperationAt (Native.erase seed.current.visit.current)
  nextOperation : OperationAt (Native.erase afterFirst.current.visit.current)
  consumerOperation : OperationAt (Native.erase afterSecond.current.visit.current)
  seedOrigin : seed = LivingRuntimeState.initial process
  firstNext : afterFirst = seed.tick.next
  secondNext : afterSecond = afterFirst.tick.next
  currents : type_of% actual_analysis_currents
  sourceLedger : type_of% original_source_ledger_and_identity
  allFaces : ∀ runtime face, type_of% (face_factorizes runtime face)
  materials : type_of% all_materials_from_same_installed_occurrence
  firstConsumer : type_of% first_next_consumes_whole_program
  secondConsumer : type_of% second_next_consumes_independent_response
  generatedNext : type_of% same_source_generated_next

theorem sourceGeneratedCPS1ProgramAndClinicalAtNext : InstalledOriginalProgramClosure :=
  ⟨readCertificate afterSecond,actualOperation seed,actualOperation afterFirst,actualOperation afterSecond,
    rfl,rfl,rfl,actual_analysis_currents,original_source_ledger_and_identity,face_factorizes,
    all_materials_from_same_installed_occurrence,first_next_consumes_whole_program,
    second_next_consumes_independent_response,same_source_generated_next⟩
end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Runtime
