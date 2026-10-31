import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeCertification
import H0mework.Versions.R2.Foundation.Inquiry.Protocol

/-! Inquiry coordinates are formed before the original programme emitter.
The answer is its actual interpreter result, and every token keeps the
same inherited responsibility row and emitted occurrence. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeLiving

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program ProgrammeWorld ProgrammeSource ProgrammeCertification

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : Input Party Good Port Technology Instrument)

structure ExecutionFaceAt {current : (V input).Current}
    (_occurrence : (ProgrammeSource.source input).toRootSource.actual.OccurrenceAt current) where
  before : RawCurrent Party Good Technology Instrument
  submitted : RawEvent Party Good Port Technology Instrument
  interpreted : ExecutionResult Party Good Port Technology Instrument
  after : RawCurrent Party Good Technology Instrument
  before_exact : before = rawCurrent input current
  submitted_exact : submitted = rawEvent input current
  interpreted_exact : interpreted = input.law.execute before 0 submitted
  after_exact : after = input.law.next before submitted
  root_next_exact : after = rawCurrent input (next input current)

def executionFace {current : (V input).Current}
    (occurrence : (ProgrammeSource.source input).toRootSource.actual.OccurrenceAt current) :
    ExecutionFaceAt input occurrence where
  before := rawCurrent input current
  submitted := rawEvent input current
  interpreted := input.law.execute (rawCurrent input current) 0 (rawEvent input current)
  after := input.law.next (rawCurrent input current) (rawEvent input current)
  before_exact := rfl
  submitted_exact := rfl
  interpreted_exact := rfl
  after_exact := rfl
  root_next_exact := (actual_raw_next input current).symm

def inquiryEntrySupport (support : (N input).Support) : OpenResponsibilityAt (N input) support := by
  cases support <;> exact ⟨.inherited, ()⟩

def inquiryEntryAt {current : (V input).Current}
    (occurrence : (ProgrammeSource.source input).toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt (N input) occurrence.1 := inquiryEntrySupport input occurrence.1

def inquiryU7 : U7ProducerCalculus (N input) where
  DemandAt := fun _ => PUnit
  generateDemand := fun _ => PUnit.unit

def inquiryU7Source : U7ActualSuccessorSource (N input) (inquiryU7 input) where
  EventAt := SourceGeneratedU7DemandAt (inquiryU7 input)
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := id
  demandEntryAt := fun {support} {_obstruction} {_demand} _event => inquiryEntrySupport input support

def inquiryCalculus : U7ObstructionEvolutionCalculus (N input) (inquiryU7 input) where
  source := inquiryU7Source input
  compile := fun {support} {obstruction} {_demand} _event => {
    disposition := .redirected (successor := obstruction)
      ⟨ProgrammeWorld.transferReceipt (observation? input) support, rfl⟩
    demandEntryDisposition := ⟨.transferred
      (ProgrammeWorld.transferReceipt (observation? input) support) rfl rfl (Nat.le_refl _), rfl⟩ }

def inquiryAudit {current : (V input).Current}
    (occurrence : (ProgrammeSource.source input).toRootSource.actual.OccurrenceAt current) :
    SourceNativeInquiryFrontAuditAt (inquiryU7 input) (inquiryCalculus input)
      (TheoryState.rootSemantic (N input)) occurrence.1 := .answered

theorem inquiryEntry_emitted (current : (V input).Current) :
    inquiryEntryAt input (emitted input current) = sourceEntry input current .inherited := by
  cases current <;> rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeLiving
