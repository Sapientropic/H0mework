import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Compiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Injective

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open DebtActivationWorld DebtActivationLedger

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : NativeFrame input) {origin : frame.V.Current}
  (registered : Registration input frame origin)

theorem openAt_subsingleton (support : (N input frame registered).Support)
    (responsibility : (N input frame registered).Responsibility) :
    Subsingleton ((N input frame registered).OpenAt support responsibility) := by
  rcases support with ⟨base, active⟩
  cases responsibility with
  | inl old => exact frame.openAt_subsingleton base old
  | inr debt =>
      cases active <;> dsimp only [N, ExtendedNetwork, extendedNetwork, DebtOpenAt] <;> infer_instance

noncomputable def restructuringLaw : SourceNativeLedgerRestructuringLaw (source input frame registered) :=
  identityOnlyWorldLedgerRestructuringLaw (source input frame registered)
    ((N input frame registered).anchorAt (supportAt input frame registered (initial input frame registered)))
    (openAt_subsingleton input frame registered)

noncomputable def restructuringCertification {current : Current input frame registered}
    (occurrence : (source input frame registered).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt (restructuringLaw input frame registered)
      ((ledgerCompiler input frame registered).compile occurrence) := by
  cases occurrence_eq_emitted input frame registered occurrence
  apply ExactLedgerRestructuringCertificationAt.ofInjective
  · change Function.Injective (fun entry =>
      ((patch input frame registered current).toLedgerWriteEvolution.origin entry).1)
    rw [patch_origin]
    exact (whole_injective input frame registered current).1
  · change Function.Injective (fun entry =>
      ((patch input frame registered current).toLedgerWriteEvolution.destination entry).1)
    rw [patch_destination]
    exact (whole_injective input frame registered current).2

noncomputable def restructuringSource : SourceNativeRestructuringLedgerSource (N input frame registered) (V input frame registered) where
  source := source input frame registered
  compiler := {
    ledgerCompiler := ledgerCompiler input frame registered
    restructuringLaw := restructuringLaw input frame registered
    certifyRestructuring := restructuringCertification input frame registered }

def entrySupport (support : (N input frame registered).Support) : OpenResponsibilityAt (N input frame registered) support :=
  oldEntry (state? := support.2) (frame.entrySupport support.1)

def disposition (support : (N input frame registered).Support) :
    (kind : WorldDispositionKind) → (N input frame registered).DispositionAt support kind
  | .supportSettlement => frame.disposition support.1 .supportSettlement
  | .transfer => .inl (frame.disposition support.1 .transfer)
  | .lawSurfaceExtension => .inl (frame.disposition support.1 .lawSurfaceExtension)

def inquiryEntryAt {current : Current input frame registered}
    (occurrence : (source input frame registered).toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt (N input frame registered) occurrence.1 := entrySupport input frame registered occurrence.1

def inquiryU7 : U7ProducerCalculus (N input frame registered) where
  DemandAt := fun _ => PUnit
  generateDemand := fun _ => PUnit.unit

def inquiryU7Source : U7ActualSuccessorSource (N input frame registered) (inquiryU7 input frame registered) where
  EventAt := SourceGeneratedU7DemandAt (inquiryU7 input frame registered)
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := id
  demandEntryAt := fun {support} {_} {_} _ => entrySupport input frame registered support

def inquiryCalculus : U7ObstructionEvolutionCalculus (N input frame registered) (inquiryU7 input frame registered) where
  source := inquiryU7Source input frame registered
  compile := fun {support} {obstruction} {_} _ => {
    disposition := .redirected (successor := obstruction) ⟨disposition input frame registered support _, rfl⟩
    demandEntryDisposition := ⟨.transferred (disposition input frame registered support _) rfl rfl (Nat.le_refl _), rfl⟩ }

def inquiryAudit {current : Current input frame registered}
    (occurrence : (source input frame registered).toRootSource.actual.OccurrenceAt current) :
    SourceNativeInquiryFrontAuditAt (inquiryU7 input frame registered) (inquiryCalculus input frame registered)
      (TheoryState.rootSemantic (N input frame registered)) occurrence.1 := .answered

def IsIssue (current : Current input frame registered) : Prop :=
  match Cursor.action input (frame.cursor current.1) with
  | .issue _ => True
  | _ => False

instance (current : Current input frame registered) : Decidable (IsIssue input frame registered current) := by
  unfold IsIssue
  cases Cursor.action input (frame.cursor current.1) <;> infer_instance

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission
