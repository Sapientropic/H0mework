import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeLiving

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

private def receiptPayload
    (observation : Option (ProgrammeWorld.ObservationLaw (RawCurrent Party Good Technology Instrument)
      (ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument)))
    (current : RawCurrent Party Good Technology Instrument)
    (past : List (RawCurrent Party Good Technology Instrument)) :
    ProgrammeWorld.TransferReceiptAt observation (.running current past) →
      Option (ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument) :=
  match observation with
  | none => fun _ => none
  | some _ => fun receipt => some receipt.val

def writtenPayload (current : RawCurrent Party Good Technology Instrument)
    (past : List (RawCurrent Party Good Technology Instrument))
    (entry : OpenResponsibilityAt (ProgrammeSource.N input)
      (ProgrammeSource.supportAt input (.running current past))) :=
  receiptPayload (ProgrammeSource.observation? input) current past
    (ProgrammeLedger.writtenTransferReceipt input current past entry)

theorem every_original_row_writes_the_same_payload
    (current : RawCurrent Party Good Technology Instrument)
    (past : List (RawCurrent Party Good Technology Instrument))
    (entry : OpenResponsibilityAt (ProgrammeSource.N input)
      (ProgrammeSource.supportAt input (.running current past))) :
    writtenPayload input current past entry =
      (ProgrammeSource.observation? input).map (fun observed => observed.generate current) := by
  unfold writtenPayload
  rw [ProgrammeLedger.writtenTransferReceipt_exact]
  cases ProgrammeSource.observation? input <;> rfl

def originalPayload : (ProgrammeSource.V input).Current →
    Option (ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument)
  | .bootstrap => none
  | .running current past => writtenPayload input current past
      (ProgrammeSource.sourceEntry input (.running current past) .inherited)

/-- Only the raw task is read. Neither the report's law nor its outcome is
used as a proof of execution or service coverage under the original input. -/
def taskOfReport (report : ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument) :
    Option (PublicFunction.PublicTaskSpec Party Good) := by
  cases report with
  | original _ _ => exact none
  | @planning decParty decGood decInstrument law current task alphabet budget outcome => exact some task

def taskOfPayload (payload : Option (ProgrammeSource.ProgrammeReport Party Good Port Technology Instrument)) :=
  payload.bind taskOfReport

structure DisclosureBlockerAt (current : (ProgrammeSource.V input).Current) where
  private mk ::
  notDisclosed : taskOfPayload (originalPayload input current) = none

def DisclosureBlockerAt.originalEntry {current : (ProgrammeSource.V input).Current}
    (_blocker : DisclosureBlockerAt input current) := ProgrammeSource.sourceEntry input current .inherited

def DisclosureBlockerAt.actualNextEntry {current : (ProgrammeSource.V input).Current}
    (blocker : DisclosureBlockerAt input current) :=
  ((ProgrammeLedger.evolution input current).destination (blocker.originalEntry input)).1

theorem DisclosureBlockerAt.same_row_and_actual_next {current : (ProgrammeSource.V input).Current}
    (blocker : DisclosureBlockerAt input current) :
    blocker.actualNextEntry input = ProgrammeSource.targetEntry input current .inherited :=
by
  cases current <;> exact ProgrammeLedger.destination_exact input _ _

inductive TaskDisclosureAt (current : (ProgrammeSource.V input).Current) : Type
  | declared (task : PublicFunction.PublicTaskSpec Party Good)
      (original : taskOfPayload (originalPayload input current) = some task)
  | unresolved (blocker : DisclosureBlockerAt input current)

def discloseTask (current : (ProgrammeSource.V input).Current) : TaskDisclosureAt input current :=
  match observed : taskOfPayload (originalPayload input current) with
  | none => .unresolved ⟨observed⟩
  | some task => .declared task observed

theorem every_current_original_row_has_the_same_disclosure
    (current : RawCurrent Party Good Technology Instrument)
    (past : List (RawCurrent Party Good Technology Instrument))
    (entry : OpenResponsibilityAt (ProgrammeSource.N input)
      (ProgrammeSource.supportAt input (.running current past))) :
    writtenPayload input current past entry = originalPayload input (.running current past) := by
  rw [every_original_row_writes_the_same_payload]
  exact (every_original_row_writes_the_same_payload input current past _).symm


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.every_original_row_writes_the_same_payload

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.DisclosureBlockerAt.same_row_and_actual_next
