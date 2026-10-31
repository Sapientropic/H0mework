import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Inquiry.Foundation

/-! The richer source installs its actual finite calculation before the
emitter.  The payload is the original interpreter result and raw successor,
not a zero-field theorem marker. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeLiving

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program ProgrammeWorld ProgrammeSource ProgrammeCertification

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : Input Party Good Port Technology Instrument)

inductive Projection
  | ledger
  | execution
  | consumer
  | inquiry

def projectionLaw : SourceNativeProjectionLaw (restructuringSource input).toLedgerSource where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .ledger => SourceNativeLedgerEvolutionAt (ProgrammeSource.source input) occurrence
    | .execution => ExecutionFaceAt input occurrence
    | .consumer => SourceNativeInquiryAnswerConsumerTokenAt
        PUnit.unit (ULift.up.{1, 0} occurrence) (inquiryEntryAt input occurrence)
        (executionFace input occurrence)
    | .inquiry => SourceNativeInquiryCompilationTokenAt
        (inquiryEntryAt input occurrence) PUnit.unit (ULift.up.{1, 0} occurrence)
        (inquiryAudit input occurrence) (ExecutionFaceAt input occurrence)
  project := fun projection {_} occurrence _ => match projection with
    | .ledger => (ledgerCompiler input).compile occurrence
    | .execution => executionFace input occurrence
    | .consumer => .canonical
    | .inquiry => .canonical (executionFace input occurrence)

def authoritySource : SourceNativeAuthoritySource (N input) (V input) where
  restructuringSource := restructuringSource input
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource input)
    (fun _ => ⟨fun impossible => impossible.elim⟩)
  lawSurface := TheoryState.rootSemantic (N input)
  projectionLaw := projectionLaw input

def livingRoot : SourceNativeLivingRootClosure (N input) (V input) where
  source := {
    base := authoritySource input
    terminalHandoff := (authoritySource input).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun impossible => impossible.elim⟩) }
  emitted := emitted input
  compiler_commutes := fun _ => rfl

theorem projected_execution_uses_actual_root_next (current : (V input).Current) :
    ((projectionLaw input).project .execution (emitted input current) ()).after =
      rawCurrent input (next input current) :=
  (executionFace input (emitted input current)).root_next_exact

theorem projected_execution_material_balance (current : (V input).Current)
    (party : Party) (good : Good) :
    let face := (projectionLaw input).project .execution (emitted input current) ()
    face.after.stock party good + input.law.totalDebit face.interpreted.items party good =
      face.before.stock party good + input.law.totalCredit face.interpreted.items party good :=
  input.law.actual_next_material_balance (rawCurrent input current) (rawEvent input current) party good

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeLiving
