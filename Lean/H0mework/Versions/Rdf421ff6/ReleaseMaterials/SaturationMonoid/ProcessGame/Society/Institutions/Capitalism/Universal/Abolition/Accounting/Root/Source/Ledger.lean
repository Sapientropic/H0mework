import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.State
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Injective

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation
open Financial.Installation.Admission (InjectiveLedger injective_cast jointStep_injective)

noncomputable section

private theorem transport_keys {N : WorldRelationNetwork} {law : DebtActivationLaw}
    (support : N.Support) {source target : law.DebtState} (event : law.TransportAt source target) :
    Financial.Installation.KeepsKeys (transportLedgerEvolution support event) := by
  constructor <;> rintro ⟨responsibility,opened⟩ <;> cases responsibility with
  | inl old => rfl
  | inr debt => rcases opened with ⟨⟨same⟩⟩; subst debt; rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.NativeFrame input)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (word : RawEvent Party Good Port Technology Instrument)

private def ImageInjective {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {source : SourceNativeSource N V} {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (image : SourceNativeLedgerEvolutionAt source occurrence) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt occurrence image, InjectiveLedger actual.ledgerEvolution

theorem source_successor_injective : InjectiveLedger (sourceSuccessor input frame visit).ledgerEvolution := by
  have all : ImageInjective (frame.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) := by
    rw [(frame.program.emit visit.current).generated_eq]
    exact fun _ => ⟨frame.origin_injective visit.current,frame.destination_injective visit.current⟩
  exact all _

theorem open_fibres (support : (N input frame claim).Support) (responsibility : (N input frame claim).Responsibility) :
    Subsingleton ((N input frame claim).OpenAt support responsibility) := by
  rcases support with ⟨old,state⟩
  cases responsibility with
  | inl responsibility => exact frame.openAt_subsingleton old responsibility
  | inr debt =>
      cases state with
      | none => change Subsingleton PEmpty; infer_instance
      | some state =>
          change Subsingleton (ULift (PLift (debt = (Responsibility.Family.activationLaw claim).debtId)))
          infer_instance

def repairEvolution : LedgerWriteEvolutionAt (N input frame claim)
    ⟨support input frame visit claim word .declared⟩ ⟨support input frame visit claim word .observed⟩ :=
  transportLedgerEvolution (oldSupport input frame visit .declared)
    (Responsibility.Family.CarryAt.actual (declared input frame visit claim) (actualLaw input) word)

def evolution : (phase : Phase) →
    LedgerWriteEvolutionAt (N input frame claim) ⟨support input frame visit claim word phase⟩
      ⟨support input frame visit claim word (next phase)⟩
  | .pending => jointStepLedgerEvolution (sourceSuccessor input frame visit).ledgerEvolution
      (sourceEntry input frame visit) (firstStep input frame visit claim).step
  | .declared => repairEvolution input frame visit claim word
  | .observed => LedgerWriteEvolutionAt.identity _

theorem repair_injective : InjectiveLedger (repairEvolution input frame visit claim word) := by
  have keys := transport_keys (N := frame.N) (law := Responsibility.Family.activationLaw claim)
    (oldSupport input frame visit .declared)
    (Responsibility.Family.CarryAt.actual (declared input frame visit claim) (actualLaw input) word)
  exact ⟨Financial.Installation.keys_imply_origin_injective _ keys (open_fibres input frame claim),
    Financial.Installation.keys_imply_destination_injective _ keys (open_fibres input frame claim)⟩

theorem evolution_injective (phase : Phase) : InjectiveLedger (evolution input frame visit claim word phase) := by
  cases phase with
  | pending =>
      exact jointStep_injective (sourceSuccessor input frame visit).ledgerEvolution
        (sourceEntry input frame visit) (firstStep input frame visit claim).step
        (source_successor_injective input frame visit)
  | declared => exact repair_injective input frame visit claim word
  | observed => exact ⟨Function.injective_id,Function.injective_id⟩

theorem original_rows_are_in_the_actual_source_successor
    (entry : OpenResponsibilityAt frame.N (sourceSupport input frame visit)) :
    ((evolution input frame visit claim word .pending).destination
      (oldEntry (law := Responsibility.Family.activationLaw claim)
        (state? := some (initialState input frame visit claim)) entry)).1 =
      oldEntry (law := Responsibility.Family.activationLaw claim) (state? := some (declared input frame visit claim))
        ((sourceSuccessor input frame visit).ledgerEvolution.destination entry).1 := rfl

theorem every_original_target_row_retains_its_actual_source
    (entry : OpenResponsibilityAt frame.N (oldSupport input frame visit .declared)) :
    ((evolution input frame visit claim word .pending).origin
      (oldEntry (law := Responsibility.Family.activationLaw claim)
        (state? := some (declared input frame visit claim)) entry)).1 =
      oldEntry (law := Responsibility.Family.activationLaw claim) (state? := some (initialState input frame visit claim))
        ((sourceSuccessor input frame visit).ledgerEvolution.origin entry).1 := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source
