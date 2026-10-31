import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Inquiry
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.Key

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Inquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section


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

local notation "F" => Source.flow input frame visit claim word
local notation "fullRoot" => root input frame visit claim word

theorem the_actual_debt_row_keeps_its_original_source_identity (phase : Source.Phase) :
    ((Source.evolution input frame visit claim word phase).destination
      (entry input frame claim (Source.support input frame visit claim word phase))).1.1 =
        Sum.inr (Responsibility.Family.activationLaw claim).debtId := by
  cases phase <;> rfl

theorem canonical_debt_row_is_the_same_original_responsibility (phase : Source.Phase) :
    (fullRoot).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (Compiler.nextEq F phase)
      (entry input frame claim (Source.support input frame visit claim word phase)) =
        entry input frame claim (Source.support input frame visit claim word (Source.next phase)) := by
  apply Financial.Installation.entry_eq_of_key
  · exact Compiler.canonical_key_of_flow F phase
      (entry input frame claim (Source.support input frame visit claim word phase)) _
      (the_actual_debt_row_keeps_its_original_source_identity input frame visit claim word phase)
  · exact Source.open_fibres input frame claim _

def initialVisit : SourceNativeTemporalVisitAt (fullRoot).toAuthoritativeRoot.toLedgerRoot :=
  .finite (fullRoot).toAuthoritativeRoot.toRoot.initialVisit

def initialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt (fullRoot)
    (initialVisit input frame visit claim word)
    (entry input frame claim (Source.support input frame visit claim word .pending)) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow (fullRoot) _
    (Compiler.generatedRow F (Compiler.initialVisit F) _)

def nextAuthority
    (currentVisit : SourceNativeTemporalVisitAt (fullRoot).toAuthoritativeRoot.toLedgerRoot)
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (fullRoot) currentVisit
      (entry input frame claim (Source.support input frame visit claim word currentVisit.current))) :
    SourceNativeLivingTemporalCausalEntryAuthorityAt (fullRoot)
      (currentVisit.next (Compiler.nextEq F currentVisit.current))
      (entry input frame claim (Source.support input frame visit claim word (Source.next currentVisit.current))) :=
  canonical_debt_row_is_the_same_original_responsibility input frame visit claim word currentVisit.current ▸
    authority.next (Compiler.nextEq F currentVisit.current)

#print axioms canonical_debt_row_is_the_same_original_responsibility
#print axioms nextAuthority

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Inquiry
